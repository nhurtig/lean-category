import LeanCategory.PreFreeEggerGood

variable {V : Type u}
variable [StarMonoid V] [userQuiver : Quiver.{v} V]

open CategoryTheory
open HomEquiv

instance quotiented : Category V where
  Hom X Y := Quotient (setoidHom X Y)
  id X := ⟦𝟙 X⟧
  comp f g := Quotient.map₂ (· ≫ ·) (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg) f g
  id_comp {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    grind
  comp_id {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    grind
  assoc {W X Y Z} := by
    rintro ⟨f⟩ ⟨g⟩ ⟨h⟩
    apply Quotient.sound
    grind

-- not eqToIso! Can't see much hope of generalizing this one
def eqToIso' {X Y : V} (h : X = Y) : X ≅ Y := {
  hom := ⟦@eqToHom _ prehom _ _ h⟧
  inv := ⟦@eqToHom _ prehom _ _ h.symm⟧
  hom_inv_id := by
    apply Quotient.sound
    exact eqToHom_comp (by rfl) (by rfl)
  inv_hom_id := by
    apply Quotient.sound
    exact eqToHom_comp (by rfl) (by rfl)
}

-- TODO use ofTensorHom to dodge the nasty whiskers
instance : MonoidalCategory V where
  tensorObj X Y := X * Y
  tensorHom f g := Quotient.map₂ (· ⊗ᵥ ·) (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg) f g
  tensorUnit := 1
  associator X Y Z := eqToIso' (mul_assoc X Y Z)
  leftUnitor X := eqToIso' (one_mul X)
  rightUnitor X := eqToIso' (mul_one X)
  whiskerLeft X {Y₁ Y₂} f := Quotient.map (X ◁ᵥ ·) (fun _ _ hf ↦ HomEquiv.whiskerLeft X hf) f
  whiskerRight {X₁ X₂} f Y := Quotient.map (· ▷ᵥ Y) (fun _ _ hf ↦ HomEquiv.whiskerRight Y hf) f
  tensorHom_def {X₁ Y₁ X₂ Y₂} := by
    rintro ⟨f⟩ ⟨g⟩
    apply Quotient.sound
    apply HomEquiv.tensorHom_def
  id_tensorHom_id _ _ := Quotient.sound id_tensor_id
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} := by -- TODO can this be sound?
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    apply Quotient.sound
    grind
  whiskerLeft_id X Y := Quotient.sound (HomEquiv.whiskerLeft_id X Y)
  id_whiskerRight X Y := Quotient.sound (HomEquiv.id_whiskerRight X Y)
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    apply Quotient.sound
    grind
  leftUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    grind
  rightUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    grind
  pentagon W X Y Z := by
    apply Quotient.sound
    eqToHom_eq_eqToHom
  triangle X Y := by
    apply Quotient.sound
    eqToHom_eq_eqToHom

instance : InvolutiveCategory V where
  starObj X := X⋆
  starHom f := Quotient.map (·⋆ᵥ) (fun _ _ hf ↦ HomEquiv.star hf) f
  skewator X Y := eqToIso' (StarMul.star_mul Y X).symm
  involutor X := eqToIso' (star_involutive X)
  starHom_id _ := Quotient.sound star_id
  starHom_comp_starHom {X Y Z} := by
    rintro ⟨f⟩ ⟨g⟩
    apply Quotient.sound
    grind
  skewator_naturality {W X Y Z} := by
    rintro ⟨f⟩ ⟨g⟩
    apply Quotient.sound
    apply star_skew
  involutor_naturality {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    grind
  f3 X Y Z := by
    apply Quotient.sound
    eqToHom_eq_eqToHom
  n2 X Y := by
    apply Quotient.sound
    eqToHom_eq_eqToHom
  a X := by
    apply Quotient.sound
    eqToHom_eq_eqToHom

@[simp]
instance final : TwistedCategory V where
  twist X := {
    hom := ⟦ς_inv X⟧
    inv := ⟦ς_hom X⟧
    hom_inv_id := by
      apply Quotient.sound
      constructor
    inv_hom_id := by
      apply Quotient.sound
      constructor
  }
  twist_naturality {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    constructor
  tℓ X Y Z := by
    apply Quotient.sound
    constructor

#check FreeMonoidalCategory

open MonoidalCategory
open InvolutiveCategory
open TwistedCategory

abbrev homMk {X Y : V} (f : X ⟶ᵥ Y) : quotiented.Hom X Y := ⟦f⟧

@[simp]
def homMkDef {X Y : V} (f : X ⟶ᵥ Y) : quotiented.Hom X Y := ⟦f⟧

abbrev eqToHom' {X Y : V} (h : X = Y) : (X ⟶ᵥ Y) := @eqToHom _ prehom _ _ h

-- TODO does this blow away all the below mk_α and similar? If so, delete them!
@[simp]
theorem mk_eqToHom {X Y : V} (h : X = Y) :
    homMk (eqToHom' h) = eqToHom h := by
  subst h
  rfl

@[simp]
theorem mk_id {X : V} : ⟦𝟙ᵥ X⟧ = 𝟙 X :=
  rfl

@[simp]
theorem mk_comp {X Y Z : V} (f : X ⟶ᵥ Y) (g : Y ⟶ᵥ Z) :
    homMk (f ≫ᵥ g) = ⟦f⟧ ≫ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_tensor {X₁ Y₁ X₂ Y₂ : V} (f : X₁ ⟶ᵥ Y₁) (g : X₂ ⟶ᵥ Y₂) :
    ⟦f ⊗ᵥ g⟧ = @MonoidalCategory.tensorHom V _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_whiskerLeft (X : V) {Y₁ Y₂ : V} (f : Y₁ ⟶ᵥ Y₂) :
    ⟦X ◁ᵥ f⟧ = X ◁ ⟦f⟧ :=
  rfl

/- @[simp] -/
/- theorem mk_whiskerLeft (X : V) {Y₁ Y₂ : V} (f : Y₁ ⟶ᵥ Y₂) : -/
/-     ⟦f.whiskerLeft X⟧ = MonoidalCategory.whiskerLeft (C := V) (X := X) (f := ⟦f⟧) := -/
/-   rfl -/

@[simp]
theorem mk_whiskerRight {X₁ X₂ : V} (f : X₁ ⟶ᵥ X₂) (Y : V) :
    ⟦f ▷ᵥ Y⟧ = ⟦f⟧ ▷ Y :=
  rfl

/- @[simp] -/
/- theorem mk_whiskerRight {X₁ X₂ : V} (f : X₁ ⟶ᵥ X₂) (Y : V) : -/
/-     ⟦f.whiskerRight Y⟧ = MonoidalCategory.whiskerRight (C := V) (f := ⟦f⟧) (Y := Y) := -/
/-   rfl -/

@[simp]
theorem mk_star {X Y : V} (f : X ⟶ᵥ Y) :
    homMk f⋆ᵥ = InvolutiveCategoryStruct.starHom ⟦f⟧ := by
  simp only [homMk]
  rfl

/-
@[simp]
theorem mk_α_hom {X Y Z : V} : homMk (eqToHom' (by simp [tensorObj, mul_assoc])) = (α_ X Y Z).hom :=
  rfl

@[simp]
theorem mk_α_inv {X Y Z : V} : homMk (eqToHom' (by simp [tensorObj, mul_assoc])) = (α_ X Y Z).inv :=
  rfl

@[simp]
theorem mk_ρ_hom {X : V} : homMk (eqToHom' (by simp [tensorObj, tensorUnit])) = (ρ_ X).hom :=
  rfl

@[simp]
theorem mk_ρ_inv {X : V} : homMk (eqToHom' (by simp [tensorObj, tensorUnit])) = (ρ_ X).inv :=
  rfl

@[simp]
theorem mk_l_hom {X : V} : homMk (eqToHom' (by simp [tensorObj, tensorUnit])) = (λ_ X).hom :=
  rfl

@[simp]
theorem mk_l_inv {X : V} : homMk (eqToHom' (by simp [tensorObj, tensorUnit])) = (λ_ X).inv :=
  rfl

@[simp]
theorem mk_χ_hom {X Y : V} :
    homMk (eqToHom' (by simp [tensorObj, InvolutiveCategoryStruct.starObj])) = (χ_ X Y).hom :=
  rfl

@[simp]
theorem mk_χ_inv {X Y : V} : 
    homMk (eqToHom' (by simp [tensorObj, InvolutiveCategoryStruct.starObj])) = (χ_ X Y).inv :=
  rfl

@[simp]
theorem mk_e_hom {X : V} : 
    homMk (eqToHom' (by simp [tensorObj, InvolutiveCategoryStruct.starObj])) = (e_ X).hom :=
  rfl

@[simp]
theorem mk_e_inv {X : V} : 
    homMk (eqToHom' (by simp [tensorObj, InvolutiveCategoryStruct.starObj])) = (e_ X).inv :=
  rfl
-/

@[simp]
theorem mk_ς_hom {X : V} : 
    homMk (ς_inv X) = (ς_ X).hom :=
  rfl

@[simp]
theorem mk_ς_inv {X : V} : 
    homMk (ς_hom X) = (ς_ X).inv :=
  rfl

@[simp]
theorem tensor_eq_tensor {X Y : V} : X * Y = X ⊗ Y :=
  rfl

@[simp]
theorem unit_eq_unit : 1 = 𝟙_ V :=
  rfl

@[simp]
theorem star_eq_star {X : V} : Star.star X = InvolutiveCategoryStruct.starObj X := by
  rfl

