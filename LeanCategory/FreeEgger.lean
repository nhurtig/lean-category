import LeanCategory.PreFreeEgger

variable {C : Type u}

namespace CategoryTheory.FreeTwistedCategory
open HomEquiv

instance categoryFreeTwistedCategory : Category.{u} (F C) where
  Hom X Y := _root_.Quotient (FreeTwistedCategory.setoidHom X Y)
  id X := ⟦Hom.id X⟧
  comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg)
  id_comp := by
    rintro X Y ⟨f⟩
    exact _root_.Quotient.sound (id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact _root_.Quotient.sound (comp_id f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact _root_.Quotient.sound (assoc f g h)


/- instance groupoidFreeTwistedCategory : Groupoid.{u} (F C) where -/
/-   inv f := Quotient.map Hom.inv (fun _ _ hf  ↦ HomEquiv.inv hf) -/

instance monoidalFreeTwistedCategory : MonoidalCategory (F C) where
  tensorObj X Y := FreeTwistedCategory.tensor X Y
  tensorHom := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg)
  whiskerLeft X _ _ f := Quot.map (fun f ↦ Hom.whiskerLeft X f) (fun f f' ↦ .whiskerLeft X f f') f
  whiskerRight f Y := Quot.map (fun f ↦ Hom.whiskerRight f Y) (fun f f' ↦ .whiskerRight f f' Y) f
  tensorHom_def {W X Y Z} := by
    rintro ⟨f⟩ ⟨g⟩
    exact _root_.Quotient.sound (HomEquiv.tensorHom_def _ _)
  id_tensorHom_id _ _ := Quot.sound id_tensorHom_id
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact _root_.Quotient.sound (tensorHom_comp_tensorHom _ _ _ _)
  whiskerLeft_id X Y := Quot.sound (HomEquiv.whiskerLeft_id X Y)
  id_whiskerRight X Y := Quot.sound (HomEquiv.id_whiskerRight X Y)
  tensorUnit := FreeTwistedCategory.unit
  associator X Y Z := ⟨⟦Hom.α_hom X Y Z⟧, ⟦Hom.α_inv X Y Z⟧,
    _root_.Quotient.sound α_hom_inv, _root_.Quotient.sound α_inv_hom⟩
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    exact _root_.Quotient.sound (associator_naturality _ _ _)
  leftUnitor X := ⟨⟦Hom.l_hom X⟧, ⟦Hom.l_inv X⟧,
    _root_.Quotient.sound l_hom_inv, _root_.Quotient.sound l_inv_hom⟩
  leftUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    exact _root_.Quotient.sound (l_naturality _)
  rightUnitor X :=
    ⟨⟦Hom.ρ_hom X⟧, ⟦Hom.ρ_inv X⟧, _root_.Quotient.sound ρ_hom_inv, _root_.Quotient.sound ρ_inv_hom⟩
  rightUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    exact _root_.Quotient.sound (ρ_naturality _)
  pentagon _ _ _ _ := _root_.Quotient.sound pentagon
  triangle _ _ := _root_.Quotient.sound triangle

instance involutiveFreeTwistedCategory : InvolutiveCategory (F C) where
  starObj X := X.star
  starHom := Quotient.map Hom.star (fun _ _ hf  ↦ HomEquiv.star hf)
  starHom_id _ := Quot.sound starHom_id
  starHom_comp_starHom {X Y Z} := by
    rintro ⟨f⟩ ⟨g⟩
    exact _root_.Quotient.sound (starHom_comp_starHom _ _)
  skewator X Y := ⟨⟦Hom.χ_hom X Y⟧, ⟦Hom.χ_inv X Y⟧, 
    _root_.Quotient.sound χ_hom_inv, _root_.Quotient.sound χ_inv_hom⟩
  skewator_naturality {X₁ X₂ Y₁ Y₂} := by
    rintro ⟨f₁⟩ ⟨f₂⟩
    exact _root_.Quotient.sound (χ_naturality _ _)
  involutor X := ⟨⟦Hom.ε_hom X⟧, ⟦Hom.ε_inv X⟧, 
    _root_.Quotient.sound ε_hom_inv, _root_.Quotient.sound ε_inv_hom⟩
  involutor_naturality {X Y} := by
    rintro ⟨f⟩
    exact _root_.Quotient.sound (HomEquiv.ε_naturality _)
  f3 _ _ _ := _root_.Quotient.sound f3
  n2 _ _ := _root_.Quotient.sound n2
  a _ := _root_.Quotient.sound a

instance freeTwistedCategory : TwistedCategory (F C) where
  twist X := ⟨⟦Hom.twist_hom X⟧, ⟦Hom.twist_inv X⟧, 
    _root_.Quotient.sound twist_hom_inv, _root_.Quotient.sound twist_inv_hom⟩
  twist_naturality {X Y} := by
    rintro ⟨f⟩
    exact _root_.Quotient.sound (HomEquiv.twist_naturality _)
  tℓ _ _ _ := _root_.Quotient.sound tℓ

/-
def empty : Quiver (F C) where
  Hom _ _ := Empty

/- def twistedNoQuiver (C : Type v) := @freeTwistedCategory C empty -/

def categoryFreeTwistedCategoryNoQuiver : Category.{max u 1, u} (F C) :=
    @categoryFreeTwistedCategory _ empty

/- #synth Category.{max u 1, u} (F C) -/

#check categoryFreeTwistedCategoryNoQuiver
-/


/-

#check monoidalFreeTwistedCategoryNoQuiver

instance arst : TwistedCategory (F C) := @freeTwistedCategory C empty
instance arst2 : TwistedCategory.{u, 1} (F C) := twistedNoQuiver C
-/

/-

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


@[simp]
def homMkDef {X Y : V} (f : X ⟶ᵥ Y) : quotiented.Hom X Y := ⟦f⟧

abbrev eqToHom' {X Y : V} (h : X = Y) : (X ⟶ᵥ Y) := @eqToHom _ prehom _ _ h

-- TODO does this blow away all the below mk_α and similar? If so, delete them!
@[simp]
theorem mk_eqToHom {X Y : V} (h : X = Y) :
    homMk (eqToHom' h) = eqToHom h := by
  subst h
  rfl

-/

@[simp]
def homMk {X Y : F V} (f : X ⟶ᵐ Y) : categoryFreeTwistedCategory.Hom X Y := ⟦f⟧

@[simp]
theorem mk_comp {X Y Z : F C} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z) :
    ⟦f.comp g⟧ = @CategoryStruct.comp (F C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_id {X : F C} : ⟦Hom.id X⟧ = 𝟙 X :=
  rfl

open MonoidalCategory

@[simp]
theorem mk_tensor {X₁ Y₁ X₂ Y₂ : F C} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
    ⟦f.tensor g⟧ = @MonoidalCategory.tensorHom (F C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_whiskerLeft {X Y₁ Y₂ : F C} (f : Y₁ ⟶ᵐ Y₂) :
    ⟦f.whiskerLeft X⟧ = X ◁ ⟦f⟧ := rfl

@[simp]
theorem mk_whiskerRight {X₁ X₂ Y : F C} (f : X₁ ⟶ᵐ X₂) :
    ⟦f.whiskerRight Y⟧ = ⟦f⟧ ▷ Y := rfl

@[simp]
theorem mk_α_hom {X Y Z : F C} : ⟦Hom.α_hom X Y Z⟧ = (α_ X Y Z).hom :=
  rfl

@[simp]
theorem mk_α_inv {X Y Z : F C} : ⟦Hom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
  rfl

@[simp]
theorem mk_ρ_hom {X : F C} : ⟦Hom.ρ_hom X⟧ = (ρ_ X).hom :=
  rfl

@[simp]
theorem mk_ρ_inv {X : F C} : ⟦Hom.ρ_inv X⟧ = (ρ_ X).inv :=
  rfl

@[simp]
theorem mk_l_hom {X : F C} : ⟦Hom.l_hom X⟧ = (λ_ X).hom :=
  rfl

@[simp]
theorem mk_l_inv {X : F C} : ⟦Hom.l_inv X⟧ = (λ_ X).inv :=
  rfl

@[simp]
theorem tensor_eq_tensor {X Y : F C} : X.tensor Y = X ⊗ Y :=
  rfl

@[simp]
theorem tensor_eq_tensor' {X Y : F C} : X * Y = X ⊗ Y :=
  rfl

@[simp]
theorem unit_eq_unit : FreeTwistedCategory.unit = 𝟙_ (F C) :=
  rfl

@[simp]
theorem unit_eq_unit' : 1 = 𝟙_ (F C) :=
  rfl

open InvolutiveCategory

@[simp]
theorem mk_star {X Y : F C} (f : X ⟶ᵐ Y) :
    ⟦f.star⟧ = @InvolutiveCategoryStruct.starHom (F C) _ _ _ _ _ ⟦f⟧ :=
  rfl

@[simp]
theorem mk_ε_hom {X : F C} : ⟦Hom.ε_hom X⟧ = (e_ X).hom :=
  rfl

@[simp]
theorem mk_ε_inv {X : F C} : ⟦Hom.ε_inv X⟧ = (e_ X).inv :=
  rfl

@[simp]
theorem mk_χ_hom {X Y : F C} : ⟦Hom.χ_hom X Y⟧ = (χ_ X Y).hom :=
  rfl

@[simp]
theorem mk_χ_inv {X Y : F C} : ⟦Hom.χ_inv X Y⟧ = (χ_ X Y).inv :=
  rfl

@[simp]
theorem star_eq_star {X : F C} : X.star = X⋆ :=
  rfl

open TwistedCategory

@[simp]
theorem mk_ς_hom {X : F C} : ⟦Hom.twist_hom X⟧ = (ς_ X).hom :=
  rfl

@[simp]
theorem mk_ς_hom' {X : F C} : ⟦Hom.twist_hom X⟧ = (TwistedCategoryStruct.twist X).hom :=
  rfl

@[simp]
theorem mk_ς_inv {X : F C} : ⟦Hom.twist_inv X⟧ = (ς_ X).inv :=
  rfl

macro "simp_mk" : tactic =>
  `(tactic|
    repeat1 (first
      | simp
      | rw [mk_comp]
      | rw [mk_id]
      | rw [mk_tensor]
      | rw [mk_whiskerLeft]
      | rw [mk_whiskerRight]
      | rw [mk_α_hom]
      | rw [mk_α_inv]
      | rw [mk_ρ_hom]
      | rw [mk_ρ_inv]
      | rw [mk_l_hom]
      | rw [mk_l_inv]
      | rw [tensor_eq_tensor]
      | rw [tensor_eq_tensor']
      | rw [unit_eq_unit]
      | rw [unit_eq_unit']
      | rw [mk_star]
      | rw [mk_ε_hom]
      | rw [mk_ε_inv]
      | rw [mk_χ_hom]
      | rw [mk_χ_inv]
      | rw [star_eq_star]
      | rw [star_eq_star']
      | rw [mk_ς_hom]
      | rw [mk_ς_inv]
      | rw [twist_inv_naturality]
      | fail "Nothing to do!"
    )
  )

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

instance : Groupoid.{u} (F C) where
    inv := _root_.Quotient.lift (fun f => ⟦f.inv⟧) <| by
      intros f g h
      simp
      induction h
      any_goals simp_mk
      case tensorHom_def =>
        rw [← tensorHom_def']
      all_goals aesop_cat
    comp_inv := by
      rintro X Y f
      induction f using Quotient.inductionOn
      case h f =>
        rw [Quotient.lift_mk]
        induction f
        all_goals simp_mk
        any_goals cat_disch
        any_goals first
          | repeat1 rw [← Category.assoc]
          | rw [← whiskerLeft_comp]
          | rw [← comp_whiskerRight]
          | rw [← InvolutiveCategory.starHom_comp_starHom]
        all_goals cat_disch
    inv_comp := by
      rintro X Y f
      induction f using Quotient.inductionOn
      case h f =>
        rw [Quotient.lift_mk]
        induction f
        all_goals simp_mk
        any_goals cat_disch
        any_goals first
          | repeat1 rw [← Category.assoc]
          | rw [← whiskerLeft_comp]
          | rw [← comp_whiskerRight]
          | rw [← InvolutiveCategory.starHom_comp_starHom]
        all_goals cat_disch

/-
instance : Groupoid.{u} (F C) :=
  { (inferInstance : Category (F C)) with
    inv := _root_.Quotient.lift (fun f => ⟦f.inv⟧) (by
      intros f g h
      simp
      induction h
      /- case twist_inv_hom X => -/
      /-   simp_mk -/
      /-   sorry -/
      /- case ε_inv_hom X => -/
      /-   simp -/
      /-   rw [mk_ε_inv] -/
      /-   simp_mk -/
      /-   rw [@mk_ς_inv C X] -/
      /-   aesop_cat -/
      /- case  -/
      /- case f3 => -/
      /-   simp_mk -/
      /-   sorry -/
      /- case f3 P Q R => -/
      /-   simp_mk -/
      /-   #check f3_inv -/
      /-   exact f3_inv P Q R -/
      /-   sorry -/
      any_goals simp_mk
      any_goals aesop_cat
      all_goals sorry
      ) }
-/

end CategoryTheory.FreeTwistedCategory

