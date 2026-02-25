import LeanCategory.PreFreeEgger

variable {V : Type u}
variable [StarMonoid V] [Quiver.{v} V]

open CategoryTheory
open HomEquiv

instance : Category (S V) where
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
def eqToIso' {X Y : S V} (h : X = Y) : X ≅ Y := {
  hom := ⟦@eqToHom _ preHom _ _ h⟧
  inv := ⟦@eqToHom _ preHom _ _ h.symm⟧
  hom_inv_id := by
    apply Quotient.sound
    exact eqToHom_comp (by rfl) (by rfl)
  inv_hom_id := by
    apply Quotient.sound
    exact eqToHom_comp (by rfl) (by rfl)
}

-- TODO use ofTensorHom to dodge the nasty whiskers
instance : MonoidalCategory (S V) where
  tensorObj X Y := X * Y
  tensorHom f g := Quotient.map₂ (· ⊗ ·) (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg) f g
  tensorUnit := 1
  associator X Y Z := eqToIso' (mul_assoc X Y Z)
  leftUnitor X := eqToIso' (one_mul X)
  rightUnitor X := eqToIso' (mul_one X)
  whiskerLeft X {Y₁ Y₂} f := Quotient.map (X ◁ ·) (fun _ _ hf ↦ HomEquiv.whiskerLeft X hf) f
  whiskerRight {X₁ X₂} f Y := Quotient.map (· ▷ Y) (fun _ _ hf ↦ HomEquiv.whiskerRight Y hf) f
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

instance : InvolutiveCategory (S V) where
  starObj X := X⋆
  starHom f := Quotient.map (·⋆) (fun _ _ hf ↦ HomEquiv.star hf) f
  skewator X Y := eqToIso' (StarMonoid.star_mul Y X).symm
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

instance : TwistedCategory (S V) where
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
