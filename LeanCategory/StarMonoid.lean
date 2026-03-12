import Mathlib

class StarMonoid (R : Type u) extends Monoid R, StarMul R

namespace StarMonoid

scoped postfix:max "⋆" => Star.star

/- structure StarHom (M : Type*) (N : Type*) [Star M] [Star N] where -/
/-   protected toFun : M → N -/
/-   protected map_star : ∀ x, toFun (x⋆) = (toFun x)⋆ -/

/- infixr:25 " →⋆ " => StarHom -/

#check StarMonoidHom

@[simp]
lemma map_star [StarMonoid P] [StarMonoid Q] {x : P} {m : P →⋆* Q} : m x⋆ = (m x)⋆ := m.map_star' x

attribute [simp] mul_assoc

inductive Pre (R : Type u) where
  | unit : Pre R
  | of : R → Pre R
  | mul : Pre R → Pre R → Pre R
  | star : Pre R → Pre R

namespace Pre

inductive Equiv : Pre R → Pre R → Prop where
 | refl X : Equiv X X
 | mul : Equiv X₁ X₂ → Equiv Y₁ Y₂ → Equiv (X₁.mul Y₁) (X₂.mul Y₂)
 | star : Equiv X Y → Equiv X.star Y.star
 | mul_one {X : Pre R} : Equiv (X.mul .unit) X
 | one_mul {X : Pre R} : Equiv (Pre.unit.mul X) X
 | assoc {X Y Z : Pre R} : Equiv ((X.mul Y).mul Z) (X.mul (Y.mul Z)) 
 | involutive {X : Pre R} : Equiv X.star.star X
 | skew {X Y : Pre R} : Equiv (X.mul Y).star (Y.star.mul X.star)
 | symm : Equiv X Y → Equiv Y X
 | trans : Equiv X Y → Equiv Y Z → Equiv X Z

def setoid : Setoid (Pre R) where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

@[simp]
def project : Pre R → List (R × Bool)
  | unit => []
  | of v => [(v, false)]
  | mul X Y => X.project ++ Y.project
  | star X => X.project.map (fun (v, b) ↦ (v, !b)) |>.reverse

end Pre

def FreeStarMonoid (R : Type u) := @Quotient (Pre R) Pre.setoid

instance freeStarMonoid (R : Type u) : StarMonoid (FreeStarMonoid R) where
  mul := Quotient.map₂ .mul <| fun _ _ hx _ _ hy ↦ Pre.Equiv.mul hx hy
  one := ⟦.unit⟧
  star := Quotient.map .star <| fun _ _ h ↦ Pre.Equiv.star h
  mul_assoc X Y Z := by
    induction X using Quotient.inductionOn
    induction Y using Quotient.inductionOn
    induction Z using Quotient.inductionOn
    exact Quotient.sound .assoc
  one_mul X := by
    induction X using Quotient.inductionOn
    exact Quotient.sound .one_mul
  mul_one X := by
    induction X using Quotient.inductionOn
    exact Quotient.sound .mul_one
  star_involutive X := by
    induction X using Quotient.inductionOn
    exact Quotient.sound .involutive
  star_mul X Y := by
    induction X using Quotient.inductionOn
    induction Y using Quotient.inductionOn
    exact Quotient.sound .skew

notation "F" => FreeStarMonoid

def project : FreeStarMonoid R ≃ List (R × Bool) where
  toFun := Quotient.lift Pre.project <| by
    intros X Y h
    induction h <;> simp_all
    unfold Function.comp; simp
  invFun L := ⟦L.foldl (fun X (v, b) ↦ X.mul (if b then (Pre.of v).star else (.of v))) Pre.unit⟧
  left_inv X := by
    simp
    induction X using Quotient.inductionOn
    rename_i X
    simp
    induction X <;> simp_all
    case h.of =>
      apply Quotient.sound
      constructor
    case h.star X ih =>
      rw [List.foldr_map]
      simp
      sorry
    case h.mul X Y ih₁ ih₂ =>
      apply Quotient.sound
      constructor
      sorry
  right_inv L := by
    sorry

end StarMonoid

