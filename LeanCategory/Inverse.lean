import Mathlib
import LeanCategory.MonoidalWord
import LeanCategory.Instances

universe u

namespace BraidGroupoid

open CategoryTheory

/-- The composition of a hom with its inverse is the identity up to `HomEquiv`. -/
@[simp, grind]
lemma HomEquiv.comp_inv {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵇ Y) :
    f.comp f.inv ≈ 1 := by
  induction f
  any_goals (constructor; done)
  case comp f g ihf ihg =>
    simp
    exact calc
      _ ≈ ((f.comp (g.comp (g.inv))).comp f.inv) := by
        grind [assoc]
      _ ≈ _ := by
        apply HomEquiv.comp
        · apply HomEquiv.comp
          · rfl
          · assumption
        · rfl
      _ ≈ _ := by
        apply HomEquiv.comp
        · exact comp_id f
        · rfl
      _ ≈ _ := by assumption
  case tensor f g ihf ihg =>
    exact calc
      (f * g).comp (f * g).inv ≈ _ := by
        apply tensorHom_comp_tensorHom
      _ ≈ Hom.tensor 1 1 := by
        apply tensor ihf ihg
      _ ≈ 1 := by
        apply id_tensorHom_id

/-- The inverse of an inverse is the original hom, up to `HomEquiv`. -/
@[simp, grind]
lemma HomEquiv.inv_inv {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵇ Y) :
    f.inv.inv ≈ f := by
  induction f
  any_goals rfl
  case comp ihf ihg =>
    apply comp ihf ihg
  case tensor ihf ihg =>
    apply tensor ihf ihg

/-- The composition of a hom with its inverse on the left is the identity up to `HomEquiv`. -/
@[simp, grind]
lemma HomEquiv.inv_comp {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵇ Y) :
    f.inv.comp f ≈ 1 := by
  exact calc
    f.inv.comp f ≈ _ := by
      symm
      apply comp_id
    _ ≈ _ := by
      apply comp
      · rfl
      · symm
        apply HomEquiv.comp_inv f.inv
    _ ≈ f.inv.comp ((f.comp f.inv).comp f.inv.inv) := by
      grind [assoc]
    _ ≈ _ := by
      apply comp
      · rfl
      · apply comp
        · apply HomEquiv.comp_inv f
        · rfl
    _ ≈ _ := by
      apply comp
      · rfl
      · apply id_comp
    _ ≈ _ := by
      apply HomEquiv.comp_inv f.inv

/-- If two homs are equivalent, their inverses are also equivalent. -/
@[simp, grind]
lemma HomEquiv.inv {α : Type u} {X Y : MonoidalWord α} {f g : X ⟶ᵇ Y} :
    f ≈ g → f.inv ≈ g.inv := by
  intro h
  exact calc
    f.inv ≈ _ := by
      symm
      apply comp_id
    _ ≈ _ := by
      apply comp
      · rfl
      · symm
        apply comp_inv g
    _ ≈ _ := by
      apply comp
      · rfl
      · apply comp
        · symm
          exact h
        · rfl
    _ ≈ (f.inv.comp f).comp g.inv := by
      grind [assoc]
    _ ≈ _ := by
      apply comp
      · apply inv_comp
      · rfl
    _ ≈ _ := by
      apply id_comp

/-- The groupoid structure on the quotient of braid morphisms. -/
instance (α : Type u) : Groupoid (MonoidalWord α) where
    inv {X Y} f := Quotient.lift (fun g => ⟦g.inv⟧) (by
        intro f g h
        apply Quotient.sound
        apply HomEquiv.inv h) f
    comp_inv f := by
      induction f using Quotient.inductionOn
      apply Quotient.sound
      apply HomEquiv.comp_inv
    inv_comp  f := by
      induction f using Quotient.inductionOn
      apply Quotient.sound
      apply HomEquiv.inv_comp

/-- A shorthand class for braided monoidal groupoids. -/
class BraidedGroupoid (C : Type u) [Category C] [MonoidalCategory C]
    [BraidedCategory C] [Groupoid C]

/-- The free braided monoidal groupoid on a type of labels. -/
instance (α : Type u) : BraidedGroupoid (MonoidalWord α) where

end BraidGroupoid
