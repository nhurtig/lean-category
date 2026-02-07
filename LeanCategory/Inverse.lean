import Mathlib
import LeanCategory.MonoidalWord
import LeanCategory.Instances

universe u

namespace BraidGroupoid

open CategoryTheory
open scoped MonoidalCategory
open scoped BraidGroupoid

/-- The composition of a hom with its inverse is the identity up to `HomEquiv`. -/
@[simp, grind]
lemma HomEquiv.comp_inv {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵇ Y) :
    HomEquiv (f.comp f.inv) (Hom.id X) := by
  induction f
  any_goals (constructor; done)
  case comp f g ihf ihg =>
    simp
    calc
      HomEquiv _ ((f.comp (g.comp (g.inv))).comp f.inv) := by
        grind [assoc]
      HomEquiv _ ((f.comp (Hom.id _)).comp f.inv) := by
        apply HomEquiv.comp
        · apply HomEquiv.comp
          · rfl
          · assumption
        · rfl
      HomEquiv _ (f.comp f.inv) := by
        apply HomEquiv.comp
        · exact comp_id f
        · rfl
      HomEquiv _ (Hom.id _) := by assumption
  case tensor f g ihf ihg =>
    calc
      HomEquiv _ _ := by
        apply tensorHom_comp_tensorHom
      HomEquiv _ _ := by
        apply tensor ihf ihg
      HomEquiv _ _ := by
        apply id_tensorHom_id

/-- The inverse of an inverse is the original hom, up to `HomEquiv`. -/
@[simp, grind]
lemma HomEquiv.inv_inv {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵇ Y) :
    HomEquiv f.inv.inv f := by
  induction f
  any_goals rfl
  case comp ihf ihg =>
    apply comp ihf ihg
  case tensor ihf ihg =>
    apply tensor ihf ihg

/-- The composition of a hom with its inverse on the left is the identity up to `HomEquiv`. -/
@[simp, grind]
lemma HomEquiv.inv_comp {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵇ Y) :
    HomEquiv (f.inv.comp f) (Hom.id Y) := by
  calc
    HomEquiv (f.inv.comp f) _ := by
      symm
      apply comp_id
    HomEquiv _ _ := by
      apply comp
      · rfl
      · symm
        apply HomEquiv.comp_inv f.inv
    HomEquiv _ (f.inv.comp ((f.comp f.inv).comp f.inv.inv)) := by
      grind [assoc]
    HomEquiv _ _ := by
      apply comp
      · rfl
      · apply comp
        · apply HomEquiv.comp_inv f
        · rfl
    HomEquiv _ _ := by
      apply comp
      · rfl
      · apply id_comp
    HomEquiv _ _ := by
      apply HomEquiv.comp_inv f.inv

/-- If two homs are equivalent, their inverses are also equivalent. -/
@[simp, grind]
lemma HomEquiv.inv {α : Type u} {X Y : MonoidalWord α} {f g : X ⟶ᵇ Y} :
    HomEquiv f g → HomEquiv f.inv g.inv := by
  intro h
  calc
    HomEquiv f.inv _ := by
      symm
      apply comp_id
    HomEquiv _ _ := by
      apply comp
      · rfl
      · symm
        apply comp_inv g
    HomEquiv _ _ := by
      apply comp
      · rfl
      · apply comp
        · symm
          exact h
        · rfl
    HomEquiv _ ((f.inv.comp f).comp g.inv) := by
      grind [assoc]
    HomEquiv _ _ := by
      apply comp
      · apply inv_comp
      · rfl
    HomEquiv _ _ := by
      apply id_comp

end BraidGroupoid

open CategoryTheory

namespace BraidGroupoid

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
