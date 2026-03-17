import Mathlib
import LeanCategory.NatDefinition.Instance
import LeanCategory.FreeTwistedQuiver.Functor

namespace CategoryTheory.NatDefinition

open FreeTwistedCategory
open FreeTwistedCategoryQuiver

variable {C : Type u} [Quiver.{v} (T C)]

open CategoryTheory MonoidalCategory InvolutiveCategory TwistedCategory

abbrev mkObj (X : C) : N C := ⟨⟨.of X⟩⟩

@[simp]
lemma projectObj_mkObj (X : T C) : FreeTwistedCategory.projectObj mkObj X = ⟨X⟩ := by
  induction X using FreeTwistedCategory.recOn'
  case unit => rfl
  case of => rfl
  case star ih =>
    simp
    rw [ih]
    rfl
  case tensor ihX ihY =>
    simp
    rw [ihX, ihY]
    rfl

def mapQuiver {X Y : T C} (x : X ⟶ Y) :
    (FreeTwistedCategory.projectObj mkObj X ⟶ FreeTwistedCategory.projectObj mkObj Y) := by
  simp
  apply _root_.Quotient.mk
  apply Hom.comp
  · apply Hom.braid
    simp
    exact (λ_ _).inv ≫ _ ◁ (ρ_ _).inv
  apply Hom.comp
  · have x := Hom.layer ⟨𝟙_ _, X, Y, 0, x, 𝟙_ _⟩
    simp at x
    exact x
  · apply Hom.braid
    exact _ ◁ (ρ_ _).hom ≫ (λ_ _).hom

def toNat : TQ C ⥤ N C := project (C := C) (D := N C) mkObj mapQuiver

end CategoryTheory.NatDefinition

