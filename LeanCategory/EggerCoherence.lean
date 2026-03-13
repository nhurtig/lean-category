import Mathlib
import LeanCategory.Egger

open CategoryTheory

open Category MonoidalCategory

namespace CategoryTheory

namespace InvolutiveCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [InvolutiveCategory C]

inductive Pure : {X Y : C} → (X ⟶ Y) → Prop where
  | id : Pure (𝟙 _)
  | comp : Pure f → Pure g → Pure (f ≫ g)
  | tensor : Pure f → Pure g → Pure (f ⊗ₘ g)
  | whiskerLeft : Pure f → Pure (_ ◁ f)
  | whiskerRight : Pure f → Pure (f ▷ _)
  | star : Pure f → Pure f⋆
  | associator_hom : Pure (α_ _ _ _).hom
  | left_unitor_hom  : Pure (λ_ _).hom
  | right_unitor_hom  : Pure (ρ_ _).hom
  | skewator_hom  : Pure (χ_ _ _).hom
  | involutor_hom  : Pure (e_ _).hom
  | associator_inv : Pure (α_ _ _ _).inv
  | left_unitor_inv  : Pure (λ_ _).inv
  | right_unitor_inv  : Pure (ρ_ _).inv
  | skewator_inv  : Pure (χ_ _ _).inv
  | involutor_inv  : Pure (e_ _).inv

theorem coherence {X Y : C} {f g : X ⟶ Y} : Pure f → Pure g → f = g := sorry

end InvolutiveCategory
end CategoryTheory

