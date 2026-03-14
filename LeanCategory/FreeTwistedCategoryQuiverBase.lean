import Mathlib
import LeanCategory.FreeTwistedCategoryBase

namespace CategoryTheory

variable (C : Type u)

open FreeTwistedCategory

structure FreeTwistedCategoryQuiver where
  as : T C

namespace FreeTwistedCategoryQuiver

variable {C : Type u}

scoped notation "TQ" => FreeTwistedCategoryQuiver

def unit : TQ C :=
  ⟨.unit⟩

def tensor (X Y : TQ C) : TQ C :=
  ⟨X.as.tensor Y.as⟩

def star (X : TQ C) : TQ C :=
  ⟨X.as.star⟩

def sizeOf : TQ C → ℕ
  | ⟨X⟩ => X.sizeOf

variable [Quiver.{v} (T C)]

inductive Hom : TQ C → TQ C → Type max u v
  | of {X Y : TQ C} (f : X.as ⟶ Y.as) : Hom X Y
  | id (X) : Hom X X
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : TQ C) {Y₁ Y₂} (f : Hom Y₁ Y₂) :
      Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : TQ C) :
      Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)
  | α_hom (X Y Z : TQ C) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : TQ C) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : Hom (FreeTwistedCategoryQuiver.unit.tensor X) X
  | l_inv (X) : Hom X (FreeTwistedCategoryQuiver.unit.tensor X)
  | ρ_hom (X : TQ C) : Hom (X.tensor .unit) X
  | ρ_inv (X : TQ C) : Hom X (X.tensor .unit)
  | star {X Y} (f : Hom X Y) : Hom X.star Y.star
  | χ_hom (X Y : TQ C) : Hom (X.star.tensor  Y.star) (Y.tensor X).star
  | χ_inv (X Y : TQ C) : Hom (Y.tensor X).star (X.star.tensor Y.star)
  | ε_hom (X : TQ C) : Hom X.star.star X
  | ε_inv (X : TQ C) : Hom X X.star.star
  | twist_hom (X : TQ C) : Hom X.star X
  | twist_inv (X : TQ C) : Hom X X.star

scoped infixr:10 " ⟶tq " => Hom -- t for "twisted"

-- whether a morphism is coherent (aka, doesn't contain twists)
@[simp]
def Hom.Pure {X Y : TQ C} : (X ⟶tq Y) → Prop
  | of _ => False
  | id _ => True
  | comp f g => f.Pure ∧ g.Pure
  | whiskerLeft _ f => f.Pure
  | whiskerRight f _ => f.Pure
  | tensor f g => f.Pure ∧ g.Pure
  | α_hom _ _ _ => True
  | α_inv _ _ _ => True
  | l_hom _ => True
  | l_inv _ => True
  | ρ_hom _ => True
  | ρ_inv _ => True
  | star f => True
  | χ_hom _ _ => True
  | χ_inv _ _ => True
  | ε_hom _ => True
  | ε_inv _ => True
  | twist_hom _ => False
  | twist_inv _ => False

end CategoryTheory.FreeTwistedCategoryQuiver

