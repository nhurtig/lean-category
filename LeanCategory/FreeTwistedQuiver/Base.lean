import Mathlib
import LeanCategory.FreeTwisted.Base

namespace CategoryTheory

variable (C : Type u)

open FreeTwistedCategory

structure FreeTwistedCategoryQuiver where
  as : T C

namespace FreeTwistedCategoryQuiver

variable {C : Type u}

scoped notation "TQ" => FreeTwistedCategoryQuiver

def of (c : C) : TQ C :=
  ⟨.of c⟩

@[simp] lemma of_as (c : C) : (of c).as = .of c := rfl
@[simp] lemma rw_of (c : C) : ⟨.of c⟩ = of c := rfl

def unit : TQ C :=
  ⟨.unit⟩

def tensor (X Y : TQ C) : TQ C :=
  ⟨X.as.tensor Y.as⟩

def star (X : TQ C) : TQ C :=
  ⟨X.as.star⟩

def recOn' {P : TQ C → Sort*} (X : TQ C) (unit : P unit) (of : ∀ c, P (of c))
    (tensor : ∀ X Y, P X → P Y → P (tensor X Y)) (star : ∀ X, P X → P (star X)) :
    P X := match X with
  | ⟨⟨.unit⟩⟩ => unit
  | ⟨⟨.of c⟩⟩ => of c
  | ⟨⟨.tensor X Y⟩⟩ => tensor ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩
      (recOn' ⟨⟨X⟩⟩ unit of tensor star) (recOn' ⟨⟨Y⟩⟩ unit of tensor star)
  | ⟨⟨.star X⟩⟩ => star ⟨⟨X⟩⟩ (recOn' ⟨⟨X⟩⟩ unit of tensor star)

def map (f : C → D) (X : TQ C) : TQ D := ⟨X.as.map f⟩

@[simp] lemma map_of (f : C → D) (c : C) : map f (of c) = of (f c) := rfl
@[simp] lemma map_unit (f : C → D) : map f unit = unit := rfl
@[simp] lemma map_tensor (f : C → D) (X Y : TQ C) :
    map f (tensor X Y) = tensor (map f X) (map f Y) := rfl
@[simp] lemma map_star (f : C → D) (X : TQ C) : map f (star X) = star (map f X) := rfl
@[simp] lemma map_as (f : C → D) (X : TQ C) : X.as.map f = (map f X).as := rfl

@[simp]
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
  | star f => f.Pure
  | α_hom _ _ _ => True
  | α_inv _ _ _ => True
  | l_hom _ => True
  | l_inv _ => True
  | ρ_hom _ => True
  | ρ_inv _ => True
  | χ_hom _ _ => True
  | χ_inv _ _ => True
  | ε_hom _ => True
  | ε_inv _ => True
  | twist_hom _ => False
  | twist_inv _ => False

end CategoryTheory.FreeTwistedCategoryQuiver

