import Mathlib
import LeanCategory.FreeInvolutive.Base

namespace CategoryTheory

variable (C : Type u)

open FreeInvolutiveCategory

-- a wrapper so we don't run into instance
-- synthesis issues: category on I C vs. category
-- on T C
structure FreeTwistedCategory where
  as : I C

namespace FreeTwistedCategory

variable {C : Type u}

scoped notation "T" => FreeTwistedCategory

def of (c : C) : T C :=
  ⟨.of c⟩

@[simp] lemma of_as (c : C) : (of c).as = .of c := rfl
@[simp] lemma rw_of (c : C) : ⟨.of c⟩ = of c := rfl

def unit : T C :=
  ⟨.unit⟩

def tensor (X Y : T C) : T C :=
  ⟨X.as.tensor Y.as⟩

def star (X : T C) : T C :=
  ⟨X.as.star⟩

def recOn' {P : T C → Sort*} (X : T C) (unit : P unit) (of : ∀ c, P (of c))
    (tensor : ∀ X Y, P X → P Y → P (tensor X Y)) (star : ∀ X, P X → P (star X)) :
    P X := match X with
  | ⟨.unit⟩ => unit
  | ⟨.of c⟩ => of c
  | ⟨.tensor X Y⟩ => tensor ⟨X⟩ ⟨Y⟩
      (recOn' ⟨X⟩ unit of tensor star) (recOn' ⟨Y⟩ unit of tensor star)
  | ⟨.star X⟩ => star ⟨X⟩ (recOn' ⟨X⟩ unit of tensor star)

def map (f : C → D) (X : T C) : T D := ⟨X.as.map f⟩

@[simp] lemma map_of (f : C → D) (c : C) : map f (of c) = of (f c) := rfl
@[simp] lemma map_unit (f : C → D) : map f unit = unit := rfl
@[simp] lemma map_tensor (f : C → D) (X Y : T C) :
    map f (tensor X Y) = tensor (map f X) (map f Y) := rfl
@[simp] lemma map_star (f : C → D) (X : T C) : map f (star X) = star (map f X) := rfl
@[simp] lemma map_as (f : C → D) (X : T C) : X.as.map f = (map f X).as := rfl

@[simp]
def sizeOf : T C → ℕ
  | ⟨X⟩ => X.sizeOf

inductive Hom : T C → T C → Type max u v
  | id (X) : Hom X X
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : T C) {Y₁ Y₂} (f : Hom Y₁ Y₂) :
      Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : T C) :
      Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)
  | α_hom (X Y Z : T C) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : T C) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : Hom (FreeTwistedCategory.unit.tensor X) X
  | l_inv (X) : Hom X (FreeTwistedCategory.unit.tensor X)
  | ρ_hom (X : T C) : Hom (X.tensor .unit) X
  | ρ_inv (X : T C) : Hom X (X.tensor .unit)
  | star {X Y} (f : Hom X Y) : Hom X.star Y.star
  | χ_hom (X Y : T C) : Hom (X.star.tensor  Y.star) (Y.tensor X).star
  | χ_inv (X Y : T C) : Hom (Y.tensor X).star (X.star.tensor Y.star)
  | ε_hom (X : T C) : Hom X.star.star X
  | ε_inv (X : T C) : Hom X X.star.star
  | twist_hom (X : T C) : Hom X.star X
  | twist_inv (X : T C) : Hom X X.star

scoped infixr:10 " ⟶t " => Hom -- t for "twisted"

@[simp]
def Hom.inv {X Y : T C} : (X ⟶t Y) → (Y ⟶t X)
  | id X => id X
  | comp f g => comp (g.inv) (f.inv)
  | whiskerLeft X f => whiskerLeft X (f.inv)
  | whiskerRight f Y => whiskerRight (f.inv) Y
  | tensor f g => tensor (f.inv) (g.inv)
  | α_hom X Y Z => α_inv X Y Z
  | α_inv X Y Z => α_hom X Y Z
  | l_hom X => l_inv X
  | l_inv X => l_hom X
  | ρ_hom X => ρ_inv X
  | ρ_inv X => ρ_hom X
  | star f => star (f.inv)
  | χ_hom X Y => χ_inv X Y
  | χ_inv X Y => χ_hom X Y
  | ε_hom X => ε_inv X
  | ε_inv X => ε_hom X
  | twist_hom X => twist_inv X
  | twist_inv X => twist_hom X

-- whether a morphism is coherent (aka, doesn't contain twists)
@[simp]
def Hom.Pure {X Y : T C} : (X ⟶t Y) → Prop
  | id _ => True
  | comp f g => f.Pure ∧ g.Pure
  | tensor f g => f.Pure ∧ g.Pure
  | whiskerLeft _ f => f.Pure
  | whiskerRight f _ => f.Pure
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

lemma Pure_inv_Pure {X Y : T C} : ∀ f : X ⟶t Y, f.Pure → f.inv.Pure := by
  intros f
  induction f <;> simp_all

end CategoryTheory.FreeTwistedCategory

