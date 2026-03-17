import Mathlib
import LeanCategory.FreeTwisted.Base
import LeanCategory.FreeTwisted.Instance

namespace CategoryTheory

variable (C : Type u)

open FreeTwistedCategory

structure NatDefinition where
  as : T C

namespace NatDefinition

variable {C : Type u}

scoped notation "N" => NatDefinition

abbrev of (c : C) : N C :=
  ⟨.of c⟩

abbrev unit : N C :=
  ⟨.unit⟩

abbrev tensor (X Y : N C) : N C :=
  ⟨X.as.tensor Y.as⟩

abbrev star (X : N C) : N C :=
  ⟨X.as.star⟩

/- @[simp] lemma as_of (c : C) : (of c).as = .of c := rfl -/
/- @[simp] lemma as_unit : (@unit C).as = .unit := rfl -/
/- @[simp] lemma as_tensor (X Y : N C) : (tensor X Y).as = X.as.tensor Y.as := rfl -/
/- @[simp] lemma as_star (X : N C) : (star X).as = X.as.star := rfl -/
/- @[simp] lemma rw_of (c : C) : ⟨.of c⟩ = of c := rfl -/

open MonoidalCategory InvolutiveCategory
/- @[simp] lemma mk_tensor (X Y : T C) : -/
/-     NatDefinition.mk (X ⊗ Y) = (NatDefinition.mk X).tensor (NatDefinition.mk Y) := rfl -/
/- @[simp] lemma mk_star (X : T C) : -/
/-     NatDefinition.mk X⋆ = star (NatDefinition.mk X) := rfl -/
@[simp] lemma tensor_def {X Y : N C} : X.tensor Y = mk (X.as ⊗ Y.as) := rfl
@[simp] lemma star_def {X : N C} : X.star = mk (X.as⋆) := rfl
@[simp] lemma of_def (c : C) : of c = mk (.of c) := rfl
@[simp] lemma unit_def : @unit C = mk .unit := rfl

/- def recOn' {P : N C → Sort*} (X : N C) (unit : P unit) (of : ∀ c, P (of c)) -/
/-     (tensor : ∀ X Y, P X → P Y → P (tensor X Y)) (star : ∀ X, P X → P (star X)) : -/
/-     P X := match X with -/
/-   | ⟨⟨.unit⟩⟩ => unit -/
/-   | ⟨⟨.of c⟩⟩ => of c -/
/-   | ⟨⟨.tensor X Y⟩⟩ => tensor ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ -/
/-       (recOn' ⟨⟨X⟩⟩ unit of tensor star) (recOn' ⟨⟨Y⟩⟩ unit of tensor star) -/
/-   | ⟨⟨.star X⟩⟩ => star ⟨⟨X⟩⟩ (recOn' ⟨⟨X⟩⟩ unit of tensor star) -/

def map (f : C → D) (X : N C) : N D := ⟨X.as.map f⟩

/- @[simp] lemma map_of (f : C → D) (c : C) : map f (of c) = of (f c) := rfl -/
/- @[simp] lemma map_unit (f : C → D) : map f unit = unit := rfl -/
/- @[simp] lemma map_tensor (f : C → D) (X Y : N C) : -/
/-     map f (tensor X Y) = tensor (map f X) (map f Y) := rfl -/
/- @[simp] lemma map_star (f : C → D) (X : N C) : map f (star X) = star (map f X) := rfl -/
@[simp] lemma map_as (f : C → D) (X : N C) : X.as.map f = (map f X).as := rfl

@[simp]
def sizeOf : N C → ℕ
  | ⟨X⟩ => X.sizeOf

variable [Quiver.{v} (T C)]

end CategoryTheory.NatDefinition

