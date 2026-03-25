import Mathlib
import LeanCategory.FreeTwisted.Base
import LeanCategory.FreeTwisted.Instance

namespace CategoryTheory

variable (C : Type u)

open FreeTwistedCategory

/--
An object in the fused braids category over a type `C`.
These have the same shape as the other objects; again we define
a new structure to avoid instance synthesis issues.
-/
structure FusedBraids where
  as : T C

namespace FusedBraids

variable {C : Type u}

@[inherit_doc FusedBraids]
scoped notation "FB" => FusedBraids

abbrev of (c : C) : FB C :=
  ⟨.of c⟩

abbrev unit : FB C :=
  ⟨.unit⟩

abbrev tensor (X Y : FB C) : FB C :=
  ⟨X.as.tensor Y.as⟩

abbrev star (X : FB C) : FB C :=
  ⟨X.as.star⟩

open MonoidalCategory InvolutiveCategory

@[simp] lemma tensor_def {X Y : FB C} : X.tensor Y = mk (X.as ⊗ Y.as) := rfl
@[simp] lemma star_def {X : FB C} : X.star = mk (X.as⋆) := rfl
@[simp] lemma of_def (c : C) : of c = mk (.of c) := rfl
@[simp] lemma unit_def : @unit C = mk .unit := rfl

def map (f : C → D) (X : FB C) : FB D := ⟨X.as.map f⟩

@[simp] lemma map_as (f : C → D) (X : FB C) : X.as.map f = (map f X).as := rfl

@[simp]
def sizeOf : FB C → ℕ
  | ⟨X⟩ => X.sizeOf

variable [Quiver.{v} (T C)]

end CategoryTheory.FusedBraids

