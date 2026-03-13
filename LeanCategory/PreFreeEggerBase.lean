import Mathlib
import LeanCategory.Egger

namespace CategoryTheory

variable {C : Type u}

section

variable (C : Type u)

inductive FreeTwistedCategory : Type u
  | of : C → FreeTwistedCategory
  | unit : FreeTwistedCategory
  | tensor : FreeTwistedCategory → FreeTwistedCategory → FreeTwistedCategory
  | star : FreeTwistedCategory → FreeTwistedCategory
  deriving Inhabited

end

namespace FreeTwistedCategory

notation "F" => FreeTwistedCategory

def sizeOf : F C → ℕ
  | of _ => 0
  | unit => 0
  | tensor A B => A.sizeOf + B.sizeOf + 1
  | star A => A.sizeOf + 1

@[simp]
instance : MulOne (F C) where
  one := unit
  mul := tensor

@[simp]
instance : Star (F C) where
  star := star

end FreeTwistedCategory
end CategoryTheory

