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

@[simp]
instance : MulOne (F C) where
  one := unit
  mul := tensor

@[simp]
instance : Star (F C) where
  star := star

end FreeTwistedCategory
end CategoryTheory

