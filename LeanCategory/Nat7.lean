import Mathlib
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

-- True whenever there's one adjacent swap between two lists
def OneSwap : List α → List α → Prop
  | a::b::xs, b'::a'::ys => a = a' ∧ b = b' ∧ xs = ys -- there's the swap!
  | a::xs, a'::ys => a = a' ∧ OneSwap xs ys -- doesn't have to be at the start
  | [], [] => False -- but it has to be somewhere!
  | _::_, [] => False -- different lengths → nope!
  | [], _::_ => False -- different lengths → nope!

-- generators of the groupoid: positive crossings
instance myQuiver (α : Type) : Quiver (List α) :=
  ⟨fun X Y => OneSwap X Y⟩

#check myQuiver Unit

-- the free groupoid on these generators
def MyGroupoid (α : Type) := @Quiver.FreeGroupoid (List α)

#check MyGroupoid
