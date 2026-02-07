import Mathlib
import LeanCategory.Instances

universe u

open BraidGroupoid
namespace KnitCategory

inductive Dir where
| left : Dir
| right : Dir
deriving Repr, DecidableEq

instance : Neg Dir where
  neg
    | Dir.left => Dir.right
    | Dir.right => Dir.left

inductive Bed where
| front : Bed
| back : Bed
deriving Repr, DecidableEq

instance : Neg Bed where
  neg
    | Bed.front => Bed.back
    | Bed.back => Bed.front

@[grind]
inductive BoxInfo (α : Type u) where
| tuck : α → Dir → BoxInfo α
| split : (carriers : MonoidalWord+ α) → (loops : MonoidalWord α) → Dir → Bed → BoxInfo α
deriving Repr
-- no drop: that's been laddered out already. Let's just ignore that the drops need to
-- be glued on to the splits for now; TODO don't ignore that

def BoxInfo.dom : BoxInfo α → MonoidalWord α
  | tuck a _ => a
  | split c l .left _ => l * c
  | split c l .right _ => c * l

@[simp, grind =]
def BoxInfo.cod : BoxInfo α → MonoidalWord α
  | tuck a _ => a * a
  | split c l .left _ => (c * c) * l
  | split c l .right _ => l * (c * c)

-- A stitch with a record of the identity strands on its left/right
-- TODO: maybe make two layers -- one for two+ outs, one for one out
structure Layer (dom cod : MonoidalWord α) where
  left : MonoidalWord α
  box : BoxInfo α
  right : MonoidalWord α
  hdom : dom ≈ left * box.dom * right := by grind
  hcod : cod ≈ left * box.cod * right := by grind
deriving Repr

inductive Hom {α : Type u} : MonoidalWord α → MonoidalWord α → Type u
    | id (X : MonoidalWord α) : Hom X X
    | braid (f : X ⟶ Y) : Hom X Y
    | layer (L : Layer X Y) : Hom X Y
    | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z

scoped[ KnitCategory ] infixr:10 " ⟶ᵏ " => Hom

-- TODO these Coe's do absolutely nothing...
instance : Coe (X ⟶ Y) (X ⟶ᵏ Y) where coe := .braid

instance : Coe (Layer X Y) (X ⟶ᵏ Y) where coe := .layer

end KnitCategory
