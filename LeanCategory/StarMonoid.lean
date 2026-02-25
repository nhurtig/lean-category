import Mathlib

postfix:max "⋆" => Star.star

class StarMonoid (R : Type u) extends Monoid R, InvolutiveStar R where
  /-- `star` skew-distributes over multiplication. -/
  star_mul : ∀ r s : R, (r * s)⋆ = s⋆ * r⋆ := by aesop

def FreeStarMonoid (R : Type u) : StarMonoid (List (R × Bool)) where
  mul r s := r ++ s
  one := []
  star r := r.reverse.map (fun x ↦ (x.1, !x.2))
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil
  star_involutive r := by
    simp
    ext i
    simp
  star_mul r s := by
    simp [HMul.hMul]

