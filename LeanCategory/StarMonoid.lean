import Mathlib

postfix:max "⋆" => Star.star

class StarMonoid (R : Type u) extends Monoid R, InvolutiveStar R where
  /-- `star` skew-distributes over multiplication. -/
  star_mul : ∀ r s : R, (r * s)⋆ = s⋆ * r⋆ := by aesop
