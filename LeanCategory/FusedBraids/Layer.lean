import Mathlib
import LeanCategory.InvolutiveComp
import LeanCategory.FreeTwisted.Functor
import LeanCategory.FusedBraids.Base

namespace CategoryTheory.FusedBraids

open CategoryTheory
open scoped FreeTwistedCategory
open scoped FusedBraids

variable {C : Type u}

/--
Notation for repeated application of the involutive category's
star on an object.
-/
scoped notation X "^⋆" n => Nat.repeat InvolutiveCategoryStruct.starObj n X

open InvolutiveCategory

lemma repeat_star_succ (X : T C) (n : ℕ) :
    (X^⋆(n + 1)) = (X^⋆n)⋆ := rfl

@[simp]
lemma repeat_star_zero (X : T C) :
    (X^⋆0) = X := rfl

variable [Quiver.{v} (T C)]

section
variable (C : Type u) [Quiver.{v} (T C)]

/--
A `Layer C` is a morphism from the quiver, with some amount of 180 degree flips on the
morphism and identity morphisms (whiskers) on either side.
-/
structure Layer : Type max u v where
  left : T C
  dom : T C
  cod : T C
  stars : ℕ -- how many times the box has been rotated
            -- (doesn't rotate the strands to either side)
  box : dom ⟶ cod
  right : T C
end

namespace Layer

/--
A helper type, isomorphic to `Bool`, that records whether we're
referring to the `Top` (codomain) or `Bottom` (domain) of a layer.
-/
inductive TopBottom where
  | Top
  | Bottom

instance : Neg TopBottom where
  neg
    | .Top => .Bottom
    | .Bottom => .Top

open MonoidalCategory

/--
The domain/codomain of a layer. The left and right whiskers
don't depend on the `TopBottom` choice, but the middle box does.
-/
def boundary : TopBottom → Layer C → T C
  | .Top, ⟨L, _, Y, s, _, R⟩ => L ⊗ (Y^⋆s) ⊗ R
  | .Bottom, ⟨L, X, _, s, _, R⟩ => L ⊗ (X^⋆s) ⊗ R

@[simp]
lemma boundary_top (l : Layer C) :
    l.boundary .Top = l.left ⊗ ((l.cod^⋆l.stars) ⊗ l.right) := rfl

@[simp]
lemma boundary_bottom (l : Layer C) :
    l.boundary .Bottom = l.left ⊗ ((l.dom^⋆l.stars) ⊗ l.right) := rfl

/--
Premorphisms (note we never quotient to make morphisms for this) on
Layers: rewrites between layers. These morphisms include twisting the
strands in the left and right objects (`freeLeft` and `freeRight`),
twisting the whole box (the `twist_hom` and `twist_inv`), and braiding
the box with the objects to its left and right
(`box_strand_hom`, `box_strand_inv`, `strand_box_hom`, and `strand_box_inv`).
Additionally, there's the involutor `ε_hom` and its inverse `ε_inv`, which
represents the involution of the star on the box.
-/
inductive Hom : Layer C → Layer C → Type max (u + 1) v where
  | comp : Hom l₁ l₂ → Hom l₂ l₃ → Hom l₁ l₃
  | freeLeft (l : (L₁ ⟶T L₂)) : Hom ⟨L₁, X, Y, s, x, R⟩ ⟨L₂, X, Y, s, x, R⟩ -- σ
  | freeRight (r : (R₁ ⟶T R₂)) : Hom ⟨L, X, Y, s, x, R₁⟩ ⟨L, X, Y, s, x, R₂⟩ -- σ
  | twist_hom  : Hom ⟨L, X, Y, s + 1, x, R⟩ ⟨L, X, Y, s, x, R⟩
  | twist_inv  : Hom ⟨L, X, Y, s, x, R⟩ ⟨L, X, Y, s + 1, x, R⟩ -- Δ
  | ε_hom  : Hom ⟨L, X, Y, s + 2, x, R⟩ ⟨L, X, Y, s, x, R⟩
  | ε_inv  : Hom ⟨L, X, Y, s, x, R⟩ ⟨L, X, Y, s + 2, x, R⟩
  | box_strand_hom (L X Y s R A) {x : X ⟶ Y} :
      Hom ⟨L, X, Y, s, x, A.tensor R⟩ ⟨L.tensor A, X, Y, s, x, R⟩ -- σ underline
  | box_strand_inv (L X Y s R A) {x : X⟶ Y} :
      Hom ⟨L.tensor A, X, Y, s, x, R⟩ ⟨L, X, Y, s, x, A.tensor R⟩
  | strand_box_hom (L X Y s R A) {x : X⟶ Y} :
      Hom ⟨L.tensor A, X, Y, s, x, R⟩ ⟨L, X, Y, s, x, A.tensor R⟩
  | strand_box_inv (L X Y s R A) {x : X⟶ Y} :
      Hom ⟨L, X, Y, s, x, A.tensor R⟩ ⟨L.tensor A, X, Y, s, x, R⟩

infixr:10 " ⟶l " => Hom
-- do we even need a category on Layer? Not right now, but it'd
-- be nice to eventually talk about how the free moves commute with the
-- box moves, and the free moves merge, and the box moves cancel...
--
-- We could even say that the category is the one induced by φ!

namespace Hom

open InvolutiveCategory TwistedCategory

/--
`φ` is a "functor" (not truly a functor, because we haven't made `Layer.Hom` into
a category) that emits the morphisms in the free twisted category
that go above and below the layer as it is rewritten by the `Layer.Hom` premorphism.
See the `layer` rewrite rule in `FusedBraids.Basic` for how this is used.
-/
@[simp]
def φ {l₁ l₂ : Layer C} (b : TopBottom) : (l₁ ⟶l l₂) → ((l₁.boundary b) ⟶T (l₂.boundary b))
  | comp f g => f.φ b ≫ g.φ b
  | freeLeft l => by
      cases b <;> simp <;> exact l ▷ _
  | freeRight r => by
      cases b <;> simp <;> exact _ ◁ _ ◁ r
  | twist_hom => by
      cases b <;> simp <;> exact _ ◁ (ς_ _).hom ▷ _
  | twist_inv => by
      cases b <;> simp <;> exact _ ◁ (ς_ _).inv ▷ _
  | ε_hom => by
      cases b <;> simp <;> exact _ ◁ (e_ _).hom ▷ _
  | ε_inv => by
      cases b <;> simp <;> exact _ ◁ (e_ _).inv ▷ _
  | box_strand_hom L X Y s R A => match b with
      | .Top => by simp ; exact (𝟙 _ ⊗⋆≫
          L ◁ (σ_ (Y^⋆s) A).hom ▷ R ⊗⋆≫ 𝟙 _)
      | .Bottom => by simp ; exact (𝟙 _ ⊗⋆≫
          L ◁ (σ_ (X^⋆s) A).hom ▷ R ⊗⋆≫ 𝟙 _)
  | box_strand_inv L X Y s R A => match b with
      | .Top => by simp ; exact (𝟙 _ ⊗⋆≫
          L ◁ (σ_ (Y^⋆s) A).inv ▷ R ⊗⋆≫ 𝟙 _)
      | .Bottom => by simp ; exact (𝟙 _ ⊗⋆≫
          L ◁ (σ_ (X^⋆s) A).inv ▷ R ⊗⋆≫ 𝟙 _)
  | strand_box_hom L X Y s R A => match b with
      | .Top => by simp ; exact (𝟙 _ ⊗⋆≫
          L ◁ (σ_ A (Y^⋆s)).hom ▷ R ⊗⋆≫ 𝟙 _)
      | .Bottom => by simp ; exact (𝟙 _ ⊗⋆≫
          L ◁ (σ_ A (X^⋆s)).hom ▷ R ⊗⋆≫ 𝟙 _)
  | strand_box_inv L X Y s R A => match b with
      | .Top => by simp ; exact (𝟙 _ ⊗⋆≫
          L ◁ (σ_ A (Y^⋆s)).inv ▷ R ⊗⋆≫ 𝟙 _)
      | .Bottom => by simp ; exact (𝟙 _ ⊗⋆≫
          L ◁ (σ_ A (X^⋆s)).inv ▷ R ⊗⋆≫ 𝟙 _)

end Hom

end CategoryTheory.FusedBraids.Layer

