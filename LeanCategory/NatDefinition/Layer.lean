import Mathlib
import LeanCategory.FreeInvolutive.InvolutiveComp
import LeanCategory.FreeTwisted.Instance
import LeanCategory.NatDefinition.Base

namespace CategoryTheory.NatDefinition

open CategoryTheory
open scoped FreeTwistedCategory
open scoped NatDefinition


variable {C : Type u}

-- the Quiver (T C) will blow away our ability
-- to synthesize this, so we give it a name to
-- use later
def Tcat : Category.{u} (T C) := inferInstance
scoped infixr:10 " ⟶T " => Tcat.Hom

scoped notation X "^⋆" n => Nat.repeat InvolutiveCategoryStruct.starObj n X

open InvolutiveCategory

lemma repeat_star_succ (X : T C) (n : ℕ) :
    (X^⋆(n + 1)) = (X^⋆n)⋆ := rfl

lemma repeat_star_zero (X : T C) :
    (X^⋆0) = X := rfl

variable [Quiver.{v} (T C)]

section
variable (C : Type u) [Quiver.{v} (T C)]

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

inductive TopBottom where
  | Top
  | Bottom

instance : Neg TopBottom where
  neg
    | .Top => .Bottom
    | .Bottom => .Top

open MonoidalCategory

def boundary : TopBottom → Layer C → T C
  | .Top, ⟨L, _, Y, s, _, R⟩ => L ⊗ (Y^⋆s) ⊗ R
  | .Bottom, ⟨L, X, _, s, _, R⟩ => L ⊗ (X^⋆s) ⊗ R

@[simp]
lemma boundary_top (l : Layer C) :
    l.boundary .Top = l.left ⊗ ((l.cod^⋆l.stars) ⊗ l.right) := rfl

@[simp]
lemma boundary_bottom (l : Layer C) :
    l.boundary .Bottom = l.left ⊗ ((l.dom^⋆l.stars) ⊗ l.right) := rfl

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

namespace Hom

open InvolutiveCategory TwistedCategory

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

-- Okay, forget about that. What about the "category of layers"? Objects would be Layer X Y.
-- Morphisms can mess with the left, mess with the right, star the box, and exchange
-- the box with something to move between the left and right. So it's on a triple?
-- Objects would be (T C) × Bool × (T C). This feels an awful like the F (S l) category...
-- Or, the objects could just be Layer X Y!. This IS the subgroupoid, just a silly
-- representation of it!!! Do we even need the Bool in the middle? I don't really think
-- so... we only need to track the objects when they change how morphisms might be able
-- to be applied. So then the morphisms are a twist on the box, morphisms on either side,
-- and exchanges between either side: ((A ⊗ B), C) → (A, B ⊗ C). Ugh, there's gonna be
-- all this junk about naturality and stuff. But do we care? We just need to say that
-- it's a category, right? Yeah, the injection φ gives it semantics, this is just
-- typed syntax.

-- So say s is a morphism ℓ₁ ⟶ ℓ₂, each Layer X Y. Then we can use φ, parameterized by
-- some b : TopBottom, to turn s into morphisms in T C: ℓ₁.boundary b ⟶β ℓ₂.boundary b.
-- Invert the top one, we have on the bottom ℓ₁.dom →β ℓ₂.dom, compose with ℓ₂, then
-- ℓ₂.cod →β ℓ₁.cod!!!! DONE!

-- (old stuff below; decided idea wouldn't work)

-- AAHHHHH! Make each Layer contain its own subgroupoid type, and define a layer's
-- MyHom type using the injection φ! Now Layers can contain multiple, duplicated, boxes (who cares,
-- this is easy to reconfigure, right?). Actually, that could technically break the isomorphism.
-- Maybe we need a Layer split/merge rule if we do this... a Layer can split over tensor...
-- but this messes with the indices and the left/right-ness. Maybe a Layer doesn't necessarily
-- have unique strand IDs, but the generators are of a different type? Yeah, each Layer
-- has its own type for strand IDs, and its own strand projection into the real world. This
-- way, when they merge they just do an ⊕ of their types. The ⊕ has some nasty commutative
-- conversion junk, but the nice thing is that it's lost on the functor into the quivered
-- category, which is what we want to canonicalize anyways. Very annoying that all the index
-- work seems to have been for naught, though.

-- So a Layer is indexed by some type; we'll call it α. It has an object (F α), and a projection
-- α → TopBottom → T C. In the T C category of MyHom, we run map then flatten to get the
-- domain and codomain. We could even have EVERYTHING be a stitch! The identity strands are
-- just really tiny ones.

-- No, this doesn't work. If we use ⊕ to merge/split, then something that isn't using ⊕ can't split.
-- It's also unclear how we'd represent the boxes themselves within the layer. Okay, do we
-- need to use ⊕? Yeah, I think we do...

-- Okay, forget about that. What about the "category of layers"? Objects would be Layer X Y.
-- Morphisms can mess with the left, mess with the right, star the box, and exchange
-- the box with something to move between the left and right. So it's on a triple?
-- Objects would be (T C) × Bool × (T C). This feels an awful like the F (S l) category...
-- Or, the objects could just be Layer X Y!. This IS the subgroupoid, just a silly
-- representation of it!!! Do we even need the Bool in the middle? I don't really think
-- so... we only need to track the objects when they change how morphisms might be able
-- to be applied. So then the morphisms are a twist on the box, morphisms on either side,
-- and exchanges between either side: ((A ⊗ B), C) → (A, B ⊗ C). Ugh, there's gonna be
-- all this junk about naturality and stuff. But do we care? We just need to say that
-- it's a category, right? Yeah, the injection φ gives it semantics, this is just
-- typed syntax.

-- So say s is a morphism ℓ₁ ⟶ ℓ₂, each Layer X Y. Then we can use φ, parameterized by
-- some b : TopBottom, to turn s into morphisms in T C: ℓ₁.boundary b ⟶β ℓ₂.boundary b.
-- Invert the top one, we have on the bottom ℓ₁.dom →β ℓ₂.dom, compose with ℓ₂, then
-- ℓ₂.cod →β ℓ₁.cod!!!! DONE!

end CategoryTheory.NatDefinition.Layer

