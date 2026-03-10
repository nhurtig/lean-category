import Mathlib
import LeanCategory.FreeEgger

namespace NatDefinition


section

variable (V : Type u)

inductive FreeTwistedCategoryNat : Type u
  | of : V → FreeTwistedCategoryNat
  | unit : FreeTwistedCategoryNat
  | tensor : FreeTwistedCategoryNat → FreeTwistedCategoryNat → FreeTwistedCategoryNat
  | star : FreeTwistedCategoryNat → FreeTwistedCategoryNat
  deriving Inhabited

end

notation "FN" => FreeTwistedCategoryNat

@[simp]
instance : MulOne (FN V) where
  one := .unit
  mul := .tensor

@[simp]
instance : Star (F V) where
  star := .star

/- @[simp] -/
/- def FtoFN : F V → FN V -/
/-   | .of v => .of v -/
/-   | .unit => .unit -/
/-   | .tensor X Y => .tensor (FtoFN X) (FtoFN Y) -/
/-   | .star X => .star (FtoFN X) -/

@[simp]
def FNtoF : FN V → F V
  | .of v => .of v
  | .unit => .unit
  | .tensor X Y => .tensor (FNtoF X) (FNtoF Y)
  | .star X => .star (FNtoF X)


/- class StarQuiver.{v} (V : Type u) extends (Quiver.{v, u} (F V)) where -/
/-   star {X Y : F V} : (X ⟶ Y) → (X.star ⟶ Y.star) -- TODO if there are problems, make this -/
  -- two-sided invertible

/- postfix:max "⋆" => StarQuiver.star -/

-- the generating objects (for us, strands)
/- variable {V : Type u} [stitches : Quiver.{v} (F V)] {star : {X Y : F V} → (X ⟶ Y) ≃ (X⋆ ⟶ Y⋆)} -/
variable {V : Type u} [stitches : Quiver.{v} (F V)]
/- variable {V : Type u} [stitches : Quiver.{v} (F V)] {star : {X Y : F V} → (X ⟶ Y) ≃ (X⋆ ⟶ Y⋆)} -/

/- #synth (Quiver (List <| V × Bool)) -/
-- A CanonicalStitch with a record of the identity strands on its left/right
-- TODO: maybe make two layers -- one for two+ outs, one for one out
#synth Quiver (F V)
section
variable (V : Type u) [stitches : Quiver.{v} (F V)]
/- variable (V : Type u) [stitches : Quiver.{v} (F V)] {star : {X Y : F V} → (X ⟶ Y) ≃ (X⋆ ⟶ Y⋆)} -/

/- inductive Starred where -/
/-   | IsStarred -/
/-   | NotStarred -/

/- instance : Neg Starred where -/
/-   neg -/
/-     | .IsStarred => .NotStarred -/
/-     | .NotStarred => .IsStarred -/

/- def Starred.act [Star α] (x : α) : s → α -/
/-   | IsStarred => x⋆ -/
/-   | NotStarred => x -/

structure Layer : Type max u v where
  left : FN V
  dom : FN V
  cod : FN V
  stars : ℕ
  box : (FNtoF dom) ⟶ (FNtoF cod)
  right : FN V
end

open CategoryTheory
open MonoidalCategory
open InvolutiveCategory
open TwistedCategory
open FreeTwistedCategory

def βcat : Category.{u} (F V) := categoryFreeTwistedCategory
infixr:10 " ⟶β " => βcat.Hom
notation "𝟙β" => βcat.id
infixr:80 " ≫β " => βcat.comp
infixr:10 " ≅β " => @Iso _ βcat
-- TODO these are all useless b/c we aren't extending anymore
def βtwist : TwistedCategory.{u} (F V) := freeTwistedCategory
infixr:70 " ⊗β " => βtwist.tensorObj
infixr:81 " ◁β " => βtwist.whiskerLeft
infixl:81 " ▷β " => βtwist.whiskerRight
infixr:70 " ⊗ₘβ " => βtwist.tensorHom
notation "𝟙_β " C:arg => βtwist.tensorUnit C
postfix:max "⋆β" => βtwist.starObj
postfix:max "⋆β" => βtwist.starHom

namespace Layer

inductive TopBottom where
  | Top
  | Bottom

open MonoidalCategory

/- def starMany [Star α] (x : α) : ℕ → α -/
/-   | 0 => x -/
/-   | n + 1 => Star.star (starMany x n) -/

/- @[simp] -/
/- lemma starMany_succ [Star α] {x : α} : starMany x (n + 1) = Star.star (starMany x n) := rfl -/

def boundary : TopBottom → Layer V → FN V
  | .Top, ⟨L, _, Y, s, _, R⟩ => L * (s.repeat .star Y * R)
  | .Bottom, ⟨L, X, _, s, _, R⟩ => L * (s.repeat .star X * R)

@[simp]
lemma boundary_top (l : Layer V) :
    l.boundary .Top = l.left * (l.stars.repeat .star l.cod * l.right) := rfl

@[simp]
lemma boundary_bottom (l : Layer V) :
    l.boundary .Bottom = l.left * (l.stars.repeat .star l.dom * l.right) := rfl

inductive Hom : Layer V → Layer V → Type max (u + 1) v where
  | comp : Hom l₁ l₂ → Hom l₂ l₃ → Hom l₁ l₃
  | free (l : ((FNtoF L₁) ⟶β (FNtoF L₂))) (r : ((FNtoF R₁) ⟶β (FNtoF R₂))) : Hom ⟨L₁, X, Y, s, x, R₁⟩ ⟨L₂, X, Y, s, x, R₂⟩ -- σ
  | twist_hom  : Hom ⟨L, X, Y, s + 1, x, R⟩ ⟨L, X, Y, s, x, R⟩
  | twist_inv  : Hom ⟨L, X, Y, s, x, R⟩ ⟨L, X, Y, s + 1, x, R⟩ -- Δ
  | box_strand_hom : Hom ⟨L, X, Y, s, x, A * R⟩ ⟨L * A, X, Y, s, x, R⟩ -- σ underline
  | box_strand_inv : Hom ⟨L * A, X, Y, s, x, R⟩ ⟨L, X, Y, s, x, A * R⟩
  | strand_box_hom : Hom ⟨L * A, X, Y, s, x, R⟩ ⟨L, X, Y, s, x, A * R⟩
  | strand_box_inv : Hom ⟨L,  X, Y, s, x, A * R⟩ ⟨L * A, X, Y, s, x, R⟩

infixr:10 " ⟶L " => Hom
-- do we even need a category on Layer?

namespace Hom

open TwistedCategory

@[simp]
def φ {l₁ l₂ : Layer V} (b : TopBottom) : (l₁ ⟶L l₂) → ((FNtoF <| l₁.boundary b) ⟶β (FNtoF <| l₂.boundary b))
  | comp f g => f.φ b ≫ g.φ b
  | free l r => by
      cases b <;> simp <;> exact l ⊗ₘ (𝟙 _) ⊗ₘ r
  | twist_hom => by
      cases b <;> simp <;> exact (𝟙 _) ⊗ₘ (ς_ _).hom ⊗ₘ (𝟙 _)
  | twist_inv => by
      cases b <;> simp <;> exact (𝟙 _) ⊗ₘ (ς_ _).inv ⊗ₘ (𝟙 _)
  | box_strand_hom => by
      cases b <;> simp <;> exact
        _ ◁ (α_ _ _ _).inv ≫
        (α_ _ _ _).inv ≫
        (_ ◁ (σ_ _ _).hom) ▷ _ ≫
        (α_ _ _ _).inv ▷ _ ≫
        (α_ _ _ _).hom
  | box_strand_inv => by
      cases b <;> simp <;> exact
        (α_ _ _ _).inv ≫
        (α_ _ _ _).hom ▷ _ ≫
        (_ ◁ (σ_ _ _).inv) ▷ _ ≫
        (α_ _ _ _).hom ≫
        _ ◁ (α_ _ _ _).hom
  | strand_box_hom => by
      cases b <;> simp <;> exact
        (α_ _ _ _).inv ≫
        (α_ _ _ _).hom ▷ _ ≫
        (_ ◁ (σ_ _ _).hom) ▷ _ ≫
        (α_ _ _ _).hom ≫
        _ ◁ (α_ _ _ _).hom
  | strand_box_inv => by
      cases b <;> simp <;> exact
        _ ◁ (α_ _ _ _).inv ≫
        (α_ _ _ _).inv ≫
        (_ ◁ (σ_ _ _).inv) ▷ _ ≫
        (α_ _ _ _).inv ▷ _ ≫
        (α_ _ _ _).hom

end Hom

-- Okay, forget about that. What about the "category of layers"? Objects would be Layer X Y.
-- Morphisms can mess with the left, mess with the right, star the box, and exchange
-- the box with something to move between the left and right. So it's on a triple?
-- Objects would be (F V) × Bool × (F V). This feels an awful like the F (S l) category...
-- Or, the objects could just be Layer X Y!. This IS the subgroupoid, just a silly
-- representation of it!!! Do we even need the Bool in the middle? I don't really think
-- so... we only need to track the objects when they change how morphisms might be able
-- to be applied. So then the morphisms are a twist on the box, morphisms on either side,
-- and exchanges between either side: ((A ⊗ B), C) → (A, B ⊗ C). Ugh, there's gonna be
-- all this junk about naturality and stuff. But do we care? We just need to say that
-- it's a category, right? Yeah, the injection φ gives it semantics, this is just
-- typed syntax.

-- So say s is a morphism ℓ₁ ⟶ ℓ₂, each Layer X Y. Then we can use φ, parameterized by
-- some b : TopBottom, to turn s into morphisms in F V: ℓ₁.boundary b ⟶β ℓ₂.boundary b.
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
-- α → TopBottom → F V. In the F V category of MyHom, we run map then flatten to get the
-- domain and codomain. We could even have EVERYTHING be a stitch! The identity strands are
-- just really tiny ones.

-- No, this doesn't work. If we use ⊕ to merge/split, then something that isn't using ⊕ can't split.
-- It's also unclear how we'd represent the boxes themselves within the layer. Okay, do we
-- need to use ⊕? Yeah, I think we do...

-- Okay, forget about that. What about the "category of layers"? Objects would be Layer X Y.
-- Morphisms can mess with the left, mess with the right, star the box, and exchange
-- the box with something to move between the left and right. So it's on a triple?
-- Objects would be (F V) × Bool × (F V). This feels an awful like the F (S l) category...
-- Or, the objects could just be Layer X Y!. This IS the subgroupoid, just a silly
-- representation of it!!! Do we even need the Bool in the middle? I don't really think
-- so... we only need to track the objects when they change how morphisms might be able
-- to be applied. So then the morphisms are a twist on the box, morphisms on either side,
-- and exchanges between either side: ((A ⊗ B), C) → (A, B ⊗ C). Ugh, there's gonna be
-- all this junk about naturality and stuff. But do we care? We just need to say that
-- it's a category, right? Yeah, the injection φ gives it semantics, this is just
-- typed syntax.

-- So say s is a morphism ℓ₁ ⟶ ℓ₂, each Layer X Y. Then we can use φ, parameterized by
-- some b : TopBottom, to turn s into morphisms in F V: ℓ₁.boundary b ⟶β ℓ₂.boundary b.
-- Invert the top one, we have on the bottom ℓ₁.dom →β ℓ₂.dom, compose with ℓ₂, then
-- ℓ₂.cod →β ℓ₁.cod!!!! DONE!

end NatDefinition.Layer

