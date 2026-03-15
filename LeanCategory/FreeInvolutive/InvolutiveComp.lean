import Mathlib
import LeanCategory.Basic

-- TODO this does not belong in the FreeInvolutive folder

/-!
# Involutive composition `⊗⋆≫` (composition up to associators/unitors/skewators/involutors)

We provide `f ⊗≫ g`, the `monoidalComp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.

## Example

Suppose we have a braiding morphism `R X Y : X ⊗ Y ⟶ Y ⊗ X` in a monoidal category, and that we
want to define the morphism with the type `V₁ ⊗ V₂ ⊗ V₃ ⊗ V₄ ⊗ V₅ ⟶ V₁ ⊗ V₃ ⊗ V₂ ⊗ V₄ ⊗ V₅` that
transposes the second and third components by `R V₂ V₃`. How to do this? The first guess would be
to use the whiskering operators `◁` and `▷`, and define the morphism as `V₁ ◁ R V₂ V₃ ▷ V₄ ▷ V₅`.
However, this morphism has the type `V₁ ⊗ ((V₂ ⊗ V₃) ⊗ V₄) ⊗ V₅ ⟶ V₁ ⊗ ((V₃ ⊗ V₂) ⊗ V₄) ⊗ V₅`,
which is not what we need. We should insert suitable associators. The desired associators can,
in principle, be defined by using the primitive three-components associator
`α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` as a building block, but writing down actual definitions
are quite tedious, and we usually don't want to see them.

The monoidal composition `⊗≫` is designed to solve such a problem. In this case, we can define the
desired morphism as `𝟙 _ ⊗≫ V₁ ◁ R V₂ V₃ ▷ V₄ ▷ V₅ ⊗≫ 𝟙 _`, where the first and the second `𝟙 _`
are completed as `𝟙 (V₁ ⊗ V₂ ⊗ V₃ ⊗ V₄ ⊗ V₅)` and `𝟙 (V₁ ⊗ V₃ ⊗ V₂ ⊗ V₄ ⊗ V₅)`, respectively.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory InvolutiveCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open scoped MonoidalCategory

/--
A typeclass carrying a choice of monoidal structural isomorphism between two objects.
Used by the `⊗≫` monoidal composition operator, and the `coherence` tactic.
-/
-- We could likely turn this into a `Prop`-valued existential if that proves useful.
-- Nat note: this is morally different from CategoryTheory.InvolutiveCategory.InvolutiveCoherence,
-- which is used for listing out a bunch of things, and then stating they're coherent. This one
-- allows people to synthesize coherent isomorphisms. The difference would be a lot clearer if
-- we actually proved coherence instead of just stating it.
class InvolutiveCoherence (X Y : C) where
  /-- An involutive structural isomorphism between two objects. -/
  iso : X ≅ Y

/-- Notation for identities up to unitors, associators, skewators, involutors. -/
scoped[CategoryTheory.InvolutiveCategory] notation " ⊗⋆𝟙 " =>
  InvolutiveCoherence.iso -- type as \ot\star\b1

/-- Construct an isomorphism between two objects in an involutive category
out of unitors, associators, skewators, and involutors. -/
abbrev involutiveIso (X Y : C) [InvolutiveCoherence X Y] : X ≅ Y := InvolutiveCoherence.iso

/-- Compose two morphisms in an involutive category,
inserting unitors, associators, skewators, and involutors between as necessary. -/
def involutiveComp {W X Y Z : C} [InvolutiveCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
  f ≫ ⊗⋆𝟙.hom ≫ g

@[inherit_doc involutiveComp]
scoped[CategoryTheory.InvolutiveCategory] infixr:80 " ⊗⋆≫ " =>
  involutiveComp -- type as \ot \gg

/-- Compose two isomorphisms in an involutive category,
inserting unitors and associators between as necessary. -/
def involutiveIsoComp {W X Y Z : C} [InvolutiveCoherence X Y] (f : W ≅ X) (g : Y ≅ Z) : W ≅ Z :=
  f ≪≫ ⊗⋆𝟙 ≪≫ g

@[inherit_doc involutiveIsoComp]
scoped[CategoryTheory.InvolutiveCategory] infixr:80 " ≪⊗⋆≫ " =>
  involutiveIsoComp -- type as \ll \ot \gg

namespace InvolutiveCoherence

variable [MonoidalCategory C] [InvolutiveCategory C]

@[simps]
instance refl (X : C) : InvolutiveCoherence X X := ⟨Iso.refl _⟩

@[simps]
instance whiskerLeft (X Y Z : C) [InvolutiveCoherence Y Z] :
    InvolutiveCoherence (X ⊗ Y) (X ⊗ Z) :=
  ⟨whiskerLeftIso X ⊗⋆𝟙⟩

@[simps]
instance whiskerRight (X Y Z : C) [InvolutiveCoherence X Y] :
    InvolutiveCoherence (X ⊗ Z) (Y ⊗ Z) :=
  ⟨whiskerRightIso ⊗⋆𝟙 Z⟩

@[simps]
instance star (X Y : C) [InvolutiveCoherence X Y] :
    InvolutiveCoherence X⋆ Y⋆ :=
  ⟨starIso ⊗⋆𝟙⟩

@[simps]
instance tensor_right (X Y : C) [InvolutiveCoherence (𝟙_ C) Y] :
    InvolutiveCoherence X (X ⊗ Y) :=
  ⟨(ρ_ X).symm ≪≫ (whiskerLeftIso X ⊗⋆𝟙)⟩

@[simps]
instance tensor_right' (X Y : C) [InvolutiveCoherence Y (𝟙_ C)] :
    InvolutiveCoherence (X ⊗ Y) X :=
  ⟨whiskerLeftIso X ⊗⋆𝟙 ≪≫ (ρ_ X)⟩

@[simps]
instance left (X Y : C) [InvolutiveCoherence X Y] :
    InvolutiveCoherence (𝟙_ C ⊗ X) Y :=
  ⟨λ_ X ≪≫ ⊗⋆𝟙⟩

@[simps]
instance left' (X Y : C) [InvolutiveCoherence X Y] :
    InvolutiveCoherence X (𝟙_ C ⊗ Y) :=
  ⟨⊗⋆𝟙 ≪≫ (λ_ Y).symm⟩

@[simps]
instance right (X Y : C) [InvolutiveCoherence X Y] :
    InvolutiveCoherence (X ⊗ 𝟙_ C) Y :=
  ⟨ρ_ X ≪≫ ⊗⋆𝟙⟩

@[simps]
instance right' (X Y : C) [InvolutiveCoherence X Y] :
    InvolutiveCoherence X (Y ⊗ 𝟙_ C) :=
  ⟨⊗⋆𝟙 ≪≫ (ρ_ Y).symm⟩

@[simps]
instance assoc (X Y Z W : C) [InvolutiveCoherence (X ⊗ (Y ⊗ Z)) W] :
    InvolutiveCoherence ((X ⊗ Y) ⊗ Z) W :=
  ⟨α_ X Y Z ≪≫ ⊗⋆𝟙⟩

@[simps]
instance assoc' (W X Y Z : C) [InvolutiveCoherence W (X ⊗ (Y ⊗ Z))] :
    InvolutiveCoherence W ((X ⊗ Y) ⊗ Z) :=
  ⟨⊗⋆𝟙 ≪≫ (α_ X Y Z).symm⟩

-- TODO Nat believes these are complete, but isn't entirely sure

@[simps]
instance skew (W X Y : C) [InvolutiveCoherence (Y ⊗ X)⋆ W] :
    InvolutiveCoherence (X⋆ ⊗ Y⋆) W :=
  ⟨(χ_ X Y ) ≪≫ ⊗⋆𝟙⟩

@[simps]
instance skew' (W X Y : C) [InvolutiveCoherence W (Y ⊗ X)⋆] :
    InvolutiveCoherence W (X⋆ ⊗ Y⋆) :=
  ⟨⊗⋆𝟙 ≪≫ (χ_ X Y).symm⟩

@[simps]
instance involute (W X : C) [InvolutiveCoherence X W] :
    InvolutiveCoherence X⋆⋆ W :=
  ⟨(e_ X) ≪≫ ⊗⋆𝟙⟩

@[simps]
instance involute' (W X : C) [InvolutiveCoherence W X] :
    InvolutiveCoherence W X⋆⋆ :=
  ⟨⊗⋆𝟙 ≪≫ (e_ X).symm⟩

end InvolutiveCoherence

@[simp] lemma involutiveComp_refl {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ⊗⋆≫ g = f ≫ g := by
  simp [involutiveComp]

end CategoryTheory
