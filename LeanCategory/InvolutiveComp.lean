import Mathlib
import LeanCategory.Basic

universe u v

open CategoryTheory MonoidalCategory InvolutiveCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open scoped MonoidalCategory

/--
An involutive coherence *should* be made up of compositions/stars/tensors/whiskers
of the coherence isomorphisms. There's nothing here that enforces that, but we
only define instances for those isomorphisms. We use this class to use Lean's
typeclass inference to automatically figure out if there's a coherent isomorphism between
any two objects, automatically generating a representative of that isomorphism if so.
If someone were to make more instances, that would break the property and it'd cause
mayhem... so don't do that.
-/
class InvolutiveCoherence (X Y : C) where
  iso : X ≅ Y

/--
The isomorphism between two objects, if it exists.
-/
scoped[CategoryTheory.InvolutiveCategory] notation " ⊗⋆𝟙 " =>
  InvolutiveCoherence.iso

abbrev involutiveIso (X Y : C) [InvolutiveCoherence X Y] : X ≅ Y := InvolutiveCoherence.iso

/--
Composition of morphisms, up to involutive coherence. Incredibly useful -- it
"fills in" by rewriting X to Y.
-/
def involutiveComp {W X Y Z : C} [InvolutiveCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
  f ≫ ⊗⋆𝟙.hom ≫ g

@[inherit_doc involutiveComp]
scoped[CategoryTheory.InvolutiveCategory] infixr:80 " ⊗⋆≫ " =>
  involutiveComp

/--
Composition of isomorphisms, up to involutive coherence. Incredibly useful -- it
"fills in" by rewriting X to Y.
-/
def involutiveIsoComp {W X Y Z : C} [InvolutiveCoherence X Y] (f : W ≅ X) (g : Y ≅ Z) : W ≅ Z :=
  f ≪≫ ⊗⋆𝟙 ≪≫ g

@[inherit_doc involutiveIsoComp]
scoped[CategoryTheory.InvolutiveCategory] infixr:80 " ≪⊗⋆≫ " =>
  involutiveIsoComp

namespace InvolutiveCoherence

variable [MonoidalCategory C] [InvolutiveCategory C]

-- Instances for InvolutiveCoherence. They're constructed
-- very carefully to help the synthesizer make the right choices
-- to quickly figure about whether an involutive coherence exists,
-- in a way that reminds Nat of sequent calculus (as opposed to
-- natural deduction)

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

@[simps]
instance skew (W X Y : C) [InvolutiveCoherence (X⋆ ⊗ Y⋆) W] :
    InvolutiveCoherence (Y ⊗ X)⋆ W :=
  ⟨(χ_ X Y ).symm ≪≫ ⊗⋆𝟙⟩

@[simps]
instance skew' (W X Y : C) [InvolutiveCoherence W (X⋆ ⊗ Y⋆)] :
    InvolutiveCoherence W (Y ⊗ X)⋆ :=
  ⟨⊗⋆𝟙 ≪≫ (χ_ X Y)⟩

@[simps]
instance involute (W X : C) [InvolutiveCoherence X W] :
    InvolutiveCoherence X⋆⋆ W :=
  ⟨(e_ X) ≪≫ ⊗⋆𝟙⟩

@[simps]
instance involute' (W X : C) [InvolutiveCoherence W X] :
    InvolutiveCoherence W X⋆⋆ :=
  ⟨⊗⋆𝟙 ≪≫ (e_ X).symm⟩

@[simp]
instance tensor_skew_left (W X Y Z : C) [InvolutiveCoherence ((X⋆ ⊗ Y⋆) ⊗ Z) W] :
    InvolutiveCoherence ((Y ⊗ X)⋆ ⊗ Z) W :=
  ⟨(whiskerRightIso (χ_ X Y ).symm Z) ≪≫ ⊗⋆𝟙⟩

@[simp]
instance tensor_skew_left' (W X Y Z : C) [InvolutiveCoherence W ((X⋆ ⊗ Y⋆) ⊗ Z)] :
    InvolutiveCoherence W ((Y ⊗ X)⋆ ⊗ Z) :=
  ⟨⊗⋆𝟙 ≪≫ (whiskerRightIso (χ_ X Y ) Z) ⟩

end InvolutiveCoherence

@[simp] lemma involutiveComp_refl {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ⊗⋆≫ g = f ≫ g := by
  simp [involutiveComp]

@[simp] lemma involuteComp_assoc {W X Y Z : C} [InvolutiveCoherence X X']
  (f : W ⟶ X) (g : X' ⟶ Y) (h : Y ⟶ Z) :
    (f ⊗⋆≫ g) ≫ h = f ⊗⋆≫ (g ≫ h) := by
  simp [involutiveComp]

end CategoryTheory

