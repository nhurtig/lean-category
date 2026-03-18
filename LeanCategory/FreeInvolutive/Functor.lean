import LeanCategory.FreeInvolutive.Instance
import LeanCategory.FreeTwisted.Instance

namespace CategoryTheory.FreeInvolutiveCategory

variable {C : Type u}

variable {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [InvolutiveCategory D] (m : C → D)

open MonoidalCategory
open InvolutiveCategory

open Hom

/--
Auxiliary definition for the projection functor: maps premorphisms in `I C`
morphisms in `D`.
-/
@[simp]
def projectMapAux : ∀ {X Y : I C}, (X ⟶i Y) → (X.projectObj m ⟶ Y.projectObj m)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, l_hom _ => (λ_ _).hom
  | _, _, l_inv _ => (λ_ _).inv
  | _, _, ρ_hom _ => (ρ_ _).hom
  | _, _, ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.comp f g => projectMapAux f ≫ projectMapAux g
  | _, _, Hom.whiskerLeft X p => X.projectObj m ◁ projectMapAux p
  | _, _, Hom.whiskerRight p X => projectMapAux p ▷ X.projectObj m
  | _, _, Hom.tensor f g => projectMapAux f ⊗ₘ projectMapAux g
  | _, _, Hom.star f => (projectMapAux f)⋆
  | _, _, χ_hom _ _ => (χ_ _ _).hom
  | _, _, χ_inv _ _ => (χ_ _ _).inv
  | _, _, ε_hom _ => (e_ _).hom
  | _, _, ε_inv _ => (e_ _).inv

/--
For any premorphism `f` in `I C`, the morphism `projectMapAux m f` is
an involutive coherence, as defined in `InvolutiveCategory`.
-/
lemma projectMapAux_InvolutiveCoherence : ∀ {X Y : I C} (f : X ⟶i Y),
    InvolutiveCoherence (projectMapAux m f) := by
  intro X Y f
  induction f <;> simp_all
  all_goals constructor <;> assumption

/--
The morphism map of the projection functor from `I C` to `D`.
-/
@[simp]
def projectMap {X Y : I C} : (X ⟶ Y) → (X.projectObj m ⟶ Y.projectObj m) :=
  _root_.Quotient.lift (projectMapAux m) <| by
    intros
    apply InvolutiveCategory.coherence <;> apply projectMapAux_InvolutiveCoherence

/--
Given a function `C → D`, we get a functor `I C ⥤ D` by projecting the free
involutive category onto the involutive morphisms in `D`, collapsing
the object structure in `T C` using `D`'s object structure.
-/
def project : I C ⥤ D where
  obj := projectObj m
  map := projectMap m
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

variable {D : Type u'} (m : C → D)

/--
Project a free involutive category on `C` to a free involutive category on `D`
using a function `C → D`.
-/
def projectFree : I C ⥤ I D := project (fun c ↦ (of (m c)))

open FreeTwistedCategory

/--
The functor witnessing that the free involutive category on `C` embeds into the
free twisted category on `C`, by just never producing the twist morphism.
-/
def embed : I C ⥤ T C := project FreeTwistedCategory.of

end CategoryTheory.FreeInvolutiveCategory

