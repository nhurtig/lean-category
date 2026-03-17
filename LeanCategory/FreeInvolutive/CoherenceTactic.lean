import Mathlib
import LeanCategory.FreeInvolutive.Instance
import LeanCategory.FreeInvolutive.Functor
import LeanCategory.InvolutiveComp

universe u v

open CategoryTheory FreeInvolutiveCategory

namespace CategoryTheory.InvolutiveCategory.Coherence

variable {C : Type u} [Category.{v} C]
open scoped MonoidalCategory InvolutiveCategory

noncomputable section lifting

variable [MonoidalCategory C] [InvolutiveCategory C]

class LiftObj (X : C) where
  protected lift : I C

instance LiftObj_unit : LiftObj (𝟙_ C) := ⟨unit⟩

instance LiftObj_tensor (X Y : C) [LiftObj X] [LiftObj Y] : LiftObj (X ⊗ Y) where
  lift := LiftObj.lift X ⊗ LiftObj.lift Y

instance LiftObj_star (X : C) [LiftObj X] : LiftObj X⋆ where
  lift := (LiftObj.lift X)⋆

instance (priority := 100) LiftObj_of (X : C) : LiftObj X := ⟨of X⟩

class LiftHom {X Y : C} [LiftObj X] [LiftObj Y] (f : X ⟶ Y) where
  protected lift : LiftObj.lift X ⟶ LiftObj.lift Y

instance LiftHom_id (X : C) [LiftObj X] : LiftHom (𝟙 X) := ⟨𝟙 _⟩

instance LiftHom_left_unitor_hom (X : C) [LiftObj X] : LiftHom (λ_ X).hom where
  lift := (λ_ (LiftObj.lift X)).hom

instance LiftHom_left_unitor_inv (X : C) [LiftObj X] : LiftHom (λ_ X).inv where
  lift := (λ_ (LiftObj.lift X)).inv

instance LiftHom_right_unitor_hom (X : C) [LiftObj X] : LiftHom (ρ_ X).hom where
  lift := (ρ_ (LiftObj.lift X)).hom

instance LiftHom_right_unitor_inv (X : C) [LiftObj X] : LiftHom (ρ_ X).inv where
  lift := (ρ_ (LiftObj.lift X)).inv

instance LiftHom_associator_hom (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).hom where
  lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).hom

instance LiftHom_associator_inv (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).inv where
  lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).inv

instance LiftHom_skewator_hom (X Y : C) [LiftObj X] [LiftObj Y] : LiftHom (χ_ X Y).hom where
  lift := (χ_ (LiftObj.lift X) (LiftObj.lift Y)).hom

instance LiftHom_skewator_inv (X Y : C) [LiftObj X] [LiftObj Y] : LiftHom (χ_ X Y).inv where
  lift := (χ_ (LiftObj.lift X) (LiftObj.lift Y)).inv

instance LiftHom_involutor_hom (X : C) [LiftObj X] : LiftHom (e_ X).hom where
  lift := (e_ (LiftObj.lift X)).hom

instance LiftHom_involutor_inv (X : C) [LiftObj X] : LiftHom (e_ X).inv where
  lift := (e_ (LiftObj.lift X)).inv

instance LiftHom_comp {X Y Z : C} [LiftObj X] [LiftObj Y] [LiftObj Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [LiftHom f] [LiftHom g] : LiftHom (f ≫ g) where
  lift := LiftHom.lift f ≫ LiftHom.lift g

instance liftHom_WhiskerLeft (X : C) [LiftObj X] {Y Z : C} [LiftObj Y] [LiftObj Z]
    (f : Y ⟶ Z) [LiftHom f] : LiftHom (X ◁ f) where
  lift := LiftObj.lift X ◁ LiftHom.lift f

instance liftHom_WhiskerRight {X Y : C} (f : X ⟶ Y) [LiftObj X] [LiftObj Y] [LiftHom f]
    {Z : C} [LiftObj Z] : LiftHom (f ▷ Z) where
  lift := LiftHom.lift f ▷ LiftObj.lift Z

instance LiftHom_tensor {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z]
    (f : W ⟶ X) (g : Y ⟶ Z) [LiftHom f] [LiftHom g] : LiftHom (f ⊗ₘ g) where
  lift := LiftHom.lift f ⊗ₘ LiftHom.lift g

instance liftHom_star {X Y : C} (f : X ⟶ Y) [LiftObj X] [LiftObj Y] [LiftHom f]
    : LiftHom f⋆ where
  lift := (LiftHom.lift f)⋆

end lifting

open Lean Meta Elab Tactic

@[nolint unusedArguments]
lemma assoc_liftHom {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y]
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) [LiftHom f] [LiftHom g] :
    f ≫ (g ≫ h) = (f ≫ g) ≫ h :=
  (Category.assoc _ _ _).symm

elab (name := liftable_prefixes) "liftable_prefixes" : tactic => do
  withOptions (fun opts => synthInstance.maxSize.set opts
    (max 256 (synthInstance.maxSize.get opts))) do
  evalTactic (← `(tactic|
    (simp -failIfUnchanged only
      [involutiveComp, monoidalComp, bicategoricalComp, Category.assoc, BicategoricalCoherence.iso,
      MonoidalCoherence.iso, InvolutiveCoherence.iso, Iso.trans, Iso.symm, Iso.refl,
      MonoidalCategory.whiskerRightIso, MonoidalCategory.whiskerLeftIso, InvolutiveCategory.starIso,
      Bicategory.whiskerRightIso, Bicategory.whiskerLeftIso]) <;>
    (apply (cancel_epi (𝟙 _)).1 <;> try infer_instance) <;>
    (simp -failIfUnchanged only
      [assoc_liftHom, Mathlib.Tactic.BicategoryCoherence.assoc_liftHom₂])))

macro "inv_coherence_step" : tactic =>
  `(tactic|
    first
      | rfl -- handles just impure, identical morphisms
      | apply congrArg₂ _ rfl -- starting w/ impure, identical morphisms
       -- edge case: f = f ≫ pure-coherent-ends-up-being-id:
      | (apply Eq.trans ((Category.comp_id _).symm) ; apply congrArg₂ _ rfl)
      | liftable_prefixes; apply congrArg₂ _ (by pure_inv_coherence) -- starting w/ pure stuff
      | pure_inv_coherence -- just pure stuff
      | fail "IDK what to do"
  )

macro "inv_coherence" : tactic =>
  `(tactic|
    first
      | simp; done
      | (try simp); repeat1 inv_coherence_step
  )

end Coherence

end CategoryTheory.InvolutiveCategory

