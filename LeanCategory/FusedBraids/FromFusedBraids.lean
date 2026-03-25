import Mathlib
import LeanCategory.FusedBraids.Instance
import LeanCategory.FreeTwisted.Functor

namespace CategoryTheory.FusedBraids

open FreeTwistedCategory
open FreeTwistedCategoryQuiver

variable {C : Type u} [Quiver.{v} (T C)]

open CategoryTheory MonoidalCategory InvolutiveCategory TwistedCategory

namespace Hom

/--
A helper function for twisting a box `s` times
-/
def boxTwist {X Y : T C} (s : ℕ) (x : X ⟶ Y) : (FreeTwistedCategoryQuiver.mk (X^⋆s) ⟶ ⟨Y^⋆s⟩) :=
  match s with
  | 0 => ⟦.of <| x⟧
  | s + 1 => 
    (ς_ _).hom ≫
    (boxTwist s x) ≫
    (ς_ _).inv

lemma boxTwist_succ {X Y : T C} {x : X ⟶ Y} :
    boxTwist (s + 1) x = (ς_ _).hom ≫ (boxTwist s x) ≫ (ς_ _).inv :=
  rfl

/--
Auxiliary function for premorphisms, turning fused braids premorphisms into
morphisms into the free twisted category with a quiver
-/
@[simp]
def fromFusedBraids {X Y : FB C} : (X ⟶fb Y) → ((FreeTwistedCategoryQuiver.mk X.as) ⟶ ⟨Y.as⟩)
  | .braid f => embed.map f
  | .comp f g => (fromFusedBraids f) ≫ (fromFusedBraids g)
  | .layer ⟨L, X, Y, s, x, R⟩ => _ ◁ (boxTwist s x) ▷ _

end Hom

open FreeTwistedCategory

open Hom
open TwistedCategory

/--
Tactic for stripping off the common left whiskers in a morphism equality,
ignoring all of them
-/
macro "strip_left" : tactic =>
  `(tactic|
    ((repeat1 (first
      | rw [← MonoidalCategory.whiskerLeft_comp_assoc]
      | rw [← MonoidalCategory.whiskerLeft_comp]
      | fail "Nothing to do!"
    )); apply congrArg; simp)
  )

/--
Tactic for maximally grouping the right whiskers in a morphism
-/
macro "extract_right" : tactic =>
  `(tactic|
    (repeat1 (first
      | rw [← MonoidalCategory.comp_whiskerRight_assoc]
      | rw [← MonoidalCategory.comp_whiskerRight]
      | fail "Nothing to do!"
    ))
  )

set_option maxHeartbeats 1000000 in -- the simp_all takes a lot of work
/--
Semantics functor for fused braids, converting fused braids into
morphisms in the free twisted category with a quiver
-/
def fromFusedBraids : (FB C) ⥤ (TQ C) where
  obj X := ⟨X.as⟩
  map := _root_.Quotient.lift Hom.fromFusedBraids <| by
    rintro f g h
    induction h <;> simp_all -- 10 goals. 2 (swap, layer) are nontrivial
    case swap L X₁ Y₁ s₁ x₁ M s₂ X₂ R Y₂ x₂ =>
      simp [involutiveComp]
      -- manualy swap the layers by working them through the associators:
      repeat1 rw [← MonoidalCategory.whiskerLeft_comp_assoc]
      repeat1 rw [Category.assoc]
      rw [MonoidalCategory.associator_naturality_left_assoc]
      rw [MonoidalCategory.associator_naturality_left_assoc]
      rw [MonoidalCategory.associator_inv_naturality_middle_assoc]
      rw [← MonoidalCategory.whisker_exchange]
      simp
      -- it's moved! The layers are in the same positions.
      -- b/c monoidal categories are thin, the stuff between
      -- the layers must be the same.
      inv_coherence
    case layer X Y l₁ l₂ x =>
      clear f g
      induction x <;> simp_all
      any_goals simp [involutiveComp]
      case freeLeft L₁ L₂ X Y s x R l =>
        rw [← whisker_assoc_assoc]
        extract_right
        repeat rw [Category.assoc]
        rw [MonoidalCategory.whisker_exchange _ _]
        simp
      case freeRight R₁ R₂ L X Y s x r =>
        strip_left
        rw [← MonoidalCategory.whisker_exchange _ _]
        simp
      case strand_box_hom =>
        repeat1 rw [← Category.assoc]
        apply congrArg (· ≫ _)
        simp
        strip_left
        extract_right
        repeat rw [← tensorHom_id]
        rw [← braid_naturality]
        simp
      case box_strand_inv =>
        repeat1 rw [← Category.assoc]
        apply congrArg (· ≫ _)
        simp
        strip_left
        extract_right
        repeat rw [← tensorHom_id]
        rw [← braid_inv_naturality]
        simp
      case box_strand_hom =>
        strip_left
        repeat1 rw [← Category.assoc]
        apply congrArg (· ≫ _)
        simp
        rw [associator_inv_naturality_middle_assoc]
        rw [Iso.hom_inv_id_assoc]
        extract_right
        apply congrArg
        simp
        rw [← id_tensorHom]
        rw [braid_inv_naturality]
        simp
      case strand_box_inv =>
        strip_left
        repeat1 rw [← Category.assoc]
        apply congrArg (· ≫ _)
        simp
        rw [associator_inv_naturality_middle_assoc]
        rw [Iso.hom_inv_id_assoc]
        extract_right
        apply congrArg
        simp
        rw [← id_tensorHom]
        rw [braid_naturality]
        simp
      case twist_hom =>
        rw [Hom.boxTwist_succ]
        simp
      case twist_inv =>
        rw [Hom.boxTwist_succ]
        simp
        repeat1 rw [← MonoidalCategory.whiskerLeft_comp_assoc]
        repeat1 rw [← MonoidalCategory.whiskerLeft_comp]
        apply congrArg
        repeat1 rw [← MonoidalCategory.comp_whiskerRight]
        simp
      case ε_hom =>
        simp [Hom.boxTwist_succ]
        strip_left
        extract_right
        apply congrArg
        simp
        rw [twist_inv_naturality_assoc]
        simp [repeat_star_succ]
        rw [twist_inv_naturality]
        simp
      case ε_inv =>
        simp [Hom.boxTwist_succ]
        strip_left
        extract_right
        apply congrArg
        simp
        rw [twist_inv_naturality_assoc]
        simp [repeat_star_succ]
        rw [twist_inv_naturality_assoc]
        simp
  map_comp := by
    rintro _ _ _ ⟨f⟩ ⟨g⟩
    rfl
  map_id := by
    rintro _
    rfl

end CategoryTheory.FusedBraids

