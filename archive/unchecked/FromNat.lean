import Mathlib
import LeanCategory.NatDefinition
import LeanCategory.FreeEggerFunctorEmbed

namespace NatDefinition

-- TODO at some point actually instantiate the stitches
variable {V : Type u}
  --[stitches : Quiver.{v} (F V)]
  [otherStitches : Quiver (FQ V)]
/- variable {V : Type u} {Q : Type u'} -/
/-     [stitches : StarQuiver.{v} V] [otherStitches : Quiver.{v'} (F Q)] -/
/-   {vq : V ≃ Q} {stitchEquiv : (X Y : F V) → (stitches.Hom X Y ≃ otherStitches.Hom (X.map vq) (Y.map vq))} -/

/-
@[simp]
def FtoFQ' : F V → FQ V
  | .of v => .of v
  | .unit => .unit
  | .tensor X Y => .tensor (FtoFQ' X) (FtoFQ' Y)
  | .star X => .star (FtoFQ' X)

@[simp]
def FtoFQ'' : F V → FQ V :=
  CategoryTheory.FreeTwistedCategory.projectObj (.of ·)

variable {stitchIso : (X Y : F V) → stitches.Hom X Y ≃ otherStitches.Hom (FtoFQ'' X) (FtoFQ'' Y)}

@[simp]
def FQtoF' : FQ V → F V
  | .of v => .of v
  | .unit => .unit
  | .tensor X Y => .tensor (FQtoF' X) (FQtoF' Y)
  | .star X => .star (FQtoF' X)

def FtoFQ : F V ≃ FQ V where
  toFun := FtoFQ'
  invFun := FQtoF'
  left_inv X := by induction X <;> simp_all
  right_inv X := by induction X <;> simp_all
-/

open CategoryTheory
open MonoidalCategory



open FreeTwistedCategory.Embed
#check FtoFQ

/- @[simp] -/
/- instance quiverFQ : Quiver (FQ V) where -/
/-   Hom X Y := FQtoF' X ⟶ FQtoF' Y -/
/- @[simp] -/
/- instance quiverFN : Quiver (FN V) where -/
/-   Hom X Y := FtoFQ (FNtoF X) ⟶ FtoFQ (FNtoF Y) -/
@[simp]
instance quiverF : Quiver (F V) where
  Hom X Y := FtoFQ X ⟶ FtoFQ Y

-- our two categories of most interest:
#synth Category (F V)
#check natCategory
#synth Category (FQ V)
-- and the supporting category of just twists:
#check FreeTwistedCategory.categoryFreeTwistedCategory
/- attribute [-instance] natCategory -/
/- #synth Category (F V) -/
/- attribute [instance] natCategory -/

#synth Quiver (F V)

/- attribute [-instance] natCategory -/
#check embed

/- #synth Category.{u, u} (F V) -/
/- #check  -/
/- #synth Category (FQ V) -/

/- instance justBraids : Category.{u, u} (F V) := @FreeTwistedCategory.categoryFreeTwistedCategory V -/
/- def embed := @CategoryTheory.FreeTwistedCategory.project -/
/-     V (F V) (FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver) _ _ (.of ·) _ -/
/- def embed := @CategoryTheory.FreeTwistedCategory.project V (F V) _ _ _ (.of ·) _ -/
#check embed.obj
/- @[simp] -/
/- lemma embed_obj_tensor {X Y : F V} : embed.obj (X ⊗ Y) = (embed.obj X) ⊗ (embed.obj Y) := rfl -/

-- from Nat's definition to the regular one (F V to FQ V)
namespace Hom

#check (@FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver V _).Hom
set_option quotPrecheck false in
infixr:10 " ⟶Q " => (@FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver V _).Hom

/- ```lean -/
/- CategoryTheory.FreeTwistedCategory.project.{u', v', u_1} {C : Type u_1} {D : Type u'} [Category.{v', u'} D] -/
/-   [MonoidalCategory D] [InvolutiveCategory D] (m : C → D) [TwistedCategory D] : F C ⥤ D -/
/- ``` -/
/- *** -/

-- the justBraids stuff breaks the notation, so we put this lemma after it
/- @[simp] -/
/- lemma FtoFQ_tensor {X Y : F V} : FtoFQ (X ⊗ Y) = (FtoFQ X) ⊗ (FtoFQ Y) := rfl -/

/- def embed : F V ⥤ FQ V := CategoryTheory.FreeTwistedCategory.project sorry -/
/- @[simp] -/
/- lemma embed_eq_FtoFQ : (@embed V stitches).obj = FtoFQ := by -/
/-   ext X -/
/-   unfold embed -/
/-   unfold FreeTwistedCategory.project -/
/-   induction X <;> simp_all <;> rfl -/

#check embed.obj
open MonoidalCategory
/- #synth (Category (FQ V)) -/

/- @[simp] -/
/- lemma myinvertthingy : FQtoF' ((@embed V _).obj X) = X := by -/
/-   sorry -/

@[simp]
lemma Nat.repeat_succ : Nat.repeat f (n + 1) x = f (Nat.repeat f n x) := rfl

#check InvolutiveCategoryStruct
open TwistedCategory
#check TwistedCategoryStruct
#synth TwistedCategoryStruct (FQ V)
#synth (Quiver <| FQ V)

-- TODO put this into NatDefinition.lean?
@[simp]
def sizeOf {X Y : F V} : Hom X Y → ℕ
  | layer ⟨_, _, _, s, _, _⟩ => s
  | id _ => 0
  | braid f => 0
  | comp f g => f.sizeOf + g.sizeOf + 1

#synth Quiver (F V)
#check @Hom
/- def embed := -/
/- (@CategoryTheory.FreeTwistedCategory.project V (F V) (FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver) _ _ (.of ·) _) -/

/- attribute [-instance] FreeTwistedCategory.categoryFreeTwistedCategory -/
/- attribute [-instance] natCategory -/
/- attribute [-instance] natCategory -/
#check preHom
#synth Quiver (F V)
def fromNatLayerHelper (D C : F V) (s : ℕ) (x : D ⟶ C) :
    (FtoFQ (s.repeat .star D) ⟶Q
       FtoFQ (s.repeat .star C)) := match s with
  | 0 => ⟦.of <| x⟧
  | s + 1 => 
    (ς_ _).hom ≫
    (fromNatLayerHelper D C s x) ≫
    (ς_ _).inv

lemma fromNatLayerHelper_succ {D C : F V} {x : D ⟶ C} :
    fromNatLayerHelper D C (s + 1) x = (ς_ _).hom ≫ (fromNatLayerHelper D C s x) ≫ (ς_ _).inv :=
  rfl

attribute [-instance] natCategory
@[simp]
/- def fromNat {X Y : F V} : Hom X Y → (@FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver V _).Hom ((@CategoryTheory.FreeTwistedCategory.project V (F V) (FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver) _ _ (.of ·) _).obj X) ((@CategoryTheory.FreeTwistedCategory.project V (F V) (FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver) _ _ (.of ·) _).obj Y) -/
/- def fromNat {X Y : F V} : Hom X Y → (@FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver V _).Hom ((@CategoryTheory.FreeTwistedCategory.project V (F V) (FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver) _ _ (.of ·) _).obj X) ((@CategoryTheory.FreeTwistedCategory.project V (F V) (FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver) _ _ (.of ·) _).obj Y) -/
def fromNat {X Y : F V} : Hom X Y → ((embed.obj X) ⟶Q (embed.obj Y))
  /- | braid f => (@embed_eq_FtoFQ V stitches) ▸ embed.map f -- gotta embed w/o quiver into w/ quiver -/
  | braid f => embed.map f -- gotta embed w/o quiver into w/ quiver
  | comp f g => FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver.comp f.fromNat g.fromNat
  | id X => 𝟙 _
  /- | layer ⟨L, D, C, 0, x, R⟩ => by simp; unfold embed; simp; unfold quiverF at x; simp at x; unfold Nat.repeat; exact _ ◁ (⟦.of <| x⟧) ▷ _ -/
  /- | layer ⟨L, D, C, 0, x, R⟩ => _ ◁ (⟦.of <| x⟧) ▷ _ -/
  | layer ⟨L, D, C, s, x, R⟩ => _ ◁ (fromNatLayerHelper D C s x) ▷ _
attribute [instance] natCategory
  /- | layer ⟨L, D, C, s+1, x, R⟩ => (_ ◁ ((@FreeTwistedCategoryQuiver.freeTwistedCategoryQuiver V _).toTwistedCategoryStruct.twist _).hom ▷ _) ≫ -/
  /-       (fromNat (layer ⟨L, D, C, s, x, R⟩)) ≫ -/
  /-       (_ ◁ ((@FreeTwistedCategoryQuiver.freeTwistedCategoryQuiver V _).toTwistedCategoryStruct.twist _).inv ▷ _) -/
  /- | layer ⟨L, D, C, s+1, x, R⟩ => (_ ◁ ((@FreeTwistedCategoryQuiver.freeTwistedCategoryQuiver V _).toTwistedCategoryStruct.twist _).hom ▷ _) ≫ -/
  /-       (fromNat (layer ⟨L, D, C, s, x, R⟩)) ≫ -/
  /-       (_ ◁ ((@FreeTwistedCategoryQuiver.freeTwistedCategoryQuiver V _).toTwistedCategoryStruct.twist _).inv ▷ _) -/
/- termination_by f => f.sizeOf -/
/- decreasing_by -/
/-   all_goals simp <;> omega -/
      
  /- | layer ⟨L, D, C, s+1, x, R⟩ => by -/
  /-     have blah := fromNat (layer ⟨L, D, C, s, x, R⟩) -/
  /-     unfold embed at blah ⊢; simp at blah ⊢; unfold quiverF at x; simp at x -/
  /-     refine (_ ◁ ?_ ▷ _) ≫ blah ≫ (_ ◁ ?_ ▷ _) <;> clear blah -/

end Hom

#synth Category (F V)
/- attribute [-instance] Hom.justBraids -- don't use it anymore -/
#synth Category (F V)

open FreeTwistedCategory
#check mk_α_inv


/- @[simp] -/
/- lemma projectObj_of_function (X : F V) : -/
/-     projectObj (fun x ↦ FreeTwistedCategoryQuiver.of x) X = FtoFQ X := by -/
  /- induction X <;> unfold FtoFQ <;> simp_all <;> rfl -/

open Hom
open TwistedCategory

#check FreeTwistedCategory.categoryFreeTwistedCategory
#synth Category (F V)
#synth Category (FQ V)
/- attribute [instance] natCategory -/
/- #synth Category (F V) -/
/- #synth Category (FQ V) -/

#check Nat.repeat
#check Nat.iterate

scoped notation:max n " =>⋆" => Nat.repeat FreeTwistedCategoryNat.star n
scoped notation:max "[[" X "]]" => FtoFQ (X)

macro "strip_left" : tactic =>
  `(tactic|
    ((repeat1 (first
      | rw [← whiskerLeft_comp_assoc]
      | rw [← whiskerLeft_comp]
      | fail "Nothing to do!"
    )); apply congrArg; simp)
  )

macro "extract_right" : tactic =>
  `(tactic|
    (repeat1 (first
      | rw [← comp_whiskerRight_assoc]
      | rw [← comp_whiskerRight]
      | fail "Nothing to do!"
    ))
  )

#check Iso
#check MonoidalCategory
set_option maxHeartbeats 1000000 in -- very large category theory rewrites
instance fromNat : (F V) ⥤ (FQ V) where
  obj X := FtoFQ X
  map := Quotient.lift Hom.fromNat <| by
    rintro f g h
    induction h <;> simp_all -- 10 goals. 2 (swap, layer) are nontrivial
    case swap =>
      strip_left -- ignore the L ◁ ... on every morphism
      -- move the x₁ layer up the word past x₂ on the LHS
      rw [associator_naturality_left_assoc]
      rw [associator_naturality_left_assoc]
      rw [← whisker_exchange_assoc]
      -- it's moved! The layers are in the same positions.
      -- b/c monoidal categories are thin, the stuff between
      -- the layers must be the same.
      simp
    case layer X Y l₁ l₂ x =>
      clear f g
      induction x <;> simp_all


        /-
        -- TODO: below proof is now deprecated.
        -- New task: use simp lemmas that embed.map
        -- respects whisker, congrArg each whisker out,
        -- embed.map respects twist.
        -- DONE: Use a simp lemma to simplifty fromNatLayerHelper on s successors
        -- I don't believe we need to apply twist naturality then cancel the twists,
        -- as both sides are hom ≫ sorry ≫ inv.

        -- remove the surrounding L and R
        repeat rw [← whiskerLeft_comp_assoc _ _ _]
        rw [← whiskerLeft_comp _ _ _]
        apply congrArg
        repeat rw [← comp_whiskerRight_assoc _ _ _]
        rw [← comp_whiskerRight _ _ _]
        rw [← comp_whiskerRight _ _ _]
        apply congrArg (· ▷ _)

        -- use naturality of twist
        unfold project
        rw [← mk_ς_hom]
        rw [← mk_ς_inv]
        simp
        rw [TwistedCategory.twist_inv_naturality]
        simp

        #check cast
        rw [← mk_star (FreeTwistedCategoryQuiver.Hom.of (cast _ s))]
        sorry
        -/
      case freeLeft L₁ L₂ X Y s x R l =>
        rw [← whisker_assoc_assoc]
        extract_right
        repeat rw [Category.assoc]
        rw [whisker_exchange _ _]
        unfold embed
        simp
      case freeRight R₁ R₂ L X Y s x r =>
        strip_left
        rw [← whisker_exchange _ _]
        unfold embed
        simp
        
        /-
        sorry
        simp only
        have h := associator_naturality_left_assoc (embed.map l) [[s =>⋆ X]] [[R]]]
        simp at hrw
        rw [hrw]
        rw [embed_map_whiskerRight]
        rw [MonoidalCategory.tensorHom_def]
        rw [MonoidalCategory.tensorHom_def']
        -/
        /- unfold project -/

        -- get the l's to meet
        /- repeat rw [Category.assoc] -/
        /- rw [← whisker_exchange_assoc] -/
        /- simp -/
        /- rw [← comp_whiskerRight_assoc] -/

        -- get the r's to meet
        /- rw [← whiskerLeft_comp_assoc _ _ _] -/
        /- rw [← whisker_exchange] -/
        /- rw [← whisker_exchange] -/
        /- rw [whisker_exchange] -/
        /- rw [whiskerLeft_comp_assoc _ _ _] -/

        /- repeat rw [Category.assoc] -/
        /- rw [← whiskerLeft_comp_assoc _ _ _] -/
        /- rw [← whiskerLeft_comp_assoc _ _ _] -/
        /- rw [← whiskerLeft_comp _ _ _] -/
        /- simp -/
        /- simp only [IsIso.hom_inv_id] -/
        /- rw [whiskerLeft_id ((project fun x ↦ FreeTwistedCategoryQuiver.of x).obj L₂) (((project fun x ↦ FreeTwistedCategoryQuiver.of x).obj X ⊗ -/
        /-     (project fun x ↦ FreeTwistedCategoryQuiver.of x).obj R₁))] -/
        /- simp -/
        /- /- rw [Category.id_comp] -/ -/
        /- simp -/

        /- #check Category.comp_id -/
        /- rw [← whisker_exchange_assoc] -/
        /- rw [← whisker_exchange_assoc] -/

        /- rw [← comp_whiskerRight _ _ _] -/
        /- simp? -/

        /- symm -/
        /- rw [← whiskerLeft_comp _ _ _] -/
        /- apply congrArg -/
        /- rw [← id_whiskerRight] -/
        /- rw [← comp_whiskerRight _ _ _] -/
        /- apply congrArg (· ▷ (project fun x ↦ FreeTwistedCategoryQuiver.of x).obj R₁) -/
        /- rw [Category.id_comp] -/

/-
        rw [whiskerLeft_id]

        sorry

        induction l using Quotient.inductionOn
        induction r using Quotient.inductionOn
        simp
        repeat1 rw [← mk_whiskerLeft]
        repeat1 rw [← mk_tensor]
        simp
        rw [MonoidalCategory.tensorHom_def]
        rw [MonoidalCategory.tensorHom_def']
        simp

        sorry
        -/
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
        rw [Hom.fromNatLayerHelper_succ]
        simp
      case twist_inv =>
        rw [Hom.fromNatLayerHelper_succ]
        simp
        repeat1 rw [← whiskerLeft_comp_assoc]
        repeat1 rw [← whiskerLeft_comp]
        apply congrArg
        repeat1 rw [← comp_whiskerRight]
        simp
  map_comp := by
    rintro _ _ _ ⟨f⟩ ⟨g⟩
    rfl
  map_id := by
    rintro _
    rfl

end NatDefinition

