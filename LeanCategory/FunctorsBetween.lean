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
#synth Category (FN V)
#synth Category (FQ V)
-- and the supporting category of just twists:
#synth Category (F V)

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
def sizeOf {X Y : FN V} : Hom X Y → ℕ
  | layer ⟨_, _, _, s, _, _⟩ => s
  | id _ => 0
  | braid f => 0
  | comp f g => f.sizeOf + g.sizeOf + 1

#synth Quiver (FN V)
#check @Hom
/- def embed := -/
/- (@CategoryTheory.FreeTwistedCategory.project V (F V) (FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver) _ _ (.of ·) _) -/

/- attribute [-instance] FreeTwistedCategory.categoryFreeTwistedCategory -/
/- attribute [-instance] natCategory -/
/- attribute [-instance] natCategory -/
#check preHom
#synth Quiver (F V)
def fromNatLayerHelper (D C : FN V) (s : ℕ) (x : (FNtoF D) ⟶ (FNtoF C)) :
    (FtoFQ (FNtoF (s.repeat FreeTwistedCategoryNat.star D)) ⟶Q
       FtoFQ (FNtoF (s.repeat FreeTwistedCategoryNat.star C))) := match s with
  | 0 => ⟦.of <| x⟧
  | s + 1 => 
    ((@FreeTwistedCategoryQuiver.freeTwistedCategoryQuiver V _).toTwistedCategoryStruct.twist _).hom ≫
    (fromNatLayerHelper D C s x) ≫
    ((@FreeTwistedCategoryQuiver.freeTwistedCategoryQuiver V _).toTwistedCategoryStruct.twist _).inv

@[simp]
/- def fromNat {X Y : F V} : Hom X Y → (@FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver V _).Hom ((@CategoryTheory.FreeTwistedCategory.project V (F V) (FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver) _ _ (.of ·) _).obj X) ((@CategoryTheory.FreeTwistedCategory.project V (F V) (FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver) _ _ (.of ·) _).obj Y) -/
/- def fromNat {X Y : F V} : Hom X Y → (@FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver V _).Hom ((@CategoryTheory.FreeTwistedCategory.project V (F V) (FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver) _ _ (.of ·) _).obj X) ((@CategoryTheory.FreeTwistedCategory.project V (F V) (FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver) _ _ (.of ·) _).obj Y) -/

-- TODO we are making the layer thing a helper function, just for the interior

def fromNat {X Y : FN V} : Hom X Y → ((embed.obj (FNtoF X)) ⟶Q (embed.obj (FNtoF Y)))
  /- | braid f => (@embed_eq_FtoFQ V stitches) ▸ embed.map f -- gotta embed w/o quiver into w/ quiver -/
  | braid f => embed.map f -- gotta embed w/o quiver into w/ quiver
  | comp f g => FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver.comp f.fromNat g.fromNat
  | id X => 𝟙 _
  /- | layer ⟨L, D, C, 0, x, R⟩ => by simp; unfold embed; simp; unfold quiverF at x; simp at x; unfold Nat.repeat; exact _ ◁ (⟦.of <| x⟧) ▷ _ -/
  /- | layer ⟨L, D, C, 0, x, R⟩ => _ ◁ (⟦.of <| x⟧) ▷ _ -/
  | layer ⟨L, D, C, s, x, R⟩ => _ ◁ (fromNatLayerHelper D C s x) ▷ _
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
  /-     exact ((@FreeTwistedCategoryQuiver.freeTwistedCategoryQuiver V _).toTwistedCategoryStruct.twist _).hom -/
  /-     exact ((@FreeTwistedCategoryQuiver.freeTwistedCategoryQuiver V _).toTwistedCategoryStruct.twist _).inv -/

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

#synth Category (F V)
#synth Category (FN V)
#synth Category (FQ V)
/- attribute [instance] natCategory -/
/- #synth Category (F V) -/
/- #synth Category (FQ V) -/

instance fromNat : (FN V) ⥤ (FQ V) where
  obj X := embed.obj (FNtoF X)
  map := Quotient.lift Hom.fromNat <| by
    rintro f g h
    induction h
    case layer X Y l₁ l₂ x =>
      simp
      clear f g
      induction x
      case twist_hom L X Y s x R =>
        simp_all
        rw [← Functor.map_inv]
        simp
        -- TODO: below proof is now deprecated.
        -- New task: use simp lemmas that embed.map
        -- respects whisker, congrArg each whisker out,
        -- embed.map respects twist.
        -- Use a simp lemma to simplifty fromNatLayerHelper on s successors
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
      all_goals sorry
      case free L₁ L₂ R₁ R₂ X Y s l r =>
        simp
        unfold embed
        simp
        rw [MonoidalCategory.tensorHom_def]
        rw [MonoidalCategory.tensorHom_def']
        /- unfold project -/

        -- get the l's to meet
        /- repeat rw [Category.assoc] -/
        /- rw [← whisker_exchange_assoc] -/
        /- simp -/
        /- rw [← comp_whiskerRight_assoc] -/

        -- get the r's to meet
        rw [← whiskerLeft_comp_assoc _ _ _]
        rw [← whisker_exchange]
        rw [← whisker_exchange]
        rw [whisker_exchange]
        rw [whiskerLeft_comp_assoc _ _ _]

        repeat rw [Category.assoc]
        rw [← whiskerLeft_comp_assoc _ _ _]
        rw [← whiskerLeft_comp_assoc _ _ _]
        rw [← whiskerLeft_comp _ _ _]
        simp
        /- simp only [IsIso.hom_inv_id] -/
        /- rw [whiskerLeft_id ((project fun x ↦ FreeTwistedCategoryQuiver.of x).obj L₂) (((project fun x ↦ FreeTwistedCategoryQuiver.of x).obj X ⊗ -/
        /-     (project fun x ↦ FreeTwistedCategoryQuiver.of x).obj R₁))] -/
        /- simp -/
        /- /- rw [Category.id_comp] -/ -/
        /- simp -/

        #check Category.comp_id
        rw [← whisker_exchange_assoc]
        rw [← whisker_exchange_assoc]

        rw [← comp_whiskerRight _ _ _]
        simp?

        symm
        rw [← whiskerLeft_comp _ _ _]
        apply congrArg
        rw [← id_whiskerRight]
        rw [← comp_whiskerRight _ _ _]
        apply congrArg (· ▷ (project fun x ↦ FreeTwistedCategoryQuiver.of x).obj R₁)
        rw [Category.id_comp]

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
      any_goals simp_all
      all_goals sorry
    all_goals sorry
    case swap X Y L X₁ Y₁ s₁ M X₂ R Y₂ s₂ =>
      simp_all
      -- get the embed.map outta here
      unfold embed
      unfold project
      simp
      repeat rw [← mk_α_inv]
      repeat rw [← mk_α_hom]
      repeat rw [← mk_whiskerLeft]
      repeat rw [← mk_whiskerRight]
      simp
      /- repeat rw [associator_naturality_left_assoc] -/
      /- rw [← whiskerLeft_comp_assoc _ (⟦FreeTwistedCategoryQuiver.Hom.of (cast ⋯ s₁)⟧ ▷ _ ▷ _ ▷ _) _] -/
      
      -- move the s₁ layer up the word, past s₂, on the LHS

      rw [← whiskerLeft_comp_assoc _ (((_ ▷ _) ▷ _) ▷ _) _]
      rw [← comp_whiskerRight _ _ _]
      rw [associator_naturality_left]
      rw [comp_whiskerRight _ _ _]
      rw [whiskerLeft_comp_assoc _ _ _]

      rw [← whiskerLeft_comp_assoc _ ((_ ▷ _) ▷ _) _]
      rw [associator_naturality_left]
      rw [whiskerLeft_comp_assoc _ _ _]

      rw [← whiskerLeft_comp_assoc _ (_ ▷ ((_ ⊗ _) ⊗ _)) _]
      rw [← whisker_exchange]
      rw [whiskerLeft_comp_assoc _ _ _]

      simp

      rw [← whiskerLeft_comp_assoc _ (((_ ▷ _) ▷ _) ▷ _) _]
      rw [associator_naturality_left]
      rw [whiskerLeft_comp_assoc _ _ _]

      rw [← whiskerLeft_comp_assoc _ ((_ ▷ _) ▷ _) _]
      rw [associator_naturality_left]
      rw [whiskerLeft_comp_assoc _ _ _]

      rw [← whiskerLeft_comp_assoc _ (_ ▷ (_ ⊗ _ ⊗ _)) _]
      rw [← whisker_exchange]

      -- it's moved! The layers are in the same positions.
      -- b/c monoidal categories are thin, the stuff between
      -- the layers must be the same.

      coherence
    all_goals simp_all

#check MonoidalCategory

instance toNat : FQ V ⥤ F V where
  obj := FtoFQ.symm
  map := sorry

#check Equivalence
-- we need something stronger than equivalence -- isomorphism of categories!

end NatDefinition
-/


