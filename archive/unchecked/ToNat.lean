import Mathlib
import LeanCategory.NatDefinition
import LeanCategory.FreeEggerQuiver

variable {V : Type u}
  --[stitches : Quiver.{v} (F V)]
  [otherStitches : Quiver (FQ V)]

@[simp]
def FQtoF : FQ V → F V
  | .of v => .of v
  | .unit => .unit
  | .tensor X Y => .tensor (FQtoF X) (FQtoF Y)
  | .star X => .star (FQtoF X)

@[simp]
def FtoFN : F V → FN V
  | .of v => .of v
  | .unit => .unit
  | .tensor X Y => .tensor (FtoFN X) (FtoFN Y)
  | .star X => .star (FtoFN X)

namespace CategoryTheory.FreeTwistedCategoryQuiver

instance toNat : FQ V ⥤ FN V where
  obj := FtoFN ∘ FQtoF
  map := sorry
  map_comp := sorry
  map_id := sorry

#check Hom
#synth Quiver (FQ V)

def fromNatLayerHelper (D C : FN V) (s : ℕ) (x : (FNtoF D) ⟶ (FNtoF C)) :
    (FtoFQ (FNtoF (s.repeat FreeTwistedCategoryNat.star D)) ⟶Q
       FtoFQ (FNtoF (s.repeat FreeTwistedCategoryNat.star C))) := match s with
  | 0 => ⟦.of <| x⟧
  | s + 1 => 
    (ς_ _).hom ≫
    (fromNatLayerHelper D C s x) ≫
    (ς_ _).inv

lemma fromNatLayerHelper_succ {D C : FN V} {x : (FNtoF D) ⟶ (FNtoF C)} :
    fromNatLayerHelper D C (s + 1) x = (ς_ _).hom ≫ (fromNatLayerHelper D C s x) ≫ (ς_ _).inv :=
  rfl

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



#check Equivalence
-- we need something stronger than equivalence -- isomorphism of categories!



