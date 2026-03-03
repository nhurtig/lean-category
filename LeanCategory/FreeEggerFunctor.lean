import LeanCategory.PreFreeEggerFunctor
import LeanCategory.FreeEggerGood

open CategoryTheory

-- TODO maybe we should just prove it straight up on the quotient? That way, we can use
-- simp to rewrite stuff... just like the monoidal file!
-- See the mk_* lemmas here:
#check FreeMonoidalCategory
-- then the normalizing lemmas here:
#check MonoidalCategory

-- we'll need to completely redo the mk_* lemmas, but we can use the normalizing lemmas for monoidal (just needs
-- updating w/ the involution/star/twist stuff)

variable {P Q : Type u}
variable [StarMonoid P] [userP : Quiver.{v} P] [StarMonoid Q] [userQ : Quiver.{v} Q]

variable (m : P →⋆* Q)
variable (M : {X Y : P} → (X ⟶ Y) → (m X ⟶ m Y))

/- @[simp] -/
/- theorem mk_id' {X : P} : ⟦𝟙ᵥ X⟧ = 𝟙 X := -/
/-   rfl -/
/- set_option trace.simplify.rewrite true -/
/- set_option diagnostics true -/
/- set_option diagnostics.threshold 0 -/
/- set_option trace.Meta.Tactic.simp true -/

/- lemma eqToHomLeftSimpTODOname {X X' Y : P} {h : X = X'} : -/

attribute [simp] mk_tensor
attribute [aesop safe] mk_tensor
#check mk_tensor
#check mk_comp
/- set_option trace.Meta.Tactic.simp.rewrite true -/
/- set_option trace.Meta.Tactic.simp true -/
/- set_option trace.Meta.Tactic.simp.rewrite true -/
/- set_option trace.Meta.Tactic.simp.discharge true -/

open MonoidalCategory

@[simp]
lemma my_map_mul : m (X ⊗ Y) = m X ⊗ m Y := by
  sorry

#check MonoidalCategory
#check FreeMonoidalCategory
#check CategoryTheory.eqToIso

--eqToHom vs. whisker lemma
lemma eqToHom_whiskerLeft {h : X' = X} {f : Y₁ ⟶ Y₂} : (eqToHom (by rw [h])) ≫ (X ◁ f) = X' ◁ f := by
  sorry

@[reassoc (attr := simp)]
lemma maybeThis {f : Y₁ ⟶ Y₂} {X₁ X₂ : P} : (m (X₁ ⊗ X₂) ◁ f) = eqToHom (by sorry) ≫ ((MonoidalCategoryStruct.tensorObj (m X₁) (m X₂)) ◁ f) ≫ eqToHom (by sorry) := by
  sorry

@[reassoc (attr := simp)]
lemma maybeThisIdWhisker {f : Y₁ ⟶ Y₂} : (m (𝟙_ P) ◁ f) = eqToHom (by sorry) ≫ ((𝟙_ Q) ◁ f) ≫ eqToHom (by sorry) := by
  sorry

@[reassoc (attr := simp)]
lemma maybeThisWhiskerId {f : Y₁ ⟶ Y₂} : (f ▷ m (𝟙_ P)) = eqToHom (by sorry) ≫ (f ▷ (𝟙_ Q)) ≫ eqToHom (by sorry) := by
  sorry

/- @[reassoc (attr := simp)] -/
/- lemma maybeThisStar {X : P} : (𝟙 (m (InvolutiveCategoryStruct.starObj X))) = eqToHom (by sorry) ≫ (𝟙 (InvolutiveCategoryStruct.starObj (m X))) ≫ eqToHom (by sorry) := by -/
/-   sorry -/

/- @[reassoc (attr := simp)] -/
/- lemma maybeThisStar {X : P} : (𝟙 (InvolutiveCategoryStruct.starObj (m X))) = eqToHom (by sorry) ≫ (𝟙 (m (InvolutiveCategoryStruct.starObj X))) ≫ eqToHom (by sorry) := by -/
/-   sorry -/

@[reassoc (attr := simp)]
lemma eqToHom_id {X' X : P} {h : X' = X} : (eqToHom h) ≫ (𝟙 X) = eqToHom h := by
  sorry

#check eqToHom_id
#check eqToHom_id_assoc

macro "myTODO" : tactic =>
  `(tactic|
    repeat (first
     | simp [MonoidalCategory.tensorHom_def]
     | rw [mk_tensor]
     )
  )

#check eqToHom

instance proj : P ⥤ Q where
  obj := m
  map {X Y} := Quotient.lift (⟦·.proj m M⟧) <| by
    intros f g h
    simp
    induction h
    any_goals myTODO
    case star_id =>
      show _ = (@eqToHom Q quotiented.toCategoryStruct _ _ rfl)
      show _ ≫ (@eqToHom Q quotiented.toCategoryStruct _ _ rfl) ≫ _ = _
      cat_disch
    case star_skew =>
      simp
      sorry
    all_goals sorry
    /- case tensor_comp_tensor => -/
    /-   rw [MonoidalCategory.whisker_exchange_assoc] -/
    /- any_goals cat_disch -/
    /- case comp_id => -/
    /-   /- simp [CategoryStruct.id] -/ -/
    /-   /- rw [mk_id] -/ -/
    /-   rw [Category.comp_id] -/
    /-   sorry -/
    /- any_goals grind -/
    /- sorry -/

def HomEquiv.myfunct {X Y : P} {f g : X ⟶ᵥ Y} (h : f ≈ g) :
    ((f.myfunct m M) ≈ (g.myfunct m M)) := by
  induction h
  any_goals simp
  any_goals constructor; done
  any_goals grind
  /- any_goals constructor <;> grind -/
  case id_tensor_id =>
    eqToHom_eq_eqToHom
  case tensor_comp_tensor =>
    simp
    sorry
  sorry

