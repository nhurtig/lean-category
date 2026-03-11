import Mathlib
import LeanCategory.Layer

namespace NatDefinition

variable {V : Type u}

variable [stitches : Quiver.{v} (F V)]

/- notation "F" => CategoryTheory.FreeTwistedCategory -/

inductive Hom : F V → F V → Type (max (u + 2) v) where
  | layer : (l : Layer V) →
      Hom (l.boundary .Bottom) (l.boundary .Top)
  | braid {X Y : F V} : (X ⟶β Y) → Hom X Y
  /- | id (X : F V) : Hom X X -- was just using braid's id, but -/
  /- -- ran into motive issues -/
  | comp {X Y Z : F V} : Hom X Y → Hom Y Z → Hom X Z

infixr:10 " ⟶ⁿ " => Hom

open CategoryTheory

/- instance (priority := low) preHom : CategoryStruct (F V) where -/
/-   Hom := Hom -/
/-   /- id X := .braid (𝟙 (FtoF X)) -/ -/
/-   id := Hom.id -/
/-   comp := Hom.comp -/

open MonoidalCategory
open InvolutiveCategory -- for the ⋆ notation
open TwistedCategory -- why not

macro "pure_iso_step_forwards" : tactic =>
  `(tactic|
    first
      | exact 𝟙 _
      | refine ?_ ▷ _
      | refine _ ◁ ?_
      | refine (α_ _ _ _).inv ≫ ?_
      | refine ?_ ≫ (α_ _ _ _).hom
      | refine (λ_ _).hom ≫ ?_
      | refine ?_ ≫ (λ_ _).inv
      | refine (ρ_ _).hom ≫ ?_
      | refine ?_ ≫ (ρ_ _).inv
      | refine (χ_ _ _).inv ≫ ?_
      | refine ?_ ≫ (χ_ _ _).hom
      | fail "IDK what to do"
  )

-- associator is reversed here
macro "pure_iso_step_backwards" : tactic =>
  `(tactic|
    first
      | exact 𝟙 _
      | refine ?_ ▷ _
      | refine _ ◁ ?_
      | refine (α_ _ _ _).hom ≫ ?_
      | refine ?_ ≫ (α_ _ _ _).inv
      | refine (λ_ _).hom ≫ ?_
      | refine ?_ ≫ (λ_ _).inv
      | refine (ρ_ _).hom ≫ ?_
      | refine ?_ ≫ (ρ_ _).inv
      | refine (χ_ _ _).inv ≫ ?_
      | refine ?_ ≫ (χ_ _ _).hom
      | fail "IDK what to do"
  )

-- the tactic equivalent of smacking a TV to see if that fixes it
macro "pure_iso" : tactic =>
  `(tactic|
      ((repeat pure_iso_step_forwards) ; (repeat pure_iso_step_backwards))
  )

open MonoidalCategory
/- @[simp, grind] -/
/- def Hom.whisker (X : F V) {Y₁ Y₂ : F V} : (Y₁ ⟶ⁿ Y₂) → (Z : F V) → -/
/-     ((X * (Y₁ * Z)) ⟶ⁿ (X * (Y₂ * Z))) -/
/-   | .layer ⟨L, D, C, s, x, R⟩, Z => -/
/-     (Hom.braid <| by pure_iso).comp <| -/
/-     (Hom.layer ⟨X * L, D, C, s, x, R * Z⟩).comp -/
/-     (.braid <| by pure_iso) -/
/-   | .braid b, Z => Hom.braid (↑X ◁ b ▷ ↑Z) -/
/-   -- | .id Y, Z => 𝟙 (X * Y * Z) -/
/-   | .comp f g, Z => (whisker X f Z).comp (whisker X g Z) -/

/- #synth Quiver N -/

/- @[simp, grind] -/
@[simp]
def Hom.whiskerLeft (X : F V) {Y₁ Y₂ : F V} : (Y₁ ⟶ⁿ Y₂) → ((X.tensor Y₁) ⟶ⁿ (X.tensor Y₂))
  /- | .id _ => .id _ -/
  | .layer ⟨L, D, C, s, x, R⟩ =>
    (Hom.braid <| by pure_iso).comp <|
    (Hom.layer ⟨X.tensor L, D, C, s, x, R⟩).comp
    (.braid <| by pure_iso)
  | .braid b => Hom.braid (X ◁ b)
  | .comp f g => (f.whiskerLeft X).comp (g.whiskerLeft X)

@[simp]
def Hom.whiskerRight (X : F V) {Y₁ Y₂ : F V} : (Y₁ ⟶ⁿ Y₂) → ((Y₁.tensor X) ⟶ⁿ (Y₂.tensor X))
  /- | .id _ => .id _ -/
  | .layer ⟨L, D, C, s, x, R⟩ =>
    (Hom.braid <| by pure_iso).comp <|
    (Hom.layer ⟨L, D, C, s, x, R.tensor X⟩).comp
    (.braid <| by pure_iso)
  | .braid b => Hom.braid (b ▷ X)
  | .comp f g => (f.whiskerRight X).comp (g.whiskerRight X)

/- @[simp, grind] -/
/- def Hom.whiskerRight {X₁ X₂ : F V} (f : X₁ ⟶ⁿ X₂) (Y : F V) : ((X₁ * Y) ⟶ⁿ (X₂ * Y)) := -/
/-   -- eqToHom (by simp) ≫ Hom.whisker 1 f Y ≫ eqToHom (by simp) -/
/-   (Hom.braid (by pure_iso)).comp <| -/
/-     (Hom.whisker 1 f Y).comp <| -/
    /- Hom.braid (by pure_iso) -/

@[simp, grind]
def Hom.tensor {X₁ X₂ Y₁ Y₂ : F V} (f : X₁ ⟶ⁿ Y₁) (g : X₂ ⟶ⁿ Y₂) :
    (X₁.tensor X₂) ⟶ⁿ (Y₁.tensor Y₂) :=
  (f.whiskerRight X₂).comp (g.whiskerLeft Y₁)

/- @[simp, grind] -/
@[simp]
def Hom.star {X Y : F V} : (X ⟶ⁿ Y) → (X.star ⟶ⁿ Y.star)
  /- | .id _ => .id _ -/
  | .layer ⟨L, X, Y, s, x, R⟩ =>
      (Hom.braid <| by pure_iso).comp <|
        (Hom.layer ⟨R.star, X, Y, s+1, x, L.star⟩).comp <|
        Hom.braid (by pure_iso)
  | .braid b => .braid b⋆
  | .comp f g => (f.star).comp g.star

-- #synth Quiver (S (F V))

-- variable {X Y Z : S (F V)} {b₁ : X ⟶ Y} {b₂ : Y ⟶ Z}
/- def swapLHSMiddle (X L Y₁ X₂ M R : F V) : L ⊗ () ⊗ () ⟶ⁿ _ := -/
/-   X ◁ L ◁ Nat.repeat FreeTwistedCategory.star s₁ Y₁ ◁ (α_ M (Nat.repeat FreeTwistedCategory.star s₂ X₂) R).hom ≫ -/
/-       (α_ X L (Nat.repeat FreeTwistedCategory.star s₁ Y₁ ⊗ M ⊗ Nat.repeat FreeTwistedCategory.star s₂ X₂ ⊗ R)).inv ≫ -/
/-         (α_ (X ⊗ L) (Nat.repeat FreeTwistedCategory.star s₁ Y₁) (M ⊗ Nat.repeat FreeTwistedCategory.star s₂ X₂ ⊗ R)).inv ≫ -/
/-           (α_ ((X ⊗ L) ⊗ Nat.repeat FreeTwistedCategory.star s₁ Y₁) M (Nat.repeat FreeTwistedCategory.star s₂ X₂ ⊗ R)).inv -/

#check MonoidalCategory
@[grind]
inductive Hom.Equiv : ∀ {X Y : (F V)}, (X ⟶ⁿ Y) → (X ⟶ⁿ Y) → Prop where
  | refl (f) : Hom.Equiv f f
  | comp {f f' : X ⟶ⁿ Y} : Hom.Equiv f f' → Hom.Equiv g g' → Hom.Equiv (f.comp g) (f'.comp g')
  /- | id_comp : Hom.Equiv ((Hom.id _).comp f) f -/
  /- | comp_id : Hom.Equiv (f.comp <| Hom.id _) f -/
  | id_comp : Hom.Equiv ((Hom.braid (𝟙β X)).comp f) f
  | comp_id {f : X ⟶ⁿ Y} : Hom.Equiv (f.comp (.braid (𝟙β Y))) f
  | assoc {f : _ ⟶ⁿ _} {g : _ ⟶ⁿ _} {h : _ ⟶ⁿ _} :
      Hom.Equiv ((f.comp g).comp h) (f.comp (g.comp h))
  | merge_braid {b₁ : X ⟶β (Y)} {b₂ : (Y) ⟶β (Z)} :
      Hom.Equiv ((Hom.braid b₁).comp (.braid b₂)) (.braid (b₁ ≫β b₂))
  -- the paper's rules
  | swap : Hom.Equiv
      ((Hom.layer ⟨L, X₁, Y₁, s₁, x₁, (M.tensor (s₂.repeat .star X₂)).tensor R⟩).comp
        ((Hom.braid (by simp; pure_iso)).comp
        ((Hom.layer ⟨(L.tensor (s₁.repeat .star Y₁)).tensor M, X₂, Y₂, s₂, x₂, R⟩))))
      ((Hom.braid <| by pure_iso).comp
        ((Hom.layer ⟨(L.tensor (s₁.repeat .star X₁)).tensor M, X₂, Y₂, s₂, x₂, R⟩).comp
        ((Hom.braid <| by pure_iso).comp
        ((Hom.layer ⟨L, X₁, Y₁, s₁, x₁, (M.tensor (s₂.repeat .star Y₂)).tensor R⟩).comp
        (Hom.braid <| by pure_iso)))))
  | layer (f : l₁ ⟶L l₂) : Hom.Equiv
      (Hom.layer l₁)
      ((Hom.braid <| f.φ .Bottom).comp <|
        (Hom.layer l₂).comp <|
        (Hom.braid <| Groupoid.inv <| f.φ .Top))
  | symm (f g) : Hom.Equiv f g → Hom.Equiv g f
  | trans {f g h : X ⟶ⁿ Y} : Hom.Equiv f g → Hom.Equiv g h → Hom.Equiv f h

def Hom.Equiv.swap_nice {L : F V} {x : L ⊗ Nat.repeat FreeTwistedCategory.star s₁ Y₁ ⊗ (M ⊗ Nat.repeat FreeTwistedCategory.star s₂ X₂) ⊗ R ⟶β
  ((L ⊗ Nat.repeat FreeTwistedCategory.star s₁ Y₁) ⊗ M) ⊗ Nat.repeat FreeTwistedCategory.star s₂ X₂ ⊗ R} (hx : x = (by pure_iso)) : Hom.Equiv
      ((Hom.layer ⟨L, X₁, Y₁, s₁, x₁, (M.tensor (s₂.repeat .star X₂)).tensor R⟩).comp
        ((Hom.braid x).comp
        ((Hom.layer ⟨(L.tensor (s₁.repeat .star Y₁)).tensor M, X₂, Y₂, s₂, x₂, R⟩))))
      ((Hom.braid <| by pure_iso).comp
        ((Hom.layer ⟨(L.tensor (s₁.repeat .star X₁)).tensor M, X₂, Y₂, s₂, x₂, R⟩).comp
        ((Hom.braid <| by pure_iso).comp
        ((Hom.layer ⟨L, X₁, Y₁, s₁, x₁, (M.tensor (s₂.repeat .star Y₂)).tensor R⟩).comp
        (Hom.braid <| by pure_iso))))) := by
  rw [hx]
  exact Hom.Equiv.swap


instance {X Y : F V} : HasEquiv (Hom X Y) where
  Equiv := Hom.Equiv

instance {X Y : F V} : HasEquiv (X ⟶ⁿ Y) where
  Equiv := Hom.Equiv

/- attribute [grind →] Hom.Equiv.comp -/

/- @[grind =_] -/
/- lemma Hom.Equiv_def {X Y : F V} {f g : X ⟶ⁿ Y} : Hom.Equiv f g ↔ f ≈ g := by -/
/-   constructor -/
/-   all_goals intros h -/
/-   all_goals exact h -/

/- @[grind =_] -/
/- lemma Hom.Equiv_def' {X Y : F V} {f g : Hom X Y} : Hom.Equiv f g ↔ f ≈ g := by -/
/-   constructor -/
/-   all_goals intros h -/
/-   all_goals exact h -/

open CategoryTheory.MonoidalCategory
#check CategoryTheory.MonoidalCategory

/- lemma Hom.Equiv.braid {X Y : F V} {b b' : X ⟶β Y} : -/
/-     b = b' → (Hom.braid b) ≈ (Hom.braid b') := by -/
/-   grind -/

instance mySetoidHom (X Y : F V) : Setoid (X ⟶ⁿ Y) :=
⟨Hom.Equiv, ⟨Hom.Equiv.refl, Hom.Equiv.symm _ _, Hom.Equiv.trans⟩⟩
#check mySetoidHom
#synth Quiver (F V)


namespace NatCategory

#check Quiver

def Hom X Y := _root_.Quotient (@mySetoidHom V _ X Y)
scoped infixr:10 " ⟶N " => Hom
@[simp]
def homMk {X Y : F V} (f : X ⟶ⁿ Y) : X ⟶N Y := ⟦f⟧

#check CategoryStruct

def id (X : F V) : X ⟶N X := ⟦Hom.braid (𝟙 X)⟧
scoped notation "𝟙N" => id

@[simp]
theorem mk_id {X : F V} : ⟦.braid (𝟙 X)⟧ = 𝟙N X :=
  rfl

def comp {X Y Z : F V} (f : X ⟶N Y) (g : Y ⟶N Z) : X ⟶N Z :=
  Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ Hom.Equiv.comp hf hg) f g
scoped infixr:80 " ≫N " => comp

@[simp]
theorem mk_comp {X Y Z : F V} (f : X ⟶ⁿ Y) (g : Y ⟶ⁿ Z) :
    ⟦Hom.comp f g⟧ = ⟦f⟧ ≫N ⟦g⟧ :=
  rfl

@[simp]
theorem unmk_braid_comp {X Y Z : F V} (f : (X) ⟶β (Y)) (g : (Y) ⟶β (Z)) :
     ⟦.braid f⟧ ≫N ⟦.braid g⟧ = ⟦.braid (f ≫β g)⟧ := by
  apply Quotient.sound
  constructor


#check Category

@[simp]
lemma id_comp : ∀ {X Y : F V} (f : X ⟶N Y), 𝟙N X ≫N f = f := by
  rintro X Y ⟨f⟩
  exact _root_.Quotient.sound .id_comp

@[simp]
lemma comp_id : ∀ {X Y : F V} (f : X ⟶N Y), f ≫N 𝟙N Y = f := by
  rintro X Y ⟨f⟩
  exact _root_.Quotient.sound .comp_id

@[simp]
lemma assoc : ∀ {W X Y Z : F V} (f : W ⟶N X) (g : X ⟶N Y) (h : Y ⟶N Z),
    (f ≫N g) ≫N h = f ≫N g ≫N h := by
  rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩
  apply _root_.Quotient.sound Hom.Equiv.assoc

@[simp]
theorem unmk_braid_comp_assoc {X Y Z : F V} (f : X ⟶β Y) (g : Y ⟶β Z) (h : Z ⟶N A) :
     ⟦.braid f⟧ ≫N ⟦.braid g⟧ ≫N h = ⟦.braid (f ≫β g)⟧ ≫N h := by
  rw [← assoc]
  apply congrArg (· ≫N _)
  apply Quotient.sound
  constructor

#check MonoidalCategoryStruct

-- it helps the real category and our "category" play nice to NOT
-- have separate definitions for objects (TODO make sure it's similar
-- with the star)
/- def tensorObj : F V → F V → F V := (· ⊗ ·) -/
/- scoped infixr:70 " ⊗N " => tensorObj -/

open MonoidalCategory
open FreeTwistedCategory
#check mk_α_inv
/- set_option pp.notation false -/
/- set_option pp.explicit true -/

#check IsIso
-- if x is an iso, then f ≫ i = g → f = g ≫ i.inv

lemma stripBraidLeft {X Y : F V} {b : X ⟶β Y} {f : Y ⟶N Z} {g : X ⟶N Z} :
    ⟦(Hom.braid b)⟧ ≫N f = g → f = ⟦(Hom.braid (inv b))⟧ ≫N g := by
  intros h
  trans (⟦Hom.braid (inv b)⟧ ≫N (⟦Hom.braid b⟧ ≫N f))
  · simp
  · rw [h]

lemma stripBraidRight {X Y : F V} {b : Y ⟶β Z} {f : X ⟶N Y} {g : X ⟶N Z} :
    f ≫N ⟦(Hom.braid b)⟧ = g → f = g ≫N ⟦(Hom.braid (inv b))⟧ := by
  intros h
  trans ((f ≫N ⟦Hom.braid b⟧) ≫N ⟦Hom.braid (inv b)⟧)
  · simp
  · rw [h]

def whiskerLeft (X : F V) {Y₁ Y₂ : F V} (f : Y₁ ⟶N Y₂) : (X ⊗ Y₁ ⟶N X ⊗ Y₂) := --by
  Quotient.liftOn f (⟦·.whiskerLeft X⟧) <| by
    clear f
    rintro f g h
    simp
    induction h
    case layer l₁ l₂ f =>
      simp_all
      induction f
      case freeRight =>
        sorry
      all_goals sorry
      case comp ih₁ ih₂ =>
        rw [ih₁]
        have ih₂ := stripBraidLeft ih₂
        have ih₂ := stripBraidRight ih₂
        rw [ih₂]
        simp
    all_goals sorry
    case swap L X₁ Y₁ s₁ x₁ M X₂ Y₂ s₂ x₂ R =>
      simp_all

      -- reassociate the second layer in the LHS:
      apply Eq.trans
      apply congrArg (_ ≫N ·)
      apply congrArg (_ ≫N ·)
      apply congrArg (_ ≫N ·)
      apply congrArg (· ≫N _)
      apply Quotient.sound
      apply Hom.Equiv.layer
      apply Layer.Hom.freeLeft
      apply Quotient.mk
      exact (CategoryTheory.FreeTwistedCategory.Hom.α_inv _ _ _).comp <|
        (FreeTwistedCategory.Hom.whiskerRight (FreeTwistedCategory.Hom.α_inv _ _ _) _)
      simp
      repeat1 rw [mk_whiskerRight]
      repeat1 rw [mk_α_inv]
      simp

      -- forget about the braids outside of the layers:
      apply Eq.trans
      apply congrArg (_ ≫N ·)
      repeat rewrite [← assoc]
      apply congrArg (· ≫N _)
      simp


      -- swap the layers:
      apply Quotient.sound
      apply Hom.Equiv.swap_nice
      pure_coherence
      simp

      -- reassociate the first layer morphism again:
      apply Eq.trans
      apply congrArg (_ ≫N ·)
      apply congrArg (· ≫N _)
      apply Quotient.sound
      apply Hom.Equiv.layer
      apply Layer.Hom.freeLeft
      apply Quotient.mk
      exact 
        (FreeTwistedCategory.Hom.whiskerRight (FreeTwistedCategory.Hom.α_hom _ _ _) _).comp <|
        (CategoryTheory.FreeTwistedCategory.Hom.α_hom _ _ _)
      simp
      repeat1 rw [mk_whiskerRight]
      repeat1 rw [mk_α_hom]
      simp

      -- now the layers are in the same positions. Show each composition is the same,
      -- using pure_coherence for braids and rfl for layers:
      apply congrArg₂ _ (congrArg _ (congrArg _ (by pure_coherence)))
      apply congrArg₂ _ rfl
      apply congrArg₂ _ (congrArg _ (congrArg _ (by pure_coherence)))
      apply congrArg₂ _ rfl (congrArg _ (congrArg _ (by pure_coherence)))
      /-
      apply congrArg
      apply congrArg
      pure_coherence

      simp

      /- have x :=  -/
      /-         ((α_ ?L (Nat.repeat FreeTwistedCategory.star ?s₁ ?Y₁) -/
      /-               ((FreeTwistedCategory.tensor ?M (Nat.repeat FreeTwistedCategory.star ?s₂ ?X₂)).tensor ?R)).inv ≫ -/
      /-           (α_ (?L ⊗ Nat.repeat FreeTwistedCategory.star ?s₁ ?Y₁) -/
      /-                 (FreeTwistedCategory.tensor ?M (Nat.repeat FreeTwistedCategory.star ?s₂ ?X₂)) ?R).inv ≫ -/
      /-             ((α_ (?L ⊗ Nat.repeat FreeTwistedCategory.star ?s₁ ?Y₁) ?M -/
      /-                       (Nat.repeat FreeTwistedCategory.star ?s₂ ?X₂)).inv ≫ -/
      /-                   𝟙 -/
      /-                     (((?L ⊗ Nat.repeat FreeTwistedCategory.star ?s₁ ?Y₁) ⊗ ?M) ⊗ -/
      /-                       Nat.repeat FreeTwistedCategory.star ?s₂ ?X₂)) ▷ -/
      /-                 ?R ≫ -/
      /-               (α_ ((FreeTwistedCategory.tensor ?L (Nat.repeat FreeTwistedCategory.star ?s₁ ?Y₁)).tensor ?M) -/
      /-                   (Nat.repeat FreeTwistedCategory.star ?s₂ ?X₂) ?R).hom) -/

      -- rewrite the middle braid so we can swap:
      apply Eq.trans
      apply congrArg (_ ≫N ·)
      apply congrArg (_ ≫N ·)
      apply congrArg (· ≫N _)
      apply congrArg
      apply congrArg
      show _ = ((α_ ?L (Nat.repeat FreeTwistedCategory.star ?s₁ ?Y₁)
                    ((FreeTwistedCategory.tensor ?M (Nat.repeat FreeTwistedCategory.star ?s₂ ?X₂)).tensor ?R)).inv ≫
                (α_ (?L ⊗ Nat.repeat FreeTwistedCategory.star ?s₁ ?Y₁)
                      (FreeTwistedCategory.tensor ?M (Nat.repeat FreeTwistedCategory.star ?s₂ ?X₂)) ?R).inv ≫
                  ((α_ (?L ⊗ Nat.repeat FreeTwistedCategory.star ?s₁ ?Y₁) ?M
                            (Nat.repeat FreeTwistedCategory.star ?s₂ ?X₂)).inv ≫
                        𝟙
                          (((?L ⊗ Nat.repeat FreeTwistedCategory.star ?s₁ ?Y₁) ⊗ ?M) ⊗
                            Nat.repeat FreeTwistedCategory.star ?s₂ ?X₂)) ▷
                      ?R ≫
                    (α_ ((FreeTwistedCategory.tensor ?L (Nat.repeat FreeTwistedCategory.star ?s₁ ?Y₁)).tensor ?M)
                        (Nat.repeat FreeTwistedCategory.star ?s₂ ?X₂) ?R).hom)
      repeat1 rw [mk_whiskerRight]
      repeat1 rw [mk_α_inv]
      simp
      pure_coherence

      -- forget about the braids outside of the layers:
      apply Eq.trans
      apply congrArg (_ ≫N ·)
      repeat rewrite [← assoc]
      apply congrArg (· ≫N _)
      /- simp -/
      apply Quotient.sound
      apply Hom.Equiv.swap

      sorry
      sorry
      coherence
      /- refine _ = ?_ -/
      /- congruence -/
      /- simp -/
      sorry
      -/
    all_goals sorry
    any_goals simp_all
    /- any_goals aesop -/
    case trans =>
      sorry
   /-
    case comp =>
      simp_all
      aesop
      sorry
    all_goals sorry
    case swap L X₁ Y₁ s₁ x₁ M X₂ Y₂ s₂ x₂ R =>
      simp_all
      /- #check ⊢ -/
      /- simp only [Hom.whiskerLeft] -/

      /- simp -/
      repeat rw [unmk_braid_comp_assoc]
      repeat rw [unmk_braid_comp]
      -- TODO for 3/11: this is silly. Can we instead
      -- define and prove a functor from freeQuiver to
      -- NatDefinition? That will show that it's
      -- all the flavors of categories anyways, but we
      -- won't have to deal with the yucky stuff. We'll
      -- just have to define the Hom stuff (like Hom.whiskerLeft),
      -- then define the aux map from freeQuiver words to
      -- NatHom words, then show the aux map respects freeQuiver
      -- equalities: equivalent things in freeQuiver are
      -- equivalent in Nat. We already did our time in dealing
      -- with the yucky Nat equalities in the other functor
      -- definition; this time we have the opportunity to
      -- use them. I still don't understand why this seems easy,
      -- as we'll have to end up proving that this equality is
      -- respected anyways... We know Nat words X and Y are equivalent
      -- via swap. Map them via the functor fromNat, call whiskerLeft
      -- proper on them, and map them back. Then those things have to
      -- be equivalent, even if the composition of the functors isn't
      -- well-behaved... Ah, I see. The rule is the whiskerLeft one
      -- in HomEquiv, that states that equality is preserved by whiskerLeft.
      -- Since we plan on mapping whiskerLeft to whiskerLeft, we have to prove
      -- this exact lemma we're struggling with now. No shortcuts...
      --
      -- Okay then. Maybe the strategy is to get out of quotient land, and 
      -- go into Hom.Equiv land. Or maybe that'll make no difference...
      --
      -- Oh, now I remember! I wanted to change the swap rule so that it's
      -- more permissive: any non-twisting braid is good. Unclear what that
      -- really means in the quotient of all those relations, though. Maybe
      -- we don't have to put it on the quotient of the relations; maybe it's
      -- just that the word in the ⟦ ⟧ is non-twisting. Boy, it would be nice
      -- to have strictness and eqToHom back again for this...
      --
      -- Wait, no again! We'll just instantiate the rewrite rule, postulate that
      -- the goal's LHS is equal to the rewrite rule's LHS, prove it using the
      -- magical coherence tactic, and then they're swapped!
      -- issue: the added X by the whiskering has screwed up the association
      -- of the L ⊗ Y₁ ⊗ M stuff, so we need to use the layer rules to reassociate.
      -- likely, the play is to apply transitivity (quotient land (strict equality) is fine?)
      -- to make the RHS a hole, apply congrArg to locate just the layer we want to
      -- mess with, do some explicit rewriting (pray that the βcat is nice), and then
      -- zoom back out and reassociate/merge braids/simp.
      apply Eq.trans
      apply congrArg (_ ≫ ·)
      apply congrArg (_ ≫ ·)
      apply congrArg (_ ≫ ·)
      apply congrArg (· ≫ _)
      apply Quotient.sound
      -- Nat's new idea: screw natCategory. It's not a category, it's just a category-shaped
      -- thing.
      apply Hom.Equiv.layer
      apply Layer.Hom.freeLeft
      apply Quotient.mk
      exact (CategoryTheory.FreeTwistedCategory.Hom.α_inv _ _ _).comp <|
        (FreeTwistedCategory.Hom.whiskerRight (FreeTwistedCategory.Hom.α_inv _ _ _) _)
      simp
      repeat rw [unmk_braid_comp_assoc]
      repeat rw [unmk_braid_comp]

      apply Eq.trans
      apply congrArg (_ ≫ ·)
      apply congrArg (_ ≫ ·)
      apply congrArg (· ≫ _)
      apply congrArg
      apply congrArg
      apply Quotient.sound
      try rewrite [← βcat.assoc]
      try rewrite [βcat.assoc]
      rewrite [← Category.assoc]
      -- want to show this is equal to the middle of the swap thing, but alas, the instance
      -- synthesis is confused
      -- synthesis is confused
      -- synthesis is confused
      coherence
      simp
      apply Quotient.sound
      repeat rewrite [← Category.assoc]
      apply congrArg (· ≫ _)
      apply Quotient.sound
      apply Hom.
      apply Layer.Hom.freeRight
      apply Quotient.mk
      exact (CategoryTheory.FreeTwistedCategory.Hom.α_inv _ _ _).comp <|
        (FreeTwistedCategory.Hom.whiskerRight (FreeTwistedCategory.Hom.α_inv _ _ _) _).comp <|
        (FreeTwistedCategory.Hom.α_hom _ _ _)
      simp

      simp
      exact CategoryTheory.FreeTwistedCategory.Hom.α_inv (C := V) X (L * s₁ =>⋆ Y₁) M
      #check CategoryTheory.FreeTwistedCategory.Hom.α_hom
      refine (CategoryTheory.FreeTwistedCategory.Hom.id _).comp ?_
      exact (CategoryTheory.FreeTwistedCategory.Hom.α_inv _ _ _)
      /- let myβ := βcat -/
      /- #synth Category.{u, u} (F V) -/
      /- #check (@βtwist V).toTwistedCategoryStruct.twist -/
      refine ((@βtwist V).toTwistedCategoryStruct.twist _).inv ≫ ?_
      simp_all
      simp
      repeat rw [unmk_braid_comp_assoc]
      repeat rw [unmk_braid_comp]
      repeat1 rw [Category.assoc]
      repeat1 rw [unmk_braid_comp_assoc]
      simp
      simp_all
      simp at h
      rw [h]
      rw [unassoc_left]
      rw [rw_left (((@βtwist V).toTwistedCategoryStruct.twist) _).inv]


      simp
      rw [assoc_left]

      repeat1 rw [← Category.assoc]

      sorry
      /- apply congrArg₂ (@CategoryStruct.comp (F V) natCategory.toCategoryStruct ?dom ?middle ?cod) -/

      apply Quotient.sound
      constructor
      constructor
      constructor
      constructor
      constructor
      constructor
      apply Hom.Equiv.comp
      apply congrArg (⟦·⟧)
      /- refine congrArg₂ (@natCategory.comp _ _ _) sorry sorry -/
      /- sorry -/

      /- simp_all -/
      /- refine congrArg₂ (· ≫ ·) sorry sorry -/
      /- simp -/
      /- sorry -/

-/
  sorry
def comp {X Y Z : F V} (f : X ⟶N Y) (g : Y ⟶N Z) : X ⟶N Z :=
  Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ Hom.Equiv.comp hf hg) f g
scoped infixr:81 " ◁ " => whiskerLeft

end NatCategory

/- instance natCategory : Category (F V) where -/
/-   Hom X Y := _root_.Quotient (mySetoidHom X Y) -/
/-   /- id X := ⟦Hom.braid (𝟙 (FtoF X))⟧ -/ -/
/-   id X := ⟦Hom.id X⟧ -/
/-   comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ Hom.Equiv.comp hf hg) -/
/-   id_comp := by -/
/-     rintro X Y ⟨f⟩ -/
/-     exact _root_.Quotient.sound .id_comp -/
/-   comp_id := by -/
/-     rintro X Y ⟨f⟩ -/
/-     exact _root_.Quotient.sound .comp_id -/
/-   assoc {W X Y Z} := by -/
/-     rintro ⟨f⟩ ⟨g⟩ ⟨h⟩ -/
/-     exact _root_.Quotient.sound .assoc -/

#check FreeTwistedCategory.categoryFreeTwistedCategory 
open FreeTwistedCategory
#check categoryFreeTwistedCategory
#check monoidalFreeTwistedCategory
#check (monoidalFreeTwistedCategory.associator _ _ _).hom
attribute [instance] βcat
#check βcat.toCategoryStruct.associator
#synth Category.{u, u} (F V)
#synth MonoidalCategoryStruct.{u, u} (F V)

/- @[simp] -/
theorem assoc_left {L₁ : F V} :
    ⟦Hom.layer ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩⟧ =
      homMk (Hom.braid ((α_ _ _ _).hom ▷ _ ) |>.comp <|
        Hom.layer ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩ |>.comp <|
          Hom.braid ((α_ _ _ _).inv ▷ _ )) := by
  simp
  apply Quotient.sound
  let l₁ : Layer V := ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩
  let l₂ : Layer V := ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩
  let f : l₁ ⟶L l₂ := .freeLeft (α_ _ _ _).hom
  have h := Hom.Equiv.layer f
  unfold Layer.Hom.φ at h
  simp at h
  exact h

theorem unassoc_left {L₁ L₂ : F V} :
    ⟦Hom.layer ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩⟧ =
      homMk (Hom.braid ((α_ _ _ _).inv ▷ _ ) |>.comp <|
        Hom.layer ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩ |>.comp <|
          Hom.braid ((α_ _ _ _).hom ▷ _ )) := by
  simp
  apply Quotient.sound
  let l₂ : Layer V := ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩
  let l₁ : Layer V := ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩
  let f : l₁ ⟶L l₂ := .freeLeft (α_ _ _ _).inv
  have h := Hom.Equiv.layer f
  unfold Layer.Hom.φ at h
  simp at h
  exact h

theorem twist_left {L₁ : F V} :
    ⟦Hom.layer ⟨L, X, Y, s, x, R⟩⟧ =
      homMk (Hom.braid ((ς_ _).inv ▷ _ ) |>.comp <|
        Hom.layer ⟨L, X, Y, s, x, R⟩ |>.comp <|
          Hom.braid ((ς_ _).hom ▷ _ )) := by
  simp
  apply Quotient.sound
  let l₁ : Layer V := ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩
  let l₂ : Layer V := ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩
  let f : l₁ ⟶L l₂ := .freeLeft (α_ _ _ _).hom
  have h := Hom.Equiv.layer f
  unfold Layer.Hom.φ at h
  simp at h
  exact h

theorem rw_left {L₁ : F V} (b : L₁ ⟶β L₂) :
    ⟦Hom.layer ⟨L₁, X, Y, s, x, R⟩⟧ =
      homMk (Hom.braid (b ▷ _) |>.comp <|
        Hom.layer ⟨L₂, X, Y, s, x, R⟩ |>.comp <|
          Hom.braid (inv b ▷ _)) := by
  simp
  apply Quotient.sound
  let l₁ : Layer V := ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩
  let l₂ : Layer V := ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩
  let f : l₁ ⟶L l₂ := .freeLeft (α_ _ _ _).hom
  have h := Hom.Equiv.layer f
  unfold Layer.Hom.φ at h
  simp at h
  exact h

attribute [-instance] βcat

#check MonoidalCategory

/- @[simp] -/
/- theorem mk_braid_comp {X Y Z : F V} (f : (X) ⟶β (Y)) (g : (Y) ⟶β (Z)) : -/
/-     ⟦Hom.braid (f ≫β g)⟧ = @CategoryStruct.comp (F V) _ _ _ _ ⟦.braid f⟧ ⟦.braid g⟧ := by -/
/-   apply Quotient.sound -/
/-   constructor -/
/-   constructor -/

/- @[simp] -/
/- theorem mk_braid_comp' {X Y Z : F V} (f : (X) ⟶β (Y)) (g : (Y) ⟶β (Z)) : -/
/-     ⟦Hom.braid (f ≫β g)⟧ = @CategoryStruct.comp (F V) _ _ _ _ ⟦.braid f⟧ ⟦.braid g⟧ := by -/
/-   apply Quotient.sound -/
/-   constructor -/
/-   constructor -/

/- @[simp] -/
/- theorem mk_braid_comp' {X Y Z : F V} (f : X ⟶β Y) (g : Y ⟶β Z) : -/
/-     ⟦Hom.braid (f ≫ g)⟧ = ⟦Hom.braid (f ≫ g)⟧ := by -/
/-   apply Quotient.sound -/

/- @[simp] -/
/- theorem mk_braid_comp'' {X Y Z : F V} (f : (X) ⟶β (Y)) (g : (FtoF Y) ⟶β (FtoF Z)) : -/
/-     Hom.braid (f ≫ g) ≈ (Hom.braid (f)).comp (Hom.braid g) := by -/
/-   constructor -/
/-   constructor -/

@[simp]
theorem mk_id {X : F V} : ⟦Hom.id X⟧ = 𝟙 X :=
  rfl

/- @[simp] -/
/- theorem mk_id {X : F V} : ⟦Hom.braid (𝟙 (FtoF X))⟧ = 𝟙 X := -/
/-   rfl -/

/- @[simp] -/
/- theorem mk_whiskerLeft {X Y₁ Y₂ : F V} (f : Y₁ ⟶ⁿ Y₂) : ⟦f.whiskerLeft X⟧ = ◁ 𝟙 X := -/
/-   rfl -/
scoped notation:max n " =>⋆" => Nat.repeat FreeTwistedCategory.star n
#check natCategory.comp
#check @CategoryStruct.comp (F V) natCategory.toCategoryStruct _ _ _
#check congrArg₂

/- set_option pp.explicit true -/
/- set_option pp.notation false -/
/- set_option pp.universes true -/
/- set_option pp.privateNames true -/
/- set_option pp.maxSteps 100000 -/
#check ((@βtwist V).toTwistedCategoryStruct.twist)
#check _root_.Quotient

/- attribute [instance] βcat -/

/- attribute [instance] βcat -/
#check Quot
instance natMonoidalCategory : @MonoidalCategory (F V) natCategory where
  tensorObj X Y := X.tensor Y
  whiskerLeft X {Y₁ Y₂} := --let inst := βcat;
    Quotient.lift (⟦·.whiskerLeft X⟧) <| by
    rintro f g h
    simp
    induction h
    case swap L X₁ Y₁ s₁ x₁ M X₂ Y₂ s₂ x₂ R =>
      simp_all
      /- #check ⊢ -/
      /- simp only [Hom.whiskerLeft] -/

      /- simp -/
      repeat rw [unmk_braid_comp_assoc]
      repeat rw [unmk_braid_comp]
      -- TODO for 3/11: this is silly. Can we instead
      -- define and prove a functor from freeQuiver to
      -- NatDefinition? That will show that it's
      -- all the flavors of categories anyways, but we
      -- won't have to deal with the yucky stuff. We'll
      -- just have to define the Hom stuff (like Hom.whiskerLeft),
      -- then define the aux map from freeQuiver words to
      -- NatHom words, then show the aux map respects freeQuiver
      -- equalities: equivalent things in freeQuiver are
      -- equivalent in Nat. We already did our time in dealing
      -- with the yucky Nat equalities in the other functor
      -- definition; this time we have the opportunity to
      -- use them. I still don't understand why this seems easy,
      -- as we'll have to end up proving that this equality is
      -- respected anyways... We know Nat words X and Y are equivalent
      -- via swap. Map them via the functor fromNat, call whiskerLeft
      -- proper on them, and map them back. Then those things have to
      -- be equivalent, even if the composition of the functors isn't
      -- well-behaved... Ah, I see. The rule is the whiskerLeft one
      -- in HomEquiv, that states that equality is preserved by whiskerLeft.
      -- Since we plan on mapping whiskerLeft to whiskerLeft, we have to prove
      -- this exact lemma we're struggling with now. No shortcuts...
      --
      -- Okay then. Maybe the strategy is to get out of quotient land, and 
      -- go into Hom.Equiv land. Or maybe that'll make no difference...
      --
      -- Oh, now I remember! I wanted to change the swap rule so that it's
      -- more permissive: any non-twisting braid is good. Unclear what that
      -- really means in the quotient of all those relations, though. Maybe
      -- we don't have to put it on the quotient of the relations; maybe it's
      -- just that the word in the ⟦ ⟧ is non-twisting. Boy, it would be nice
      -- to have strictness and eqToHom back again for this...
      --
      -- Wait, no again! We'll just instantiate the rewrite rule, postulate that
      -- the goal's LHS is equal to the rewrite rule's LHS, prove it using the
      -- magical coherence tactic, and then they're swapped!
      -- issue: the added X by the whiskering has screwed up the association
      -- of the L ⊗ Y₁ ⊗ M stuff, so we need to use the layer rules to reassociate.
      -- likely, the play is to apply transitivity (quotient land (strict equality) is fine?)
      -- to make the RHS a hole, apply congrArg to locate just the layer we want to
      -- mess with, do some explicit rewriting (pray that the βcat is nice), and then
      -- zoom back out and reassociate/merge braids/simp.
      apply Eq.trans
      apply congrArg (_ ≫ ·)
      apply congrArg (_ ≫ ·)
      apply congrArg (_ ≫ ·)
      apply congrArg (· ≫ _)
      apply Quotient.sound
      -- Nat's new idea: screw natCategory. It's not a category, it's just a category-shaped
      -- thing.
      apply Hom.Equiv.layer
      apply Layer.Hom.freeLeft
      apply Quotient.mk
      exact (CategoryTheory.FreeTwistedCategory.Hom.α_inv _ _ _).comp <|
        (FreeTwistedCategory.Hom.whiskerRight (FreeTwistedCategory.Hom.α_inv _ _ _) _)
      simp
      repeat rw [unmk_braid_comp_assoc]
      repeat rw [unmk_braid_comp]

      apply Eq.trans
      apply congrArg (_ ≫ ·)
      apply congrArg (_ ≫ ·)
      apply congrArg (· ≫ _)
      apply congrArg
      apply congrArg
      apply Quotient.sound
      try rewrite [← βcat.assoc]
      try rewrite [βcat.assoc]
      rewrite [← Category.assoc]
      -- want to show this is equal to the middle of the swap thing, but alas, the instance
      -- synthesis is confused
      -- synthesis is confused
      -- synthesis is confused
      coherence
      simp
      apply Quotient.sound
      repeat rewrite [← Category.assoc]
      apply congrArg (· ≫ _)
      apply Quotient.sound
      apply Hom.
      apply Layer.Hom.freeRight
      apply Quotient.mk
      exact (CategoryTheory.FreeTwistedCategory.Hom.α_inv _ _ _).comp <|
        (FreeTwistedCategory.Hom.whiskerRight (FreeTwistedCategory.Hom.α_inv _ _ _) _).comp <|
        (FreeTwistedCategory.Hom.α_hom _ _ _)
      simp

      simp
      exact CategoryTheory.FreeTwistedCategory.Hom.α_inv (C := V) X (L * s₁ =>⋆ Y₁) M
      #check CategoryTheory.FreeTwistedCategory.Hom.α_hom
      refine (CategoryTheory.FreeTwistedCategory.Hom.id _).comp ?_
      exact (CategoryTheory.FreeTwistedCategory.Hom.α_inv _ _ _)
      /- let myβ := βcat -/
      /- #synth Category.{u, u} (F V) -/
      /- #check (@βtwist V).toTwistedCategoryStruct.twist -/
      refine ((@βtwist V).toTwistedCategoryStruct.twist _).inv ≫ ?_
      simp_all
      simp
      repeat rw [unmk_braid_comp_assoc]
      repeat rw [unmk_braid_comp]
      repeat1 rw [Category.assoc]
      repeat1 rw [unmk_braid_comp_assoc]
      simp
      simp_all
      simp at h
      rw [h]
      rw [unassoc_left]
      rw [rw_left (((@βtwist V).toTwistedCategoryStruct.twist) _).inv]


      simp
      rw [assoc_left]

      repeat1 rw [← Category.assoc]

      sorry
      /- apply congrArg₂ (@CategoryStruct.comp (F V) natCategory.toCategoryStruct ?dom ?middle ?cod) -/

      apply Quotient.sound
      constructor
      constructor
      constructor
      constructor
      constructor
      constructor
      apply Hom.Equiv.comp
      apply congrArg (⟦·⟧)
      /- refine congrArg₂ (@natCategory.comp _ _ _) sorry sorry -/
      /- sorry -/

      /- simp_all -/
      /- refine congrArg₂ (· ≫ ·) sorry sorry -/
      /- simp -/
      /- sorry -/
    all_goals sorry
    any_goals simp_all
    sorry

end NatDefinition

/-


-- hmmm... maybe it's easier to define this stuff on the quotient directly so we can work
-- with equality instead of ≈: congruence and rw/simp are automatic
@[grind]
lemma Hom.Equiv.whisker (X : N) {Y₁ Y₂ : N} {f f' : Y₁ ⟶ Y₂} (h : f ≈ f') (Z : N) : (Hom.whisker X f Z) ≈ (Hom.whisker X f' Z) := by
  induction h
  any_goals simp
  case swap =>
    -- reassociate
    -- merge the eqToHoms (whisker of eqToHom is an eqToHom)
    -- rewrite just the bit between the eqToHom with swap
    -- merge the eqToHoms again
    -- done!
    sorry
  any_goals constructor <;> done
  all_goals grind

@[grind]
lemma Hom.Equiv.whiskerLeft (X : N) {Y₁ Y₂ : N} {f f' : Y₁ ⟶ Y₂} (h : f ≈ f') :
    (Hom.whiskerLeft X f) ≈ (Hom.whiskerLeft X f') := by
  apply comp (refl _)
  apply comp ?_ (refl _)
  exact Hom.Equiv.whisker X h 1

@[grind]
lemma Hom.Equiv.whiskerRight {X₁ X₂ : N} (Y : N) {f f' : X₁ ⟶ X₂} (h : f ≈ f') :
    (Hom.whiskerRight f Y) ≈ (Hom.whiskerRight f' Y) :=
  Hom.Equiv.whisker 1 h Y

@[grind]
lemma Hom.Equiv.tensor {X₁ X₂ Y₁ Y₂ : N} {f f' : X₁ ⟶ Y₁} {g g' : X₂ ⟶ Y₂} : f ≈ f' → g ≈ g' →
    (Hom.tensor f g) ≈ (Hom.tensor f' g') := by
  intros hf hg
  constructor
  · exact Hom.Equiv.whiskerRight X₂ hf
  · exact Hom.Equiv.whiskerLeft Y₁ hg

@[grind]
lemma Hom.Equiv.star {X Y : N} {f f' : X ⟶ Y} (h : f ≈ f') :
    (Hom.star f) ≈ (Hom.star f') := by
  induction h
  any_goals simp
  any_goals constructor <;> done
  case swap =>
    -- probably similar to the swap case in whisker: merge eqToHom, swap, merge eqToHom
    sorry
  all_goals grind
  -- all_goals grind

-- -- Q for quotient -- the quotient of N
-- @[grind]
-- structure Q where
--   val : V

-- instance : Coe V Q where
--   coe v := ⟨v⟩

-- instance : Coe Q V where
--   coe n := n.val

-- @[ext]
-- lemma Q.ext {x y : N} : x.val = y.val → x = y := by
--   grind

#synth Quiver N
-- TODO generalize eqToHom_comp
lemma eqToHom_comp' {X Y Z : N} {f : X ⟶ Y} {g : Y ⟶ Z} {p : X = Y} {q : Y = Z} :
    (f ≈ eqToHom p) → (g ≈ eqToHom q) → (f ≫ g) ≈ (eqToHom (p.trans q)) := by
  intros hf hg
  apply Hom.Equiv.trans
  · exact Hom.Equiv.comp hf hg
  · cases p
    cases q
    simp
    grind

#check MonoidalCategory.whiskerRight

-- after checking out the moonoidal category definition, this equality is backwards
-- also maybe we should balance out the eqToHoms on either side
-- also why do we need this? It follows from monoidal stuff; we shouldn't NEED it for
-- defining monoidal, right?
-- @[simp, grind]
-- lemma Hom.Equiv.whisker_whisker (X₁ X₂ : N) {Y₁ Y₂ : N} (f : Hom Y₁ Y₂) (Z₁ Z₂ : N) :
--     Hom.whisker X₁ (Hom.whisker X₂ f Z₁) Z₂ ≈
--       eqToHom (by simp [mul_assoc]) ≫ Hom.whisker (X₁ * X₂) f (Z₁ * Z₂) ≫ eqToHom (by simp [mul_assoc]) := by
--   induction f
--   all_goals simp
--   -- case id =>
--   --   -- TODO this calls for reduction tactic
--   --   apply Hom.Equiv.symm
--   --   apply eqToHom_comp'
--   --   · apply Hom.Equiv.refl
--   --   · apply eqToHom_comp'
--   --     · apply Hom.Equiv.refl
--   --     · apply Hom.Equiv.refl
--   --     · rfl
--   case comp f g =>
--     apply Hom.Equiv.trans
--     · exact Hom.Equiv.comp f g
--     · simp
--       -- reassociate to get the inner eqToHom on the LHS next to each other
--       -- cancel (together, they're id)
--       -- rfl
--       sorry
--   case layer =>
--     -- merge the eqToHom on either side of the RHS
--     -- extensionality on the layer
--     -- mul_assoc
--     sorry
--   case braid =>
--     symm
--     -- trans
--     -- · symm
--     --   apply assoc
--     -- · trans
--     --   · apply Hom.Equiv.comp
--     --     ·
--     --       rename_i X _ a
--     --       apply eqToHom_braid (X' := X₁.val * (X₂.val * (X.val.val * Z₁.val) * Z₂.val)) ({ val := { val := X₁.val * X₂.val } } ◁ a ▷ { val := { val := Z₁.val * Z₂.val } })
--     --     · apply refl
--     --   · sorry
--     trans
--     · apply Hom.Equiv.comp
--       · apply Hom.Equiv.refl
--       · apply braid_eqToHom
--     · trans
--       · rename_i X _ b
--         apply eqToHom_braid ({ val := { val := X₁.val * X₂.val } } ◁ b ▷ { val := { val := Z₁.val * Z₂.val } } ≫ eqToHom _) (X₁.val * (X₂.val * (X.val.val * Z₁.val) * Z₂.val))
--       ·
--         apply braid
--         -- LHS: eqToHoms around a whisker of a
--         -- RHS: a composition of three
--         -- first: left whisker of associator
--         -- second: double whisker of a
--         -- third: left whisker of associator inv
--         -- simp [MonoidalCategory.whiskerRight]


--         -- for RHS first/third: unfold associator; whisker of an eqToHom is an eqToHom
--         -- probs need a general monoidal category rule about double whiskering

--         simp
--         sorry
--     -- apply braid
--     -- sorry

--   all_goals simp [Hom.whisker]
--   simp
--   sorry


-- #synth Category N

-- If S is a CategoryStruct on the quotient:
-- instance : Category obj :=
--   { S with
--     id_comp := -- your proof,
--     comp_id := -- your proof,
--     assoc := -- your proof
--   }

-- not necessary to define. If we want to, define and use the
-- mk_* lemmas
instance : MonoidalCategory (F V) where
  tensorObj X Y := X * Y
  tensorHom := Quotient.lift₂ (⟦Hom.tensor · ·⟧) <| by
    intros f₁ g₁ f₂ g₂ hf hg
    simp
    sorry

open TwistedCategory

instance : TwistedCategoryStruct (F V) where
  tensorObj X Y := X * Y
  tensorHom f g := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ Hom.Equiv.tensor hf hg) f g
  tensorUnit := 1
  whiskerLeft X {Y₁ Y₂} f :=
    Quotient.map (Hom.whiskerLeft X ·) (fun _ _ hf ↦ Hom.Equiv.whiskerLeft X hf) f
  whiskerRight {X₁ X₂} f Y :=
    Quotient.map (Hom.whiskerRight · Y) (fun _ _ hf ↦ Hom.Equiv.whiskerRight Y hf) f
  associator X Y Z := eqToIso (mul_assoc X Y Z)
  leftUnitor X := eqToIso (one_mul X)
  rightUnitor X := eqToIso (mul_one X)
  starObj X := X⋆
  starHom {X Y} f := Quotient.map Hom.star (fun _ _ hf ↦ Hom.Equiv.star hf) f
  skewator X Y := eqToIso (StarMonoid.star_mul Y X).symm
  involutor X := eqToIso (star_involutive X)
  twist X := { -- TODO it'd be nice to lift an isomorphism to another isomorphism
    hom := ⟦.braid (ς_ ⟨⟨X⟩⟩).hom⟧
    inv := ⟦.braid (ς_ ⟨⟨X⟩⟩).inv⟧
    hom_inv_id := by
      apply Quotient.sound
      simp
      trans
      · apply Hom.Equiv.merge_braid
      · simp
        rfl
    inv_hom_id := by
      apply Quotient.sound
      simp
      trans
      · apply Hom.Equiv.merge_braid
      · simp
        rfl
  }

-- next step: prefunctor between S V and N words that'll eventually be our isomorphism

-- -- not eqToIso' or eqToIso, but morally eqToIso'! TODO generalize eqToIso'
-- def eqToIso'' {X Y : N} (h : X = Y) : X ≅ Y := {
--   hom := ⟦eqToHom h⟧
--   inv := ⟦eqToHom h.symm⟧
--   hom_inv_id := by
--     apply Quotient.sound
--     exact eqToHom_comp' (by rfl) (by rfl)
--   inv_hom_id := by
--     apply Quotient.sound
--     exact eqToHom_comp' (by rfl) (by rfl)
-- }

-- #check FreeMonoidalCategory
-- def mymk :

-- maybe defining a MonoidalCategory N isn't worth it.
-- The end goal is to define a isomorphism between the categories
-- on S V and N
-- the natural isomorphisms are what's giving us trouble here, and
-- truly we don't care about that -- just map objects to objects,
-- morphisms to morphisms
-- first, just define it on the precategories: Hom to Hom

/-
-- TODO use ofTensorHom
#check ofTensorHom
instance : MonoidalCategory N where
  tensorObj X Y := X * Y
  tensorHom f g := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ Hom.Equiv.tensor hf hg) f g
  tensorUnit := 1
  associator X Y Z := eqToIso'' (mul_assoc X Y Z)
  leftUnitor X := eqToIso'' (one_mul X)
  rightUnitor X := eqToIso'' (mul_one X)
  whiskerLeft X {Y₁ Y₂} f := Quotient.map (Hom.whiskerLeft X ·) (fun _ _ hf ↦ Hom.Equiv.whiskerLeft X hf) f
  whiskerRight {X₁ X₂} f Y := Quotient.map (Hom.whiskerRight · Y) (fun _ _ hf ↦ Hom.Equiv.whiskerRight Y hf) f
  tensorHom_def {X₁ Y₁ X₂ Y₂} := by
    rintro ⟨f⟩ ⟨g⟩
    apply Quotient.sound
    simp
    -- -- rw [Quotient.map₂_mk]
    -- -- simp [Quotient]
    -- trans
    -- ·
    --   apply Quotient.sound
    --   simp
    --   rfl
    -- · trans Category.toCategoryStruct.comp (homMk (Hom.whiskerRight f X₂)) (homMk (Hom.whiskerLeft Y₁ g))
    --   · simp [CategoryStruct.comp]
    --   ·
    --     simp
    --     apply congrArg₂
    --     ·
    --       apply Quotient.sound
    --       sorry
    --     · sorry
        -- apply HomEquiv.tensorHom_def
  id_tensorHom_id _ _ := by
    apply Quotient.sound
    simp
    -- repeatedly merge eqToHom with (.braid 𝟙)
    sorry
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    apply Quotient.sound
    simp
    -- need to swap the f₂ and g₁ in the middle
    -- reassociate to get them next to each other
    -- casework on f₂ and g₁
    -- induction for the comp
    -- braids merge; use tensorHom_comp_tensorHom
    -- layers swap
    -- braid/layer is layer moves (HARD!!!)
    sorry
  whiskerLeft_id X Y := by
    apply Quotient.sound
    simp
    apply Hom.Equiv.trans
    · apply Hom.Equiv.comp
      · apply Hom.Equiv.refl
      · apply Hom.Equiv.id_comp
    · apply eqToHom_comp'
      · apply Hom.Equiv.refl
      · apply Hom.Equiv.refl
  id_whiskerRight X Y := by
    apply Quotient.sound
    simp
    rfl
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    apply Quotient.sound
    simp
    grind
  -- leftUnitor_naturality {X Y} := by
  --   rintro ⟨f⟩
  --   apply Quotient.sound
  --   grind
  -- rightUnitor_naturality {X Y} := by
  --   rintro ⟨f⟩
  --   apply Quotient.sound
  --   grind
  -- pentagon W X Y Z := by
  --   apply Quotient.sound
  --   eqToHom_eq_eqToHom
  -- triangle X Y := by
  --   apply Quotient.sound
  --   eqToHom_eq_eqToHom

-- then an isomorphism of categories between the one on N and the one on S V

#check Functor.Monoidal
-/
-/

