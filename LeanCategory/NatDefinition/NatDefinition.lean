import Mathlib
import LeanCategory.NatDefinition.Layer
import LeanCategory.FreeInvolutive.CoherenceTactic

namespace CategoryTheory.NatDefinition
open scoped Layer

variable {C : Type u}

/- notation "F" => CategoryTheory.FreeTwistedCategory -/

inductive Hom : N C → N C → Type (max (u + 2) v) where
  | layer : (l : Layer C) →
      Hom ⟨(l.boundary .Bottom)⟩ ⟨(l.boundary .Top)⟩
  | braid {X Y : N C} : (X.as ⟶T Y.as) → Hom X Y
  /- | id (X : N C) : Hom X X -- was just using braid's id, but -/
  /- -- ran into motive issues -/
  | comp {X Y Z : N C} : Hom X Y → Hom Y Z → Hom X Z

infixr:10 " ⟶n " => Hom

open CategoryTheory

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
/- def Hom.whisker (X : N C) {Y₁ Y₂ : N C} : (Y₁ ⟶n Y₂) → (Z : N C) → -/
/-     ((X * (Y₁ * Z)) ⟶n (X * (Y₂ * Z))) -/
/-   | .layer ⟨L, D, C, s, x, R⟩, Z => -/
/-     (Hom.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _).comp <| -/
/-     (Hom.layer ⟨X * L, D, C, s, x, R * Z⟩).comp -/
/-     (.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _) -/
/-   | .braid b, Z => Hom.braid (↑X ◁ b ▷ ↑Z) -/
/-   -- | .id Y, Z => 𝟙 (X * Y * Z) -/
/-   | .comp f g, Z => (whisker X f Z).comp (whisker X g Z) -/

/- #synth Quiver N -/

/- @[simp, grind] -/
@[simp]
def Hom.whiskerLeft (X : N C) {Y₁ Y₂ : N C} : (Y₁ ⟶n Y₂) → ((X.tensor Y₁) ⟶n (X.tensor Y₂))
  | .layer ⟨L, D, C, s, x, R⟩ =>
    (Hom.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _).comp <|
      (Hom.layer ⟨X.as ⊗ L, D, C, s, x, R⟩).comp
        (.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)
  | .braid b => Hom.braid (X.as ◁ b)
  | .comp f g => (f.whiskerLeft X).comp (g.whiskerLeft X)

@[simp]
def Hom.whiskerRight (X : N C) {Y₁ Y₂ : N C} : (Y₁ ⟶n Y₂) → ((Y₁.tensor X) ⟶n (Y₂.tensor X))
  | .layer ⟨L, D, C, s, x, R⟩ =>
    (Hom.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _).comp <|
      (Hom.layer ⟨L, D, C, s, x, R ⊗ X.as⟩).comp
        (.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)
  | .braid b => Hom.braid (b ▷ X.as)
  | .comp f g => (f.whiskerRight X).comp (g.whiskerRight X)

@[simp, grind]
def Hom.tensor {X₁ X₂ Y₁ Y₂ : N C} (f : X₁ ⟶n Y₁) (g : X₂ ⟶n Y₂) :
    (X₁.tensor X₂) ⟶n (Y₁.tensor Y₂) :=
  (f.whiskerRight X₂).comp (g.whiskerLeft Y₁)

@[simp]
def Hom.starHom {X Y : N C} : (X ⟶n Y) → (X.star ⟶n Y.star)
  /- | .id _ => .id _ -/
  | .layer ⟨L, X, Y, s, x, R⟩ =>
      (Hom.braid <| by simp [repeat_star_succ]; exact 𝟙 _ ⊗⋆≫ 𝟙 _).comp <|
        (Hom.layer ⟨R.star, X, Y, s+1, x, L.star⟩).comp <|
          (Hom.braid <| by simp [repeat_star_succ]; exact 𝟙 _ ⊗⋆≫ 𝟙 _)
  | .braid b => .braid b⋆
  | .comp f g => (f.starHom).comp g.starHom

@[grind]
inductive HomEquiv : ∀ {X Y : (N C)}, (X ⟶n Y) → (X ⟶n Y) → Prop where
  | refl (f) : HomEquiv f f
  | comp {f f' : X ⟶n Y} : HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
  /- | id_comp : HomEquiv ((Hom.id _).comp f) f -/
  /- | comp_id : HomEquiv (f.comp <| Hom.id _) f -/
  | id_comp : HomEquiv ((Hom.braid (𝟙 X)).comp f) f
  | comp_id {f : X ⟶n Y} : HomEquiv (f.comp (.braid (𝟙 Y.as))) f
  | assoc {f : _ ⟶n _} {g : _ ⟶n _} {h : _ ⟶n _} :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | merge_braid {b₁ : X ⟶T (Y)} {b₂ : (Y) ⟶T (Z)} :
      HomEquiv ((Hom.braid b₁).comp (.braid b₂)) (.braid (b₁ ≫ b₂))
  -- the paper's rules
  | swap : HomEquiv
      ((Hom.layer ⟨L, X₁, Y₁, s₁, x₁, M ⊗ (X₂^⋆s₂) ⊗ R⟩).comp
        ((Hom.braid (by pure_iso)).comp
        /- ((Hom.braid (by simp; exact 𝟙 (L ⊗ (Y₁^⋆s₁) ⊗ M ⊗ (X₂^⋆s₂) ⊗ R) ⊗⋆≫ 𝟙 (((L ⊗ Y₁^⋆s₁) ⊗ M) ⊗ (X₂^⋆s₂) ⊗ R))).comp -/
        ((Hom.layer ⟨(L ⊗ (Y₁^⋆s₁)) ⊗ M, X₂, Y₂, s₂, x₂, R⟩))))
      /- ((Hom.braid <| by simp; exact 𝟙 (L ⊗ (X₁^⋆s₁) ⊗ M ⊗ (X₂^⋆s₂) ⊗ R) ⊗⋆≫ 𝟙 (((L ⊗ X₁^⋆s₁) ⊗ M) ⊗ (X₂^⋆s₂) ⊗ R)).comp -/
      ((Hom.braid <| by pure_iso).comp
        ((Hom.layer ⟨(L ⊗ (X₁^⋆s₁)) ⊗ M, X₂, Y₂, s₂, x₂, R⟩).comp
          ((Hom.braid <| by pure_iso).comp
            ((Hom.layer ⟨L, X₁, Y₁, s₁, x₁, M ⊗ (Y₂^⋆s₂) ⊗ R⟩).comp
              (Hom.braid <| by pure_iso)))))
  | layer (f : l₁ ⟶l l₂) : HomEquiv
      /- ((Hom.layer l₁).comp (Hom.braid <| f.φ .Top)) -/
      /- ((Hom.braid <| f.φ .Bottom).comp (Hom.layer l₂)) -/
      (Hom.layer l₁)
      ((Hom.braid <| f.φ .Bottom).comp <|
        (Hom.layer l₂).comp <|
        (Hom.braid <| Groupoid.inv <| f.φ .Top))
  | symm (f g) : HomEquiv f g → HomEquiv g f
  | trans {f g h : X ⟶n Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h

/- def HomEquiv.swap_nice {L : N C} {x : L ⊗ Nat.repeat FreeTwistedCategory.star s₁ Y₁ ⊗ (M ⊗ Nat.repeat FreeTwistedCategory.star s₂ X₂) ⊗ R ⟶T -/
/-   ((L ⊗ Nat.repeat FreeTwistedCategory.star s₁ Y₁) ⊗ M) ⊗ Nat.repeat FreeTwistedCategory.star s₂ X₂ ⊗ R} (hx : x = (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) : HomEquiv -/
/-       ((Hom.layer ⟨L, X₁, Y₁, s₁, x₁, (M.tensor (s₂.repeat .star X₂)).tensor R⟩).comp -/
/-         ((Hom.braid x).comp -/
/-         ((Hom.layer ⟨(L.tensor (s₁.repeat .star Y₁)).tensor M, X₂, Y₂, s₂, x₂, R⟩)))) -/
/-       ((Hom.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _).comp -/
/-         ((Hom.layer ⟨(L.tensor (s₁.repeat .star X₁)).tensor M, X₂, Y₂, s₂, x₂, R⟩).comp -/
/-         ((Hom.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _).comp -/
/-         ((Hom.layer ⟨L, X₁, Y₁, s₁, x₁, (M.tensor (s₂.repeat .star Y₂)).tensor R⟩).comp -/
/-         (Hom.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _))))) := by -/
/-   rw [hx] -/
/-   exact HomEquiv.swap -/


/- instance {X Y : N C} : HasEquiv (Hom X Y) where -/
/-   Equiv := HomEquiv -/

/- instance {X Y : N C} : HasEquiv (X ⟶n Y) where -/
/-   Equiv := HomEquiv -/

/- attribute [grind →] HomEquiv.comp -/

/- @[grind =_] -/
/- lemma HomEquiv_def {X Y : N C} {f g : X ⟶n Y} : HomEquiv f g ↔ f ≈ g := by -/
/-   constructor -/
/-   all_goals intros h -/
/-   all_goals exact h -/

/- @[grind =_] -/
/- lemma HomEquiv_def' {X Y : N C} {f g : Hom X Y} : HomEquiv f g ↔ f ≈ g := by -/
/-   constructor -/
/-   all_goals intros h -/
/-   all_goals exact h -/

/- lemma HomEquiv.braid {X Y : N C} {b b' : X ⟶T Y} : -/
/-     b = b' → (Hom.braid b) ≈ (Hom.braid b') := by -/
/-   grind -/

instance mySetoidHom (X Y : N C) : Setoid (X ⟶n Y) :=
⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

instance : Category (N C) where
  Hom X Y := _root_.Quotient (mySetoidHom X Y)
  id X := ⟦Hom.braid (𝟙 X.as)⟧
  comp := Quotient.map₂ Hom.comp <| fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg
  comp_id := by
    rintro X Y ⟨f⟩
    exact _root_.Quotient.sound .comp_id
  id_comp := by
    rintro X Y ⟨f⟩
    exact _root_.Quotient.sound .id_comp
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact _root_.Quotient.sound .assoc

@[simp]
def homMk {X Y : N C} (f : X ⟶n Y) : X ⟶ Y := ⟦f⟧

@[simp]
theorem mk_id {X : N C} : ⟦.braid (𝟙 X.as)⟧ = 𝟙 X :=
  rfl

@[simp]
theorem mk_comp {X Y Z : N C} (f : X ⟶n Y) (g : Y ⟶n Z) :
    ⟦Hom.comp f g⟧ = @CategoryStruct.comp (N C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

open FreeTwistedCategory
/- def mkLayer (L : N C) {X Y : N C} (s : ℕ) (x : X.as ⟶ Y.as) (R : N C) : -/
/-     L.tensor ((X^⋆s).tensor R) ⟶ L.tensor ((Y^⋆s).tensor R) := ⟦Hom.layer ⟨L, X, Y, s, x, R⟩⟧ -/
/- def mkLayer (L : T C) {X Y : T C} (s : ℕ) (x : X ⟶ Y) (R : T C) : -/
/-     ⟨L.as ⊗ (X^⋆s).as ⊗ R.as⟩ ⟶ L.tensor ((Y^⋆s).tensor R) := ⟦Hom.layer ⟨L, X, Y, s, x, R⟩⟧ -/
def mkLayer (L : FreeTwistedCategory C) {X Y : T C} (s : ℕ) (x : X ⟶ Y) (R : FreeTwistedCategory C) :
    (mk <| L ⊗ (X^⋆s) ⊗ R ) ⟶ ⟨L ⊗ (Y^⋆s) ⊗ R⟩ := ⟦Hom.layer ⟨L, X, Y, s, x, R⟩⟧

@[simp]
theorem mk_layer {L : T C} {x : X ⟶ Y} : ⟦.layer ⟨L, X, Y, s, x, R⟩⟧ = mkLayer L s x R :=
  rfl

def mkBraid {X Y : N C} (b : X.as ⟶ Y.as) : X ⟶ Y := ⟦Hom.braid b⟧

@[simp]
theorem mk_braid {X Y : N C} {b : X.as ⟶ Y.as} : ⟦.braid b⟧ = mkBraid b :=
  rfl

@[simp]
theorem mkBraid_id {X : N C} : mkBraid (𝟙 X.as) = 𝟙 X :=
  rfl

@[simp]
theorem mkBraid_id' : mkBraid (𝟙 X) = 𝟙 (mk X) :=
  rfl

@[simp]
theorem unmk_braid_comp {X Y Z : N C} (f : X.as ⟶ Y.as) (g : Y.as ⟶ Z.as) :
     mkBraid f ≫ mkBraid g = mkBraid (f ≫ g) := by
  apply _root_.Quotient.sound
  constructor

@[simp]
theorem unmk_braid_comp_assoc {W X Y Z : N C} (f : W.as ⟶ X.as) (g : X.as ⟶ Y.as) (h : Y ⟶ Z) :
     mkBraid f ≫ mkBraid g ≫ h = mkBraid (f ≫ g) ≫ h := by
  rw [← Category.assoc]
  apply congrArg (· ≫ _)
  simp

lemma twist_inv_conjugation {L : T C} :
    /- ⟦.layer ⟨L, _, _, s, x, R⟩⟧ = mkBraid (L.as ◁ (ς_ _).inv ▷ R) ≫ -/
    /-   ⟦.layer ⟨L, _, _, s + 1, x, R⟩⟧ ≫ mkBraid (L.as ◁ (ς_ _).hom ▷ R.as) := by -/
    mkLayer L s x R = mkBraid (L ◁ (ς_ _).inv ▷ R) ≫
      mkLayer L (s + 1) x R ≫ mkBraid (L ◁ (ς_ _).hom ▷ R) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      exact Layer.Hom.twist_inv
  rfl

lemma twist_hom_conjugation_forced {L : T C} {x : X ⟶ Y} :
    mkLayer L s x R = mkBraid (L ◁ ((e_ _).inv ≫ (ς_ _).hom) ▷ R) ≫
      mkLayer L (s + 1) x R ≫ mkBraid (L ◁ ((ς_ _).inv ≫ (e_ _).hom) ▷ R) := by
    /- ⟦.layer ⟨L, _, _, s + 1, x, R⟩⟧ = mkBraid (L.as ◁ (ς_ _).hom ▷ R.as) ≫ -/
    /-   ⟦.layer ⟨L, _, _, s, x, R⟩⟧ ≫ mkBraid (L.as ◁ (ς_ _).inv ▷ R.as) := by -/
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      exact Layer.Hom.comp Layer.Hom.ε_inv Layer.Hom.twist_hom
  simp
  simp [repeat_star_succ]

lemma twist_hom_conjugation {L : T C} :
    mkLayer L (s + 1) x R = mkBraid (L ◁ (ς_ _).hom ▷ R) ≫
      mkLayer L s x R ≫ mkBraid (L ◁ (ς_ _).inv ▷ R) := by
    /- ⟦.layer ⟨L, _, _, s + 1, x, R⟩⟧ = mkBraid (L.as ◁ (ς_ _).hom ▷ R.as) ≫ -/
    /-   ⟦.layer ⟨L, _, _, s, x, R⟩⟧ ≫ mkBraid (L.as ◁ (ς_ _).inv ▷ R.as) := by -/
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      exact Layer.Hom.twist_hom
  rfl

lemma strand_box_hom_conjugation {L : T C} {x : X ⟶ Y} :
    mkLayer (L ⊗ A) s x R =
      mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L ◁ (σ_ A (X^⋆s)).hom ▷ R ⊗⋆≫ 𝟙 _)) ≫
        mkLayer L s x (A ⊗ R) ≫
          mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L ◁ (σ_ A (Y^⋆s)).inv ▷ R ⊗⋆≫ 𝟙 _)) := by
    /- ⟦.layer ⟨L.tensor A, X, Y, s, x, R⟩⟧ =  -/
    /-   mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L.as ◁ (σ_ A.as (X^⋆s).as).hom ▷ R.as ⊗⋆≫ 𝟙 _)) ≫ -/
    /-     ⟦.layer ⟨L, _, _, s, x, A.tensor R⟩⟧ ≫ -/
    /-       mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L.as ◁ (σ_ A.as (Y^⋆s).as).inv ▷ R.as ⊗⋆≫ 𝟙 _)) := by -/
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.strand_box_hom
  simp [involutiveComp]

lemma strand_box_inv_conjugation {L : T C} {x : X ⟶ Y} :
    mkLayer L s x (A ⊗ R) = mkBraid (𝟙 _ ⊗⋆≫ L ◁ (σ_ A (X^⋆s)).inv ▷ R ⊗⋆≫ 𝟙 _) ≫
      mkLayer (L ⊗ A) s x R ≫
        mkBraid (𝟙 _ ⊗⋆≫ L ◁ (σ_ A (Y^⋆s)).hom ▷ R ⊗⋆≫ 𝟙 _) := by
    /- ⟦.layer ⟨L, X, Y, s, x, A.tensor R⟩⟧ =  -/
    /-   mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L.as ◁ (σ_ A.as (X^⋆s).as).inv ▷ R.as ⊗⋆≫ 𝟙 _)) ≫ -/
        /- ⟦.layer ⟨L.tensor A, _, _, s, x, R⟩⟧ ≫ -/
        /-   mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L.as ◁ (σ_ A.as (Y^⋆s).as).hom ▷ R.as ⊗⋆≫ 𝟙 _)) := by -/
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.strand_box_inv
  simp [involutiveComp]

lemma box_strand_hom_conjugation {L : T C} {x : X ⟶ Y} :
    mkLayer L s x (A ⊗ R) = mkBraid (𝟙 _ ⊗⋆≫ L ◁ (σ_ (X^⋆s) A).hom ▷ R ⊗⋆≫ 𝟙 _) ≫
      mkLayer (L ⊗ A) s x R ≫
        mkBraid (𝟙 _ ⊗⋆≫ L ◁ (σ_ (Y^⋆s) A).inv ▷ R ⊗⋆≫ 𝟙 _) := by
    /- ⟦.layer ⟨L, X, Y, s, x, A.tensor R⟩⟧ =  -/
    /-   mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L.as ◁ (σ_ (X^⋆s).as A.as).hom ▷ R.as ⊗⋆≫ 𝟙 _)) ≫ -/
    /-     ⟦.layer ⟨L.tensor A, _, _, s, x, R⟩⟧ ≫ -/
    /-       mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L.as ◁ (σ_ (Y^⋆s).as A.as).inv ▷ R.as ⊗⋆≫ 𝟙 _)) := by -/
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.box_strand_hom
  simp [involutiveComp]

lemma box_strand_inv_conjugation {L : T C} {x : X ⟶ Y} :
    /- ⟦.layer ⟨L ⊗ A, X, Y, s, x, R⟩⟧ =  -/
    /-   mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L ◁ (σ_ (X^⋆s) A).inv ▷ R ⊗⋆≫ 𝟙 _)) ≫ -/
    /-     ⟦.layer ⟨L, _, _, s, x, A ⊗ R⟩⟧ ≫ -/
    /-       mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L ◁ (σ_ (Y^⋆s) A).hom ▷ R ⊗⋆≫ 𝟙 _)) := by -/
    mkLayer (L ⊗ A) s x R =
      mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L ◁ (σ_ (X^⋆s) A).inv ▷ R ⊗⋆≫ 𝟙 _)) ≫
        mkLayer L s x (A ⊗ R) ≫
          mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ L ◁ (σ_ (Y^⋆s) A).hom ▷ R ⊗⋆≫ 𝟙 _)) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.box_strand_inv
  simp [involutiveComp]

@[simp]
lemma associator_conjugation_left {L₁ L₂ : T C} :
    /- ⟦.layer ⟨L₁.tensor (L₂.tensor L₃), _, _, s, x, R⟩⟧ =  -/
    /-   mkBraid ((α_ _ _ _).inv ▷ _) ≫ -/
    /-     ⟦.layer ⟨(L₁.tensor L₂).tensor L₃, _, _, s, x, R⟩⟧ ≫ -/
    /-       mkBraid ((α_ _ _ _).hom ▷ _) := by -/
      mkLayer (L₁ ⊗ (L₂ ⊗ L₃)) s x R =
        mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) ≫
          mkLayer ((L₁ ⊗ L₂) ⊗ L₃) s x R ≫
            mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) := by
    /- ⟦.layer ⟨L₁.tensor (L₂.tensor L₃), _, _, s, x, R⟩⟧ =  -/
      /- mkBraid ((α_ _ _ _).inv ▷ _) ≫ -/
      /-   ⟦.layer ⟨(L₁.tensor L₂).tensor L₃, _, _, s, x, R⟩⟧ ≫ -/
      /-     mkBraid ((α_ _ _ _).hom ▷ _) := by -/
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeLeft
      exact (α_ _ _ _).inv
  simp [involutiveComp]

@[simp]
lemma associator_conjugation_right {R₁ L : T C} :
    mkLayer L s x ((R₁ ⊗ R₂) ⊗ R₃) =
      mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) ≫
        mkLayer L s x (R₁ ⊗ (R₂ ⊗ R₃)) ≫
          mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) := by
    /- ⟦.layer ⟨L, _, _, s, x, ((R₁.tensor R₂).tensor R₃)⟩⟧ = -/
    /-   mkBraid (_ ◁ _ ◁ (α_ _ _ _).hom) ≫ -/
    /-     ⟦.layer ⟨L, _, _, s, x, (R₁.tensor (R₂.tensor R₃))⟩⟧ ≫ -/
    /-       mkBraid (_ ◁ _ ◁ (α_ _ _ _).inv) := by -/
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeRight
      exact (α_ _ _ _).hom
  simp [involutiveComp]

@[simp]
lemma involutor_conjugation {L : T C} :
    /- ⟦.layer ⟨L, _, _, s + 2, x, R⟩⟧ = -/
    /-   mkBraid (_ ◁ (e_ _).hom ▷ _) ≫ -/
    /-     ⟦.layer ⟨L, _, _, s, x, R⟩⟧ ≫ -/
    /-       mkBraid (_ ◁ (e_ _).inv ▷ _) := by -/
    mkLayer L (s + 2) x  R =
      mkBraid (_ ◁ (e_ _).hom ▷ _) ≫
        mkLayer L s x R ≫
          mkBraid (_ ◁ (e_ _).inv ▷ _) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      exact Layer.Hom.ε_hom
  simp

lemma braid_conjugation_left {L₁ L₂ : T C} (b : L₁ ⟶ L₂) :
    /- ⟦.layer ⟨L₁, _, _, s, x, R⟩⟧ = -/
    /-   mkBraid (b ▷ (_ ⊗ _)) ≫ -/
    /-     ⟦.layer ⟨L₂, _, _, s, x, R⟩⟧ ≫ -/
    /-       mkBraid (inv b ▷ (_ ⊗ _)) := by -/
    mkLayer L₁ s x R =
      mkBraid (b ▷ (_ ⊗ _)) ≫
        mkLayer L₂ s x R ≫
          mkBraid (inv b ▷ (_ ⊗ _)) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeLeft
      exact b
  simp

lemma braid_conjugation_right {R₁ R₂ : T C} (b : R₁ ⟶ R₂) :
    mkLayer L s x R₁ =
      mkBraid (_ ◁ _ ◁ b) ≫
        mkLayer L s x R₂ ≫
          mkBraid (_ ◁ _ ◁ inv b) := by
    /- ⟦.layer ⟨L, _, _, s, x, R₁⟩⟧ = -/
    /-   mkBraid (_ ◁ _ ◁ b) ≫ -/
    /-     ⟦.layer ⟨L, _, _, s, x, R₂⟩⟧ ≫ -/
    /-       mkBraid (_ ◁ _ ◁ inv b) := by -/
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeRight
      exact b
  simp

lemma stripBraidLeft {X Y : N C} {b : X.as ⟶ Y.as} {f : Y ⟶ Z} {g : X ⟶ Z} :
    ⟦(Hom.braid b)⟧ ≫ f = g → f = ⟦(Hom.braid (inv b))⟧ ≫ g := by
  intros h
  trans (⟦Hom.braid (inv b)⟧ ≫ (⟦Hom.braid b⟧ ≫ f))
  · simp
  · rw [h]

lemma stripBraidRight {X Y : N C} {b : Y.as ⟶ Z.as} {f : X ⟶ Y} {g : X ⟶ Z} :
    f ≫ mkBraid b = g → f = g ≫ mkBraid (inv b) := by
  intros h
  trans ((f ≫ ⟦Hom.braid b⟧) ≫ ⟦Hom.braid (inv b)⟧)
  · simp
  · simp only [mk_braid]; rw [h]

lemma stripBraid {W X Y Z : N C} {b₁ : W.as ⟶ X.as} {f : X ⟶ Y} {b₂ : Y.as ⟶ Z.as} {g : W ⟶ Z} :
    mkBraid b₁ ≫ f ≫ mkBraid b₂ = g → f = mkBraid (inv b₁) ≫ g ≫ mkBraid (inv b₂) := by
  intros h
  have h := stripBraidLeft h
  have h := stripBraidRight h
  simp at h
  exact h

def HomEquiv.swap_nice' {L : T C} {x₁ : X₁ ⟶ Y₁} {x₂ : X₂ ⟶ Y₂} {x : _ ⟶T _} (hx : x = (by pure_iso)) :
    (mkLayer L s₁ x₁ (M ⊗ (X₂^⋆s₂) ⊗ R)) ≫
      (mkBraid x) ≫
        (mkLayer ((L ⊗ (Y₁^⋆s₁)) ⊗ M) s₂ x₂ R) =
    (mkBraid (by pure_iso)) ≫
      (mkLayer ((L ⊗ (X₁^⋆s₁)) ⊗ M) s₂ x₂ R) ≫
        (mkBraid (by pure_iso)) ≫
          (mkLayer L s₁ x₁ (M ⊗ (Y₂^⋆s₂) ⊗ R)) ≫
            (mkBraid (by pure_iso)) := by
  rw [hx]
  clear x hx
  simp_all
  have hrw :=
    @_root_.Quotient.sound _ (mySetoidHom _ _) _ _ <|
      HomEquiv.swap (L := L) (M := M) (R := R) (s₁ := s₁) (s₂ := s₂) (x₁ := x₁) (x₂ := x₂)
  simp at hrw
  rw [hrw]

def HomEquiv.swap_nice''' {L : N C} {x₁ : X₁ ⟶ Y₁} {x₂ : X₂ ⟶ Y₂} {x : _ ⟶T _} (hx : x = (by simp; pure_iso)) :
    (mkLayer L s₁ x₁ (M ⊗ (s₂.repeat .star X₂) ⊗ R)) ≫
      (mkBraid x) ≫
      (mkLayer ((L ⊗ (s₁.repeat .star Y₁)) ⊗ M) s₂ x₂ R) =
    (mkBraid (by simp; pure_iso)) ≫
    (mkLayer ((L ⊗ (s₁.repeat .star X₁)) ⊗ M) s₂ x₂ R) ≫
      (mkBraid (by simp; pure_iso)) ≫
      (mkLayer L s₁ x₁ (M ⊗ ((s₂.repeat .star Y₂) ⊗ R))) ≫
      (mkBraid (by simp; pure_iso)) := by
  rw [hx]
  clear x hx
  simp_all
  have hrw :=
    @Quotient.sound _ (mySetoidHom _ _) _ _ <|
      HomEquiv.swap (L := L) (M := M) (R := R) (s₁ := s₁) (s₂ := s₂) (x₁ := x₁) (x₂ := x₂)
  simp at hrw
  have hrw := stripBraidLeft hrw
  simp at hrw
  repeat1 rw [← whiskerLeft_comp_assoc] at hrw
  repeat1 rw [← whiskerLeft_comp] at hrw
  repeat1 rw [Iso.inv_hom_id] at hrw
  simp at hrw
  rw [hrw]

-- it helps the real category and our "category" play nice to NOT
-- have separate definitions for objects (TODO make sure it's similar
-- with the star)
/- def tensorObj : N C → N C → N C := (· ⊗ ·) -/
/- scoped infixr:70 " ⊗N " => tensorObj -/


lemma my_silly {X Y Z : N C} (f₁ f₂ : X ⟶ Y) (g₁ g₂ : Y ⟶ Z) : f₁ ≫ g₁ = f₂ ≫ g₂ :=
  sorry

macro "handle_braid_step" : tactic =>
  `(tactic|
    first
      | rfl -- just non-pures
      | apply congrArg₂ _ rfl -- starting w/ impure
      | (apply Eq.trans ((Category.comp_id _).symm) ; apply congrArg₂ _ rfl) -- f = f ≫ pure-coherent
      | liftable_prefixes; apply congrArg₂ _ (by coherence) -- starting w/ Braid
      | coherence -- just braids
      | fail "IDK what to do -- braid step")

-- call on braids, not mkBraid of the braids
macro "handle_braid" : tactic =>
  `(tactic|
    first
      | simp [involutiveComp, repeat_star_succ]; done
      | (try simp [involutiveComp, repeat_star_succ]); repeat1 handle_braid_step)

macro "my_coherence_step" : tactic =>
  `(tactic|
    first
      | rfl -- just Layer
      | apply congrArg₂ _ (congrArg _ (by handle_braid)) -- starting w/ Braid
      | apply congrArg₂ _ rfl -- starting w/ Layer
      | apply congrArg _ <| by handle_braid -- just Braid
      | fail "IDK what to do"
  )

macro "my_coherence" : tactic =>
  `(tactic|
    first
      | simp [involutiveComp, repeat_star_succ]; done
      | (try simp [involutiveComp, repeat_star_succ]); repeat1 my_coherence_step
  )

open Layer
open scoped Layer
def HomEquiv.swap_nice'''' {L : T C} {x₁ : X₁ ⟶ Y₁} {x₂ : X₂ ⟶ Y₂} {x : L ⊗ (Y₁^⋆s₁) ⊗ (M ⊗ (X₂^⋆s₂) ⊗ R) ⟶T ((L ⊗ (Y₁^⋆s₁)) ⊗ M) ⊗ (X₂^⋆s₂) ⊗ R} (hx : x = 𝟙 (L ⊗ (Y₁^⋆s₁) ⊗ (M ⊗ (X₂^⋆s₂) ⊗ R)) ⊗⋆≫ 𝟙 (((L ⊗ (Y₁^⋆s₁)) ⊗ M) ⊗ (X₂^⋆s₂) ⊗ R)) :
    mkLayer L s₁ x₁ (M ⊗ (X₂^⋆s₂) ⊗ R) ≫
      mkBraid x ≫
        mkLayer ((L ⊗ (Y₁^⋆s₁)) ⊗ M) s₂ x₂ R =
    mkBraid (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _) ≫
      mkLayer ((L ⊗ (X₁^⋆s₁)) ⊗ M) s₂ x₂ R ≫
        mkBraid (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _) ≫
          mkLayer L s₁ x₁ (M ⊗ (Y₂^⋆s₂) ⊗ R) ≫
            mkBraid (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 (((L ⊗ (Y₁^⋆s₁)) ⊗ M) ⊗ (Y₂^⋆s₂) ⊗ R)) 
            := by
    /- (mkLayer L s₁ x₁ (M ⊗ (X₂^⋆s₂) ⊗ R)) ≫ -/
    /-   (mkBraid x) ≫ -/
    /-   (mkLayer ((L ⊗ (Y₁^⋆s₁)) ⊗ M) s₂ x₂ R) = -/
    /- (mkBraid (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) ≫ -/
    /- (mkLayer ((L ⊗ (X₁^⋆s₁)) ⊗ M) s₂ x₂ R) ≫ -/
    /-   (mkBraid (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) ≫ -/
    /-   (mkLayer L s₁ x₁ (M ⊗ ((Y₂^⋆s₂) ⊗ R))) ≫ -/
    /-   (mkBraid (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) := by -/
  rw [hx]
  clear x hx
  simp_all
  #check @HomEquiv.swap
  /- #check @HomEquiv.swap C L _ _ s₁ x₁ M R _ _ s₂ x₂ -/
  have hrw := @HomEquiv.swap C L X₁ Y₁ s₁ x₁ M s₂ X₂ R Y₂ x₂
  #check @_root_.Quotient.sound
  have hrw := @_root_.Quotient.sound _ (mySetoidHom _ _) _ _ <| hrw
  simp at hrw
  /- have hrw := stripBraidLeft hrw -/
  /- simp at hrw -/
  simp [involutiveComp] at hrw ⊢
  /- repeat1 rw [← whiskerLeft_comp_assoc] at hrw -/
  /- repeat1 rw [← whiskerLeft_comp] at hrw -/
  /- repeat1 rw [Iso.inv_hom_id] at hrw -/
  /- simp at hrw -/
  rw [hrw]
  my_coherence
      /- HomEquiv.swap (L := L) (M := M) (R := R) (s₁ := s₁) (s₂ := s₂) (x₁ := x₁) (x₂ := x₂) -/

def swap_nice'' {L : T C} {X : N C} {x₁ : X₁ ⟶ Y₁} {x₂ : X₂ ⟶ Y₂} {s₁ s₂ : ℕ} :
    mkLayer (X.as ⊗ L) s₁ x₁ (M ⊗ (X₂^⋆s₂) ⊗ R) ≫
      mkBraid (𝟙 ((X.as ⊗ L) ⊗ (Y₁^⋆s₁) ⊗ M ⊗ (X₂^⋆s₂) ⊗ R) ⊗⋆≫ 𝟙 ((((X.as ⊗ L) ⊗ Y₁^⋆s₁) ⊗ M) ⊗ (X₂^⋆s₂) ⊗ R)) ≫
        mkLayer (((X.as ⊗ L) ⊗ Y₁^⋆s₁) ⊗ M) s₂ x₂ R =
    mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) ≫
      mkLayer (((X.as ⊗ L) ⊗ X₁^⋆s₁) ⊗ M) s₂ x₂ R ≫
        mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) ≫
          mkLayer (X.as ⊗ L) s₁ x₁ (M ⊗ (Y₂^⋆s₂) ⊗ R) ≫
            mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) := sorry
  /- mkLayer (X.as ⊗ L) s₁ x₁ (M ⊗ (Y₂^⋆X₂) ⊗ s₂) ≫ -/
  /-     mkBraid (𝟙 ((X.as ⊗ L) ⊗ (Y₁^⋆s₁) ⊗ M ⊗ (Y₂^⋆X₂) ⊗ s₂) ⊗⋆≫ 𝟙 ((((X.as ⊗ L) ⊗ Y₁^⋆s₁) ⊗ M) ⊗ (Y₂^⋆X₂) ⊗ s₂)) ≫ -/
  /-       mkLayer (((X.as ⊗ L) ⊗ Y₁^⋆s₁) ⊗ M) X₂ R s₂ = -/


set_option maxHeartbeats 10000000 in -- big simp_all
def whiskerLeft (X : N C) {Y₁ Y₂ : N C} (f : Y₁ ⟶ Y₂) : (X.tensor Y₁ ⟶ X.tensor Y₂) := --by
  Quotient.liftOn f (⟦·.whiskerLeft X⟧) <| by
    clear f
    rintro f g h
    simp
    induction h <;> simp_all
    case layer l₁ l₂ f =>
      induction f
      case comp ih₁ ih₂ =>
        simp at ih₁ ih₂ ⊢
        have ih₁ := stripBraid ih₁
        have ih₂ := stripBraid ih₂
        rw [ih₁, ih₂]
        my_coherence
      all_goals simp_all
      case freeLeft L₁ X' Y s x R L₂ b =>
        rw [braid_conjugation_left (X.as ◁ b)]
        my_coherence
      case freeRight b =>
        rw [braid_conjugation_right b]
        my_coherence
      case box_strand_hom =>
        rw [box_strand_hom_conjugation]
        my_coherence
      case box_strand_inv L X' Y s R A x =>
        rw [box_strand_inv_conjugation]
        my_coherence
      case strand_box_hom =>
        rw [strand_box_hom_conjugation]
        my_coherence
      case strand_box_inv =>
        rw [strand_box_inv_conjugation]
        my_coherence
      case twist_hom =>
        rw [twist_hom_conjugation]
        my_coherence
      case twist_inv =>
        rw [twist_inv_conjugation]
        my_coherence
      case ε_hom =>
        my_coherence
      case ε_inv =>
        my_coherence
    case swap L X₁ Y₁ s₁ x₁ M s₂ X₂ R Y₂ x₂ =>
      rewrite [braid_conjugation_left ((α_ _ _ _).inv ▷ _)]
      simp
      apply Eq.trans
      case h₁ =>
        apply congrArg (_ ≫ ·)
        repeat rewrite [← Category.assoc]
        apply congrArg (· ≫ _)
        · simp
          apply HomEquiv.swap_nice'
          handle_braid
      simp
      rewrite [braid_conjugation_left ((α_ _ _ _).inv ▷ _)]
      my_coherence

set_option maxHeartbeats 10000000 in -- big simp_all
def whiskerRight {X₁ X₂ : N C} (f : X₁ ⟶ X₂) (Y : N C) : (X₁.tensor Y ⟶ X₂.tensor Y) := --by
  Quotient.liftOn f (⟦·.whiskerRight Y⟧) <| by
    clear f
    rintro f g h
    simp
    induction h <;> simp_all
    case layer l₁ l₂ f =>
      induction f
      case comp ih₁ ih₂ =>
        simp at ih₁ ih₂ ⊢
        have ih₁ := stripBraid ih₁
        have ih₂ := stripBraid ih₂
        rw [ih₁, ih₂]
        my_coherence
      all_goals simp_all
      case freeLeft L₁ X' Y s x R L₂ b =>
        rw [braid_conjugation_left b]
        my_coherence
      case freeRight b =>
        rw [braid_conjugation_right (b ▷ Y.as)]
        my_coherence
      case box_strand_hom =>
        rw [box_strand_hom_conjugation]
        my_coherence
      case box_strand_inv L X' Y s R A x =>
        rw [box_strand_inv_conjugation]
        my_coherence
      case strand_box_hom =>
        rw [strand_box_hom_conjugation]
        my_coherence
      case strand_box_inv =>
        rw [strand_box_inv_conjugation]
        my_coherence
      case twist_hom =>
        rw [twist_hom_conjugation]
        my_coherence
      case twist_inv =>
        rw [twist_inv_conjugation]
        my_coherence
      case ε_hom =>
        my_coherence
      case ε_inv =>
        my_coherence
    case swap L X₁ Y₁ s₁ x₁ M s₂ X₂ R Y₂ x₂ =>
      rewrite [braid_conjugation_right (_ ◁ (α_ _ _ _).hom)]
      simp
      apply Eq.trans
      case h₁ =>
        apply congrArg (_ ≫ ·)
        repeat rewrite [← Category.assoc]
        apply congrArg (· ≫ _)
        · simp
          apply HomEquiv.swap_nice'
          handle_braid
      simp
      rewrite [braid_conjugation_right (_ ◁ (α_ _ _ _).inv)]
      my_coherence

#check whiskerLeft


set_option maxHeartbeats 10000000 in -- big simp_all
def whiskerRight  {Y₁ Y₂ : N C} (f : Y₁ ⟶ Y₂) (X : N C) : (Y₁ ⊗ X ⟶ Y₂ ⊗ X) := --by
  Quotient.liftOn f (⟦·.whiskerRight X⟧) <| by
    clear f
    rintro f g h
    simp
    induction h <;> simp_all
    case layer l₁ l₂ f =>
      induction f
      case comp ih₁ ih₂ =>
        have ih₂ := stripBraid ih₂
        simp_all
      all_goals simp_all
      case freeLeft b =>
        rw [Layer_braid_conjugation_left b]
        my_coherence
      case freeRight b =>
        rw [Layer_braid_conjugation_right (b ▷ _)]
        my_coherence
      case box_strand_hom =>
        rw [Layer_box_strand_inv_conjugation]
        my_coherence
      case box_strand_inv =>
        rw [Layer_box_strand_hom_conjugation]
        my_coherence
      case strand_box_hom =>
        rw [Layer_strand_box_inv_conjugation]
        my_coherence
      case strand_box_inv =>
        rw [Layer_strand_box_hom_conjugation]
        my_coherence
      case twist_hom =>
        rw [Layer_twist_inv_conjugation]
        my_coherence
      case twist_inv =>
        rw [Layer_twist_hom_conjugation_forced]
        my_coherence
      case ε_inv =>
        -- monoidal coherence doesn't like the involutor
        -- we'll do it ourselves
        repeat rw [← whiskerLeft_comp_assoc]
        repeat rw [Category.assoc]
        repeat rw [← comp_whiskerRight]
        my_coherence
    case swap L X₁ Y₁ s₁ x₁ M X₂ Y₂ s₂ x₂ R =>
      -- forget about the final braid (so we can apply swap_nice w/o assoc):
      apply Eq.trans
      · repeat rewrite [← assoc]
        apply congrArg (· ≫ _)
        · simp

          -- do the swap:
          rw [HomEquiv.swap_nice' (by coherence)]

      -- simp up; simp doesn't handle rewriting internal monoidal stuff
      my_coherence


/-
macro "my_coherence_step" : tactic =>
  `(tactic|
    first
      | rfl -- just Layer
      | apply congrArg _ <| by coherence -- just Braid
      | apply congrArg₂ _ (congrArg _ (by coherence)) -- starting w/ Braid
      | apply congrArg₂ _ rfl -- starting w/ Layer
      | fail "IDK what to do"
  )

macro "my_coherence" : tactic =>
  `(tactic|
    first
      | simp ; done
      | ((try simp) ; (repeat1 my_coherence_step))
  )
-/

@[simp]
lemma skewator_conjugation_left {L₁ L₂ : T C} :
      mkLayer (L₁ ⊗ L₂)⋆ s x R =
        mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) ≫
          mkLayer (L₂⋆ ⊗ L₁⋆) s x R ≫
            mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeLeft
      exact (χ_ _ _).inv
  simp [involutiveComp]

@[simp]
lemma skewator_conjugation_right {L : T C} :
      mkLayer L s x (R₁ ⊗ R₂)⋆ =
        mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) ≫
          mkLayer L s x (R₂⋆ ⊗ R₁⋆) ≫
            mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeRight
      exact (χ_ _ _).inv
  simp [involutiveComp]

def HomEquiv.swap_nice_starred' {L : T C} {x₁ : X₁ ⟶ Y₁} {x₂ : X₂ ⟶ Y₂} {x : _ ⟶T _} (hx : x = (by pure_iso)) :
    (mkLayer L (s₁ + 1) x₁ (M ⊗ (X₂^⋆s₂)⋆ ⊗ R)) ≫
      (mkBraid x) ≫
        (mkLayer ((L ⊗ (Y₁^⋆s₁)⋆) ⊗ M) (s₂ + 1) x₂ R) =
    (mkBraid (by pure_iso)) ≫
      (mkLayer ((L ⊗ (X₁^⋆s₁)⋆) ⊗ M) (s₂ + 1) x₂ R) ≫
        (mkBraid (by pure_iso)) ≫
          (mkLayer L (s₁ + 1) x₁ (M ⊗ (Y₂^⋆s₂)⋆ ⊗ R)) ≫
            (mkBraid (by pure_iso)) := by
  rw [hx]
  clear x hx
  simp_all
  have hrw :=
    @_root_.Quotient.sound _ (mySetoidHom _ _) _ _ <|
      HomEquiv.swap (L := L) (M := M) (R := R) (s₁ := s₁ + 1) (s₂ := s₂ + 1) (x₁ := x₁) (x₂ := x₂)
  simp at hrw
  simp [repeat_star_succ] at hrw ⊢
  rw [hrw]

set_option maxHeartbeats 10000000 in -- big simp_all
def starHom {X Y : N C} (f : X ⟶ Y) : (X.star ⟶ Y.star) := --by
  Quotient.liftOn f (⟦·.starHom⟧) <| by
    clear f
    rintro f g h
    simp
    induction h <;> simp_all
    case layer l₁ l₂ f =>
      induction f
      case comp ih₁ ih₂ =>
        simp at ih₁ ih₂ ⊢
        have ih₁ := stripBraid ih₁
        have ih₂ := stripBraid ih₂
        rw [ih₁, ih₂]
        my_coherence
      all_goals simp_all
      case freeLeft L₁ X' Y s x R L₂ b =>
        rw [braid_conjugation_right b⋆]
        simp_all
        my_coherence
      case freeRight b =>
        rw [braid_conjugation_left b⋆]
        my_coherence
      case box_strand_hom =>
        rw [strand_box_hom_conjugation]
        my_coherence
      case box_strand_inv L X' Y s R A x =>
        rw [strand_box_inv_conjugation]
        my_coherence
      case strand_box_hom =>
        rw [box_strand_hom_conjugation]
        my_coherence
      case strand_box_inv =>
        rw [box_strand_inv_conjugation]
        my_coherence
      case twist_hom =>
        rw [twist_hom_conjugation_forced]
        my_coherence
      case twist_inv =>
        rw [twist_inv_conjugation]
        my_coherence
      case ε_hom L X Y s x R =>
        my_coherence
      case ε_inv =>
        my_coherence
    case swap L X₁ Y₁ s₁ x₁ M s₂ X₂ R Y₂ x₂ =>
      symm
      rewrite [braid_conjugation_left ((χ_ _ _).inv ▷ _)]
      rewrite [braid_conjugation_right (_ ◁ (χ_ _ _).inv)]
      simp
      apply Eq.trans
      case h₁ =>
        apply congrArg (_ ≫ ·)
        repeat rewrite [← Category.assoc]
        apply congrArg (· ≫ _)
        · simp
          apply HomEquiv.swap_nice_starred'
          handle_braid
      rewrite [braid_conjugation_left ((χ_ _ _).hom ▷ _)]
      rewrite [braid_conjugation_right (_ ◁ (χ_ _ _).hom)]
      my_coherence

#check Nat

#check MonoidalCategory
def tensorHom {X₁ Y₁ X₂ Y₂ : N C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (X₁.tensor X₂ ⟶ Y₁.tensor Y₂) :=
  (whiskerRight f X₂) ≫ (whiskerLeft Y₁ g)

#check Nat

instance : MonoidalCategory (N C) where
  tensorObj := tensor
  tensorHom f g := (whiskerRight f _) ≫ (whiskerLeft _ g)
  tensorUnit := unit
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator X Y Z := {
    hom := mkBraid <| (α_ X.as Y.as Z.as).hom
    inv := mkBraid <| (α_ X.as Y.as Z.as).inv
  }
  leftUnitor X := {
    hom := mkBraid <| (λ_ X.as).hom
    inv := mkBraid <| (λ_ X.as).inv
  }
  rightUnitor X := {
    hom := mkBraid <| (ρ_ X.as).hom
    inv := mkBraid <| (ρ_ X.as).inv
  }
  -- END STRUCT, START PROPERTIES
  tensorHom_def := sorry
  id_tensorHom_id X Y := by
    simp
    sorry
  whiskerLeft_id f Y := by
    sorry
    /- unfold CategoryStruct.id -/
    /- unfold instCategory -/
    /- simp only -/
    /- simp [Quotient.liftOn_mk] -/
    /- #check Quotient.liftOn_mk -/
    sorry
  id_whiskerRight X f := by sorry
  tensorHom_comp_tensorHom := sorry
  associator_naturality := sorry
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon := sorry
  triangle := sorry

def starHom {X Y : N C} (f : X ⟶N Y) : (X⋆ ⟶N Y⋆) := --by
  Quotient.liftOn f (⟦·.starHom⟧) <| by
    clear f
    rintro f g h
    simp
    induction h
    /- induction h <;> simp_all -/
    case layer l₁ l₂ f =>
      simp_all
      induction f
      /- induction f <;> simp_all -/
      case freeLeft b =>
        simp_all
        rw [Layer_braid_conjugation_right b⋆]
        simp_all
        -- I don't want to deal with the skewator junk
        -- I want coherence, but for involutive categories
        monoidal_simps
        sorry
      all_goals sorry
      case comp ih₁ ih₂ =>
        have ih₂ := stripBraid ih₂
        simp_all
      case freeRight b =>
        rw [Layer_braid_conjugation_right (b ▷ _)]
        my_coherence
      case box_strand_hom =>
        rw [Layer_box_strand_inv_conjugation]
        my_coherence
      case box_strand_inv =>
        rw [Layer_box_strand_hom_conjugation]
        my_coherence
      case strand_box_hom =>
        rw [Layer_strand_box_inv_conjugation]
        my_coherence
      case strand_box_inv =>
        rw [Layer_strand_box_hom_conjugation]
        my_coherence
      case twist_hom =>
        rw [Layer_twist_inv_conjugation]
        my_coherence
      case twist_inv =>
        rw [Layer_twist_hom_conjugation]
        my_coherence
      case ε_inv =>
        -- monoidal coherence doesn't like the involutor
        -- we'll do it ourselves
        repeat rw [← whiskerLeft_comp_assoc]
        repeat rw [Category.assoc]
        repeat rw [← comp_whiskerRight]
        my_coherence
    case swap L X₁ Y₁ s₁ x₁ M X₂ Y₂ s₂ x₂ R =>
      sorry
      -- forget about the final braid (so we can apply swap_nice w/o assoc):
      apply Eq.trans
      · repeat rewrite [← assoc]
        apply congrArg (· ≫ _)
        · simp

          -- do the swap:
          rw [HomEquiv.swap_nice' (by coherence)]

      -- simp up; simp doesn't handle rewriting internal monoidal stuff
      my_coherence

#check coherence

#check MonoidalCategory
def comp {X Y Z : N C} (f : X ⟶N Y) (g : Y ⟶N Z) : X ⟶N Z :=
  Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg) f g
scoped infixr:81 " ◁ " => whiskerLeft

end NatCategory

/- instance natCategory : Category (N C) where -/
/-   Hom X Y := _root_.Quotient (mySetoidHom X Y) -/
/-   /- id X := ⟦Hom.braid (𝟙 (FtoF X))⟧ -/ -/
/-   id X := ⟦Hom.id X⟧ -/
/-   comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg) -/
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
#synth Category.{u, u} (N C)
#synth MonoidalCategoryStruct.{u, u} (N C)

/- @[simp] -/
theorem assoc_left {L₁ : N C} :
    ⟦Hom.layer ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩⟧ =
      homMk (Hom.braid ((α_ _ _ _).hom ▷ _ ) |>.comp <|
        Hom.layer ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩ |>.comp <|
          Hom.braid ((α_ _ _ _).inv ▷ _ )) := by
  simp
  apply Quotient.sound
  let l₁ : Layer C := ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩
  let l₂ : Layer C := ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩
  let f : l₁ ⟶L l₂ := .freeLeft (α_ _ _ _).hom
  have h := HomEquiv.layer f
  unfold Layer.Hom.φ at h
  simp at h
  exact h

theorem unassoc_left {L₁ L₂ : N C} :
    ⟦Hom.layer ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩⟧ =
      homMk (Hom.braid ((α_ _ _ _).inv ▷ _ ) |>.comp <|
        Hom.layer ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩ |>.comp <|
          Hom.braid ((α_ _ _ _).hom ▷ _ )) := by
  simp
  apply Quotient.sound
  let l₂ : Layer C := ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩
  let l₁ : Layer C := ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩
  let f : l₁ ⟶L l₂ := .freeLeft (α_ _ _ _).inv
  have h := HomEquiv.layer f
  unfold Layer.Hom.φ at h
  simp at h
  exact h

theorem twist_left {L₁ : N C} :
    ⟦Hom.layer ⟨L, X, Y, s, x, R⟩⟧ =
      homMk (Hom.braid ((ς_ _).inv ▷ _ ) |>.comp <|
        Hom.layer ⟨L, X, Y, s, x, R⟩ |>.comp <|
          Hom.braid ((ς_ _).hom ▷ _ )) := by
  simp
  apply Quotient.sound
  let l₁ : Layer C := ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩
  let l₂ : Layer C := ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩
  let f : l₁ ⟶L l₂ := .freeLeft (α_ _ _ _).hom
  have h := HomEquiv.layer f
  unfold Layer.Hom.φ at h
  simp at h
  exact h

theorem rw_left {L₁ : N C} (b : L₁ ⟶T L₂) :
    ⟦Hom.layer ⟨L₁, X, Y, s, x, R⟩⟧ =
      homMk (Hom.braid (b ▷ _) |>.comp <|
        Hom.layer ⟨L₂, X, Y, s, x, R⟩ |>.comp <|
          Hom.braid (inv b ▷ _)) := by
  simp
  apply Quotient.sound
  let l₁ : Layer C := ⟨(L₁.tensor L₂).tensor L₃, X, Y, s, x, R⟩
  let l₂ : Layer C := ⟨L₁.tensor (L₂.tensor L₃), X, Y, s, x, R⟩
  let f : l₁ ⟶L l₂ := .freeLeft (α_ _ _ _).hom
  have h := HomEquiv.layer f
  unfold Layer.Hom.φ at h
  simp at h
  exact h

attribute [-instance] βcat

#check MonoidalCategory

/- @[simp] -/
/- theorem mk_braid_comp {X Y Z : N C} (f : (X) ⟶T (Y)) (g : (Y) ⟶T (Z)) : -/
/-     ⟦Hom.braid (f ≫β g)⟧ = @CategoryStruct.comp (N C) _ _ _ _ ⟦.braid f⟧ ⟦.braid g⟧ := by -/
/-   apply Quotient.sound -/
/-   constructor -/
/-   constructor -/

/- @[simp] -/
/- theorem mk_braid_comp' {X Y Z : N C} (f : (X) ⟶T (Y)) (g : (Y) ⟶T (Z)) : -/
/-     ⟦Hom.braid (f ≫β g)⟧ = @CategoryStruct.comp (N C) _ _ _ _ ⟦.braid f⟧ ⟦.braid g⟧ := by -/
/-   apply Quotient.sound -/
/-   constructor -/
/-   constructor -/

/- @[simp] -/
/- theorem mk_braid_comp' {X Y Z : N C} (f : X ⟶T Y) (g : Y ⟶T Z) : -/
/-     ⟦Hom.braid (f ≫ g)⟧ = ⟦Hom.braid (f ≫ g)⟧ := by -/
/-   apply Quotient.sound -/

/- @[simp] -/
/- theorem mk_braid_comp'' {X Y Z : N C} (f : (X) ⟶T (Y)) (g : (FtoF Y) ⟶T (FtoF Z)) : -/
/-     Hom.braid (f ≫ g) ≈ (Hom.braid (f)).comp (Hom.braid g) := by -/
/-   constructor -/
/-   constructor -/

@[simp]
theorem mk_id {X : N C} : ⟦Hom.id X⟧ = 𝟙 X :=
  rfl

/- @[simp] -/
/- theorem mk_id {X : N C} : ⟦Hom.braid (𝟙 (FtoF X))⟧ = 𝟙 X := -/
/-   rfl -/

/- @[simp] -/
/- theorem mk_whiskerLeft {X Y₁ Y₂ : N C} (f : Y₁ ⟶n Y₂) : ⟦f.whiskerLeft X⟧ = ◁ 𝟙 X := -/
/-   rfl -/
scoped notation:max n " =>⋆" => Nat.repeat FreeTwistedCategory.star n
#check natCategory.comp
#check @CategoryStruct.comp (N C) natCategory.toCategoryStruct _ _ _
#check congrArg₂

/- set_option pp.explicit true -/
/- set_option pp.notation false -/
/- set_option pp.universes true -/
/- set_option pp.privateNames true -/
/- set_option pp.maxSteps 100000 -/
#check ((@βtwist C).toTwistedCategoryStruct.twist)
#check _root_.Quotient

/- attribute [instance] βcat -/

/- attribute [instance] βcat -/
#check Quot
instance natMonoidalCategory : @MonoidalCategory (N C) natCategory where
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
      -- go into HomEquiv land. Or maybe that'll make no difference...
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
      apply HomEquiv.layer
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
      exact CategoryTheory.FreeTwistedCategory.Hom.α_inv (C := C) X (L * s₁ =>⋆ Y₁) M
      #check CategoryTheory.FreeTwistedCategory.Hom.α_hom
      refine (CategoryTheory.FreeTwistedCategory.Hom.id _).comp ?_
      exact (CategoryTheory.FreeTwistedCategory.Hom.α_inv _ _ _)
      /- let myβ := βcat -/
      /- #synth Category.{u, u} (N C) -/
      /- #check (@βtwist C).toTwistedCategoryStruct.twist -/
      refine ((@βtwist C).toTwistedCategoryStruct.twist _).inv ≫ ?_
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
      rw [rw_left (((@βtwist C).toTwistedCategoryStruct.twist) _).inv]


      simp
      rw [assoc_left]

      repeat1 rw [← Category.assoc]

      sorry
      /- apply congrArg₂ (@CategoryStruct.comp (N C) natCategory.toCategoryStruct ?dom ?middle ?cod) -/

      apply Quotient.sound
      constructor
      constructor
      constructor
      constructor
      constructor
      constructor
      apply HomEquiv.comp
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
lemma HomEquiv.whisker (X : N) {Y₁ Y₂ : N} {f f' : Y₁ ⟶ Y₂} (h : f ≈ f') (Z : N) : (Hom.whisker X f Z) ≈ (Hom.whisker X f' Z) := by
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
lemma HomEquiv.whiskerLeft (X : N) {Y₁ Y₂ : N} {f f' : Y₁ ⟶ Y₂} (h : f ≈ f') :
    (Hom.whiskerLeft X f) ≈ (Hom.whiskerLeft X f') := by
  apply comp (refl _)
  apply comp ?_ (refl _)
  exact HomEquiv.whisker X h 1

@[grind]
lemma HomEquiv.whiskerRight {X₁ X₂ : N} (Y : N) {f f' : X₁ ⟶ X₂} (h : f ≈ f') :
    (Hom.whiskerRight f Y) ≈ (Hom.whiskerRight f' Y) :=
  HomEquiv.whisker 1 h Y

@[grind]
lemma HomEquiv.tensor {X₁ X₂ Y₁ Y₂ : N} {f f' : X₁ ⟶ Y₁} {g g' : X₂ ⟶ Y₂} : f ≈ f' → g ≈ g' →
    (Hom.tensor f g) ≈ (Hom.tensor f' g') := by
  intros hf hg
  constructor
  · exact HomEquiv.whiskerRight X₂ hf
  · exact HomEquiv.whiskerLeft Y₁ hg

@[grind]
lemma HomEquiv.star {X Y : N} {f f' : X ⟶ Y} (h : f ≈ f') :
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
--   val : C

-- instance : Coe C Q where
--   coe v := ⟨v⟩

-- instance : Coe Q C where
--   coe n := n.val

-- @[ext]
-- lemma Q.ext {x y : N} : x.val = y.val → x = y := by
--   grind

#synth Quiver N
-- TODO generalize eqToHom_comp
lemma eqToHom_comp' {X Y Z : N} {f : X ⟶ Y} {g : Y ⟶ Z} {p : X = Y} {q : Y = Z} :
    (f ≈ eqToHom p) → (g ≈ eqToHom q) → (f ≫ g) ≈ (eqToHom (p.trans q)) := by
  intros hf hg
  apply HomEquiv.trans
  · exact HomEquiv.comp hf hg
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
-- lemma HomEquiv.whisker_whisker (X₁ X₂ : N) {Y₁ Y₂ : N} (f : Hom Y₁ Y₂) (Z₁ Z₂ : N) :
--     Hom.whisker X₁ (Hom.whisker X₂ f Z₁) Z₂ ≈
--       eqToHom (by simp [mul_assoc]) ≫ Hom.whisker (X₁ * X₂) f (Z₁ * Z₂) ≫ eqToHom (by simp [mul_assoc]) := by
--   induction f
--   all_goals simp
--   -- case id =>
--   --   -- TODO this calls for reduction tactic
--   --   apply HomEquiv.symm
--   --   apply eqToHom_comp'
--   --   · apply HomEquiv.refl
--   --   · apply eqToHom_comp'
--   --     · apply HomEquiv.refl
--   --     · apply HomEquiv.refl
--   --     · rfl
--   case comp f g =>
--     apply HomEquiv.trans
--     · exact HomEquiv.comp f g
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
--     --   · apply HomEquiv.comp
--     --     ·
--     --       rename_i X _ a
--     --       apply eqToHom_braid (X' := X₁.val * (X₂.val * (X.val.val * Z₁.val) * Z₂.val)) ({ val := { val := X₁.val * X₂.val } } ◁ a ▷ { val := { val := Z₁.val * Z₂.val } })
--     --     · apply refl
--     --   · sorry
--     trans
--     · apply HomEquiv.comp
--       · apply HomEquiv.refl
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
instance : MonoidalCategory (N C) where
  tensorObj X Y := X * Y
  tensorHom := Quotient.lift₂ (⟦Hom.tensor · ·⟧) <| by
    intros f₁ g₁ f₂ g₂ hf hg
    simp
    sorry

open TwistedCategory

instance : TwistedCategoryStruct (N C) where
  tensorObj X Y := X * Y
  tensorHom f g := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg) f g
  tensorUnit := 1
  whiskerLeft X {Y₁ Y₂} f :=
    Quotient.map (Hom.whiskerLeft X ·) (fun _ _ hf ↦ HomEquiv.whiskerLeft X hf) f
  whiskerRight {X₁ X₂} f Y :=
    Quotient.map (Hom.whiskerRight · Y) (fun _ _ hf ↦ HomEquiv.whiskerRight Y hf) f
  associator X Y Z := eqToIso (mul_assoc X Y Z)
  leftUnitor X := eqToIso (one_mul X)
  rightUnitor X := eqToIso (mul_one X)
  starObj X := X⋆
  starHom {X Y} f := Quotient.map Hom.star (fun _ _ hf ↦ HomEquiv.star hf) f
  skewator X Y := eqToIso (StarMonoid.star_mul Y X).symm
  involutor X := eqToIso (star_involutive X)
  twist X := { -- TODO it'd be nice to lift an isomorphism to another isomorphism
    hom := ⟦.braid (ς_ ⟨⟨X⟩⟩).hom⟧
    inv := ⟦.braid (ς_ ⟨⟨X⟩⟩).inv⟧
    hom_inv_id := by
      apply Quotient.sound
      simp
      trans
      · apply HomEquiv.merge_braid
      · simp
        rfl
    inv_hom_id := by
      apply Quotient.sound
      simp
      trans
      · apply HomEquiv.merge_braid
      · simp
        rfl
  }

-- next step: prefunctor between S C and N words that'll eventually be our isomorphism

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
-- on S C and N
-- the natural isomorphisms are what's giving us trouble here, and
-- truly we don't care about that -- just map objects to objects,
-- morphisms to morphisms
-- first, just define it on the precategories: Hom to Hom

/-
-- TODO use ofTensorHom
#check ofTensorHom
instance : MonoidalCategory N where
  tensorObj X Y := X * Y
  tensorHom f g := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg) f g
  tensorUnit := 1
  associator X Y Z := eqToIso'' (mul_assoc X Y Z)
  leftUnitor X := eqToIso'' (one_mul X)
  rightUnitor X := eqToIso'' (mul_one X)
  whiskerLeft X {Y₁ Y₂} f := Quotient.map (Hom.whiskerLeft X ·) (fun _ _ hf ↦ HomEquiv.whiskerLeft X hf) f
  whiskerRight {X₁ X₂} f Y := Quotient.map (Hom.whiskerRight · Y) (fun _ _ hf ↦ HomEquiv.whiskerRight Y hf) f
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
    apply HomEquiv.trans
    · apply HomEquiv.comp
      · apply HomEquiv.refl
      · apply HomEquiv.id_comp
    · apply eqToHom_comp'
      · apply HomEquiv.refl
      · apply HomEquiv.refl
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

-- then an isomorphism of categories between the one on N and the one on S C

#check Functor.Monoidal
-/
-/

