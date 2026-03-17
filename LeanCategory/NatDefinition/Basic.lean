import Mathlib
import LeanCategory.NatDefinition.Layer
import LeanCategory.FreeInvolutive.CoherenceTactic

namespace CategoryTheory.NatDefinition
open scoped Layer
open FreeTwistedCategory

universe u
variable {C : Type u} [Quiver.{v} (T C)]

inductive Hom : N C → N C → Type (max (u + 2) v) where
  | layer : (l : Layer C) →
      Hom ⟨(l.boundary .Bottom)⟩ ⟨(l.boundary .Top)⟩
  | braid {X Y : N C} : (X.as ⟶T Y.as) → Hom X Y
  | comp {X Y Z : N C} : Hom X Y → Hom Y Z → Hom X Z

infixr:10 " ⟶n " => Hom

open CategoryTheory

open MonoidalCategory
open InvolutiveCategory -- for the ⋆ notation
open TwistedCategory -- why not

open MonoidalCategory

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
        ((Hom.braid (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)).comp
        ((Hom.layer ⟨(L ⊗ (Y₁^⋆s₁)) ⊗ M, X₂, Y₂, s₂, x₂, R⟩))))
      ((Hom.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _).comp
        ((Hom.layer ⟨(L ⊗ (X₁^⋆s₁)) ⊗ M, X₂, Y₂, s₂, x₂, R⟩).comp
          ((Hom.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _).comp
            ((Hom.layer ⟨L, X₁, Y₁, s₁, x₁, M ⊗ (Y₂^⋆s₂) ⊗ R⟩).comp
              (Hom.braid <| by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)))))
  | layer (f : l₁ ⟶l l₂) : HomEquiv
      (Hom.layer l₁)
      ((Hom.braid <| f.φ .Bottom).comp <|
        (Hom.layer l₂).comp <|
        (Hom.braid <| Groupoid.inv <| f.φ .Top))
  | symm (f g) : HomEquiv f g → HomEquiv g f
  | trans {f g h : X ⟶n Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h

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

def mkLayer (L : FreeTwistedCategory C) {X Y : T C} (s : ℕ) (x : X ⟶ Y)
    (R : FreeTwistedCategory C) : (mk <| L ⊗ (X^⋆s) ⊗ R ) ⟶ ⟨L ⊗ (Y^⋆s) ⊗ R⟩ :=
  ⟦Hom.layer ⟨L, X, Y, s, x, R⟩⟧

@[simp]
theorem mk_layer {L : T C} {x : X ⟶ Y} : ⟦.layer ⟨L, X, Y, s, x, R⟩⟧ = mkLayer L s x R :=
  rfl

def mkBraid {X Y : N C} (b : X.as ⟶T Y.as) : X ⟶ Y := ⟦Hom.braid b⟧

@[simp]
theorem mk_braid {X Y : N C} {b : X.as ⟶T Y.as} : ⟦.braid b⟧ = mkBraid b :=
  rfl

@[simp]
theorem mkBraid_id {X : N C} : mkBraid (𝟙 X.as) = 𝟙 X :=
  rfl

@[simp]
theorem mkBraid_id' : mkBraid (𝟙 X) = @CategoryStruct.id (N C) _ _ :=
  rfl

@[simp]
theorem unmk_braid_comp {X Y Z : N C} (f : X.as ⟶T Y.as) (g : Y.as ⟶T Z.as) :
     mkBraid f ≫ mkBraid g = mkBraid (f ≫ g) := by
  apply _root_.Quotient.sound
  constructor

@[simp]
theorem unmk_braid_comp_assoc {W X Y Z : N C} (f : W.as ⟶T X.as) (g : X.as ⟶T Y.as) (h : Y ⟶ Z) :
     mkBraid f ≫ mkBraid g ≫ h = mkBraid (f ≫ g) ≫ h := by
  rw [← Category.assoc]
  apply congrArg (· ≫ _)
  simp

lemma twist_inv_conjugation {L : T C} :
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
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      exact Layer.Hom.comp Layer.Hom.ε_inv Layer.Hom.twist_hom
  simp
  simp [repeat_star_succ]

lemma twist_hom_conjugation {L : T C} :
    mkLayer L (s + 1) x R = mkBraid (L ◁ (ς_ _).hom ▷ R) ≫
      mkLayer L s x R ≫ mkBraid (L ◁ (ς_ _).inv ▷ R) := by
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
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.strand_box_hom
  simp [involutiveComp]

lemma strand_box_inv_conjugation {L : T C} {x : X ⟶ Y} :
    mkLayer L s x (A ⊗ R) = mkBraid (𝟙 _ ⊗⋆≫ L ◁ (σ_ A (X^⋆s)).inv ▷ R ⊗⋆≫ 𝟙 _) ≫
      mkLayer (L ⊗ A) s x R ≫
        mkBraid (𝟙 _ ⊗⋆≫ L ◁ (σ_ A (Y^⋆s)).hom ▷ R ⊗⋆≫ 𝟙 _) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.strand_box_inv
  simp [involutiveComp]

lemma box_strand_hom_conjugation {L : T C} {x : X ⟶ Y} :
    mkLayer L s x (A ⊗ R) = mkBraid (𝟙 _ ⊗⋆≫ L ◁ (σ_ (X^⋆s) A).hom ▷ R ⊗⋆≫ 𝟙 _) ≫
      mkLayer (L ⊗ A) s x R ≫
        mkBraid (𝟙 _ ⊗⋆≫ L ◁ (σ_ (Y^⋆s) A).inv ▷ R ⊗⋆≫ 𝟙 _) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.box_strand_hom
  simp [involutiveComp]

lemma box_strand_inv_conjugation {L : T C} {x : X ⟶ Y} :
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
      mkLayer (L₁ ⊗ (L₂ ⊗ L₃)) s x R =
        mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) ≫
          mkLayer ((L₁ ⊗ L₂) ⊗ L₃) s x R ≫
            mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) := by
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
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeRight
      exact (α_ _ _ _).hom
  simp [involutiveComp]

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

@[simp]
lemma involutor_conjugation {L : T C} :
    mkLayer L (s + 2) x  R =
      mkBraid (_ ◁ (e_ _).hom ▷ _) ≫
        mkLayer L s x R ≫
          mkBraid (_ ◁ (e_ _).inv ▷ _) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      exact Layer.Hom.ε_hom
  simp

lemma braid_conjugation_left {L₁ L₂ : T C} (b : L₁ ⟶T L₂) :
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

lemma braid_conjugation_right {R₁ R₂ : T C} (b : R₁ ⟶T R₂) :
    mkLayer L s x R₁ =
      mkBraid (_ ◁ _ ◁ b) ≫
        mkLayer L s x R₂ ≫
          mkBraid (_ ◁ _ ◁ inv b) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeRight
      exact b
  simp

lemma stripBraidLeft {X Y : N C} {b : X.as ⟶T Y.as} {f : Y ⟶ Z} {g : X ⟶ Z} :
    ⟦(Hom.braid b)⟧ ≫ f = g → f = ⟦(Hom.braid (inv b))⟧ ≫ g := by
  intros h
  trans (⟦Hom.braid (inv b)⟧ ≫ (⟦Hom.braid b⟧ ≫ f))
  · simp
  · rw [h]

lemma stripBraidRight {X Y : N C} {b : Y.as ⟶T Z.as} {f : X ⟶ Y} {g : X ⟶ Z} :
    f ≫ mkBraid b = g → f = g ≫ mkBraid (inv b) := by
  intros h
  trans ((f ≫ ⟦Hom.braid b⟧) ≫ ⟦Hom.braid (inv b)⟧)
  · simp
  · simp only [mk_braid]; rw [h]

lemma stripBraid {W X Y Z : N C} {b₁ : W.as ⟶T X.as} {f : X ⟶ Y} {b₂ : Y.as ⟶T Z.as} {g : W ⟶ Z} :
    mkBraid b₁ ≫ f ≫ mkBraid b₂ = g → f = mkBraid (inv b₁) ≫ g ≫ mkBraid (inv b₂) := by
  intros h
  have h := stripBraidLeft h
  have h := stripBraidRight h
  simp at h
  exact h

def HomEquiv.swap_coherent {L : T C} {x₁ : X₁ ⟶ Y₁} {x₂ : X₂ ⟶ Y₂} {x : _ ⟶T _}
    (hx : x = (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) :
      (mkLayer L s₁ x₁ (M ⊗ (X₂^⋆s₂) ⊗ R)) ≫
        (mkBraid x) ≫
          (mkLayer ((L ⊗ (Y₁^⋆s₁)) ⊗ M) s₂ x₂ R) =
      (mkBraid (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) ≫
        (mkLayer ((L ⊗ (X₁^⋆s₁)) ⊗ M) s₂ x₂ R) ≫
          (mkBraid (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) ≫
            (mkLayer L s₁ x₁ (M ⊗ (Y₂^⋆s₂) ⊗ R)) ≫
              (mkBraid (by simp; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) := by
  rw [hx]
  clear x hx
  simp_all
  have hrw :=
    @_root_.Quotient.sound _ (mySetoidHom _ _) _ _ <|
      HomEquiv.swap (L := L) (M := M) (R := R) (s₁ := s₁) (s₂ := s₂) (x₁ := x₁) (x₂ := x₂)
  simp at hrw
  rw [hrw]

def HomEquiv.swap_coherent_starred {L : T C} {x₁ : X₁ ⟶ Y₁} {x₂ : X₂ ⟶ Y₂} {x : _ ⟶T _}
    (hx : x = (by simp [repeat_star_succ]; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) :
      (mkLayer L (s₁ + 1) x₁ (M ⊗ (X₂^⋆s₂)⋆ ⊗ R)) ≫
        (mkBraid x) ≫
          (mkLayer ((L ⊗ (Y₁^⋆s₁)⋆) ⊗ M) (s₂ + 1) x₂ R) =
      (mkBraid (by simp [repeat_star_succ]; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) ≫
        (mkLayer ((L ⊗ (X₁^⋆s₁)⋆) ⊗ M) (s₂ + 1) x₂ R) ≫
          (mkBraid (by simp [repeat_star_succ]; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) ≫
            (mkLayer L (s₁ + 1) x₁ (M ⊗ (Y₂^⋆s₂)⋆ ⊗ R)) ≫
              (mkBraid (by simp [repeat_star_succ]; exact 𝟙 _ ⊗⋆≫ 𝟙 _)) := by
  rw [hx]
  clear x hx
  simp_all
  have hrw :=
    @_root_.Quotient.sound _ (mySetoidHom _ _) _ _ <|
      HomEquiv.swap (L := L) (M := M) (R := R) (s₁ := s₁ + 1) (s₂ := s₂ + 1) (x₁ := x₁) (x₂ := x₂)
  simp at hrw
  simp [repeat_star_succ] at hrw ⊢
  rw [hrw]

macro "nat_coherence_step" : tactic =>
  `(tactic|
    first
      | rfl -- just mkLayer
      | apply congrArg₂ _ (congrArg _ (by inv_coherence)) -- starting w/ mkBraid
      | apply congrArg₂ _ rfl -- starting w/ mkLayer
      | apply congrArg _ <| by inv_coherence -- just mkBraid
      | fail "IDK what to do"
  )

macro "nat_coherence" : tactic =>
  `(tactic|
    first
      | simp [involutiveComp, repeat_star_succ]; done
      | (try simp [involutiveComp, repeat_star_succ]); repeat1 nat_coherence_step
  )

open Layer
open scoped Layer

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
        nat_coherence
      all_goals simp_all
      case freeLeft L₁ X' Y s x R L₂ b =>
        rw [braid_conjugation_left (X.as ◁ b)]
        nat_coherence
      case freeRight b =>
        rw [braid_conjugation_right b]
        nat_coherence
      case box_strand_hom =>
        rw [box_strand_hom_conjugation]
        nat_coherence
      case box_strand_inv L X' Y s R A x =>
        rw [box_strand_inv_conjugation]
        nat_coherence
      case strand_box_hom =>
        rw [strand_box_hom_conjugation]
        nat_coherence
      case strand_box_inv =>
        rw [strand_box_inv_conjugation]
        nat_coherence
      case twist_hom =>
        rw [twist_hom_conjugation]
        nat_coherence
      case twist_inv =>
        rw [twist_inv_conjugation]
        nat_coherence
      case ε_hom =>
        nat_coherence
      case ε_inv =>
        nat_coherence
    case swap L X₁ Y₁ s₁ x₁ M s₂ X₂ R Y₂ x₂ =>
      rewrite [braid_conjugation_left ((α_ _ _ _).inv ▷ _)]
      simp
      apply Eq.trans
      case h₁ =>
        apply congrArg (_ ≫ ·)
        repeat rewrite [← Category.assoc]
        apply congrArg (· ≫ _)
        · simp
          apply HomEquiv.swap_coherent
          inv_coherence
      simp
      rewrite [braid_conjugation_left ((α_ _ _ _).inv ▷ _)]
      nat_coherence

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
        nat_coherence
      all_goals simp_all
      case freeLeft L₁ X' Y s x R L₂ b =>
        rw [braid_conjugation_left b]
        nat_coherence
      case freeRight b =>
        rw [braid_conjugation_right (b ▷ Y.as)]
        nat_coherence
      case box_strand_hom =>
        rw [box_strand_hom_conjugation]
        nat_coherence
      case box_strand_inv L X' Y s R A x =>
        rw [box_strand_inv_conjugation]
        nat_coherence
      case strand_box_hom =>
        rw [strand_box_hom_conjugation]
        nat_coherence
      case strand_box_inv =>
        rw [strand_box_inv_conjugation]
        nat_coherence
      case twist_hom =>
        rw [twist_hom_conjugation]
        nat_coherence
      case twist_inv =>
        rw [twist_inv_conjugation]
        nat_coherence
      case ε_hom =>
        nat_coherence
      case ε_inv =>
        nat_coherence
    case swap L X₁ Y₁ s₁ x₁ M s₂ X₂ R Y₂ x₂ =>
      rewrite [braid_conjugation_right (_ ◁ (α_ _ _ _).hom)]
      simp
      apply Eq.trans
      case h₁ =>
        apply congrArg (_ ≫ ·)
        repeat rewrite [← Category.assoc]
        apply congrArg (· ≫ _)
        · simp
          apply HomEquiv.swap_coherent
          inv_coherence
      simp
      rewrite [braid_conjugation_right (_ ◁ (α_ _ _ _).inv)]
      nat_coherence

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
        nat_coherence
      all_goals simp_all
      case freeLeft L₁ X' Y s x R L₂ b =>
        rw [braid_conjugation_right b⋆]
        simp_all
        nat_coherence
      case freeRight b =>
        rw [braid_conjugation_left b⋆]
        nat_coherence
      case box_strand_hom =>
        rw [strand_box_hom_conjugation]
        nat_coherence
      case box_strand_inv L X' Y s R A x =>
        rw [strand_box_inv_conjugation]
        nat_coherence
      case strand_box_hom =>
        rw [box_strand_hom_conjugation]
        nat_coherence
      case strand_box_inv =>
        rw [box_strand_inv_conjugation]
        nat_coherence
      case twist_hom =>
        rw [twist_hom_conjugation_forced]
        nat_coherence
      case twist_inv =>
        rw [twist_inv_conjugation]
        nat_coherence
      case ε_hom L X Y s x R =>
        nat_coherence
      case ε_inv =>
        nat_coherence
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
          apply HomEquiv.swap_coherent_starred
          inv_coherence
      rewrite [braid_conjugation_left ((χ_ _ _).hom ▷ _)]
      rewrite [braid_conjugation_right (_ ◁ (χ_ _ _).hom)]
      nat_coherence

end CategoryTheory.NatDefinition


