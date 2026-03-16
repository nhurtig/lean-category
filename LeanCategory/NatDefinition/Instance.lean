import Mathlib
import LeanCategory.NatDefinition.Basic

namespace CategoryTheory.NatDefinition

open MonoidalCategory InvolutiveCategory FreeTwistedCategory

@[simp]
lemma whiskerLeft_mkBraid : ∀ {X Y₁ Y₂ : N C} (b : Y₁.as ⟶ Y₂.as),
    whiskerLeft X (mkBraid b) = mkBraid (X.as ◁ b) := by
  intros
  unfold whiskerLeft mkBraid
  rw [Quotient.liftOn_mk]
  simp

@[simp]
lemma whiskerLeft_mkLayer : whiskerLeft X (mkLayer L s x R) =
    (mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _)) ≫ mkLayer (X.as ⊗ L) s x R ≫ (mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _)) := by
  unfold whiskerLeft mkLayer
  rw [Quotient.liftOn_mk]
  simp
  my_coherence

@[simp]
lemma whiskerLeft_comp : ∀ {X Y Z : N C} (f : X ⟶ Y) (g : Y ⟶ Z) (W : N C),
    whiskerLeft W (f ≫ g) = whiskerLeft W f ≫ whiskerLeft W g := by
  intros X Y Z f g W
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rename_i f g
  simp
  conv =>
    lhs
    unfold whiskerLeft
    rw [← mk_comp]
    rw [_root_.Quotient.liftOn_mk]
    simp
  unfold whiskerLeft
  simp

@[simp]
lemma whiskerRight_mkBraid : ∀ {X₁ X₂ Y : N C} (b : X₁.as ⟶ X₂.as),
    whiskerRight (mkBraid b) Y = mkBraid (b ▷ Y.as) := by
  intros
  unfold whiskerRight mkBraid
  rw [Quotient.liftOn_mk]
  simp

@[simp]
lemma whiskerRight_mkLayer : whiskerRight (mkLayer L s x R) Y =
    (mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ 𝟙 _))) ≫ mkLayer L s x (R ⊗ Y.as) ≫
      (mkBraid (by simp; exact (𝟙 _ ⊗⋆≫ 𝟙 _))) := by
  unfold whiskerRight mkLayer
  rw [Quotient.liftOn_mk]
  simp

@[simp]
lemma whiskerRight_comp : ∀ {X Y Z : N C} (f : X ⟶ Y) (g : Y ⟶ Z) (W : N C),
    whiskerRight (f ≫ g) W = whiskerRight f W ≫ whiskerRight g W := by
  intros X Y Z f g W
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rename_i f g
  simp
  conv =>
    lhs
    unfold whiskerRight
    rw [← mk_comp]
    rw [_root_.Quotient.liftOn_mk]
    simp
  unfold whiskerRight
  simp

@[simp]
lemma starHom_mkBraid : ∀ {X Y : N C} (b : X.as ⟶ Y.as), starHom (mkBraid b) = mkBraid b⋆ := by
  intros
  unfold starHom mkBraid
  rw [Quotient.liftOn_mk]
  simp

@[simp]
lemma starHom_mkLayer : starHom (mkLayer L s x R) =
    mkBraid (by simp [repeat_star_succ]; exact (𝟙 _ ⊗⋆≫ 𝟙 _)) ≫
      mkLayer R⋆ (s + 1) x L⋆ ≫ mkBraid (by simp [repeat_star_succ]; exact (𝟙 _ ⊗⋆≫ 𝟙 _)) := by
  unfold starHom mkLayer
  rw [Quotient.liftOn_mk]
  simp

@[simp]
lemma starHom_comp : ∀ {X Y Z : N C} (f : X ⟶ Y) (g : Y ⟶ Z),
    starHom (f ≫ g) = starHom f ≫ starHom g := by
  intros X Y Z f g
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rename_i f g
  simp
  conv =>
    lhs
    unfold starHom
    rw [← mk_comp]
    rw [_root_.Quotient.liftOn_mk]
    simp
  unfold starHom
  simp

@[simp, reassoc (attr := simp)]
lemma whiskerLeft_id : ∀ (X Y : N C), whiskerLeft X (𝟙 Y) = (𝟙 <| X.tensor Y) := by
  intros X Y
  unfold CategoryStruct.id instCategory whiskerLeft
  simp only
  rw [Quotient.liftOn_mk]
  simp

@[simp, reassoc (attr := simp)]
lemma id_whiskerRight : ∀ (X Y : N C), whiskerRight (𝟙 X) Y = (𝟙 <| X.tensor Y) := by
  intros X Y
  unfold CategoryStruct.id instCategory whiskerRight
  simp only
  rw [Quotient.liftOn_mk]
  simp

/- (whiskerRight f _) ≫ (whiskerLeft _ g) -/
def tensorHom {X Y : N C} (f : X ⟶ X') (g : Y ⟶ Y') : tensor X Y ⟶ tensor X' Y' :=
  (whiskerRight f _) ≫ (whiskerLeft _ g)

@[simp, reassoc (attr := simp)]
lemma id_tensorHom_id : ∀ (X Y : N C), tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (X.tensor Y) := by
  intros X Y
  unfold tensorHom
  simp

@[reassoc]
lemma whisker_exchange {W X Y Z : N C} (f : W ⟶ X) (g : Y ⟶ Z) :
    whiskerRight f Y ≫ whiskerLeft X g = whiskerLeft W g ≫ whiskerRight f Z := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rename_i f g
  unfold whiskerRight whiskerLeft
  simp
  induction f <;> induction g <;> simp_all
  case layer.layer l₁ l₂ =>
    rw [braid_conjugation_right (α_ _ _ _).inv]
    rw [braid_conjugation_left <| (α_ _ _ _).inv ▷ _]
    rw [braid_conjugation_left <| (α_ _ _ _).hom]
    simp only [IsIso.Iso.inv_inv, Category.assoc, unmk_braid_comp,
      involuteComp_assoc, Category.id_comp, unmk_braid_comp_assoc, whiskerRight_tensor,
      IsIso.Iso.inv_hom, inv_whiskerRight, Iso.hom_inv_id_assoc]
    apply Eq.trans
    case h₁ =>
      apply congrArg (_ ≫ ·)
      repeat rewrite [← Category.assoc]
      apply congrArg (· ≫ _)
      repeat rewrite [Category.assoc]
      · apply HomEquiv.swap_coherent
        handle_braid
    simp
    rewrite [braid_conjugation_left ((α_ _ _ _).inv ▷ _)]
    my_coherence
  case braid.layer b l =>
    rw [braid_conjugation_left (b ▷ _)]
    simp_all
    my_coherence_step
    my_coherence_step
    -- need to cancel the stuff between the b's:
    apply congrArg
    symm
    simp [involutiveComp]
    repeat rw [← comp_whiskerRight_assoc]
    repeat rw [← comp_whiskerRight]
    simp
  case layer.braid l b =>
    rw [braid_conjugation_right (_ ◁ b)]
    simp_all
    my_coherence_step
    my_coherence_step
    -- need to cancel the stuff between the b's:
    apply congrArg
    simp [involutiveComp]
    repeat1 rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    repeat1 rw [← MonoidalCategory.whiskerLeft_comp]
    simp
  case layer.comp l g₁ g₂ ih₁ ih₂ =>
    apply Eq.trans
    · rewrite [← Category.assoc]
      rewrite [← Category.assoc]
      rewrite [← Category.assoc]
      apply congrArg (· ≫ _)
      · simp
        rw [ih₁]
    simp
    rw [ih₂]
  case braid.comp b g₁ g₂ ih₁ ih₂ =>
    repeat rw [← Category.assoc]
    rw [ih₁]; clear ih₁
    simp
    rw [ih₂]
  case comp.comp f₁ f₂ _ _ g₁ g₂ ih₁ ih₂ ih₃ ih₄ =>
    repeat rw [← Category.assoc]
    apply congrArg (· ≫ _)
    simp_all
  case comp.braid =>
    repeat rw [← Category.assoc]
    apply congrArg (· ≫ _)
    simp_all
  case comp.layer =>
    repeat rw [← Category.assoc]
    apply congrArg (· ≫ _)
    simp_all
  case braid.braid =>
    rw [MonoidalCategory.whisker_exchange]

@[reassoc]
lemma tensorHom_comp_tensorHom : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : N C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  unfold tensorHom
  intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
  simp
  apply congrArg
  repeat rw [← Category.assoc]
  apply congrArg (· ≫ _)
  rw [whisker_exchange]

@[simp]
lemma leftUnitor_conjugation_left {L : T C} :
      mkLayer (𝟙_ _ ⊗ L) s x R =
        mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) ≫
          mkLayer L s x R ≫
            mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeLeft
      exact (λ_ _).hom
  simp [involutiveComp]

@[simp]
lemma rightUnitor_conjugation_left {L : T C} :
      mkLayer (L ⊗ 𝟙_ _) s x R =
        mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) ≫
          mkLayer L s x R ≫
            mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeLeft
      exact (ρ_ _).hom
  simp [involutiveComp]

@[simp]
lemma leftUnitor_conjugation_right {L : T C} :
      mkLayer L s x (𝟙_ _ ⊗ R) =
        mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) ≫
          mkLayer L s x R ≫
            mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeRight
      exact (λ_ _).hom
  simp [involutiveComp]

@[simp]
lemma rightUnitor_conjugation_right {L : T C} :
      mkLayer L s x (R ⊗ 𝟙_ _) =
        mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) ≫
          mkLayer L s x R ≫
            mkBraid (𝟙 _ ⊗⋆≫ 𝟙 _) := by
  apply Eq.trans
  · apply _root_.Quotient.sound
    · apply HomEquiv.layer
      apply Layer.Hom.freeRight
      exact (ρ_ _).hom
  simp [involutiveComp]

@[reassoc]
lemma leftUnitor_naturality : ∀ {X Y : N C} (f : X ⟶ Y),
    whiskerLeft _ f ≫ mkBraid (λ_ Y.as).hom = mkBraid (λ_ X.as).hom ≫ f := by
  intros X Y f
  induction f using Quotient.inductionOn
  rename_i f
  unfold whiskerLeft
  simp
  induction f <;> simp_all
  case comp f g ih₁ ih₂ =>
    rw [← Category.assoc]
    rw [ih₁]
    simp
  case layer l =>
    rcases l with ⟨L, X, Y, s, x, R⟩
    my_coherence

@[reassoc]
lemma rightUnitor_naturality : ∀ {X Y : N C} (f : X ⟶ Y),
    whiskerRight f _ ≫ mkBraid (ρ_ Y.as).hom = mkBraid (ρ_ X.as).hom ≫ f := by
  intros X Y f
  induction f using Quotient.inductionOn
  rename_i f
  unfold whiskerRight
  simp
  induction f <;> simp_all
  case comp f g ih₁ ih₂ =>
    rw [← Category.assoc]
    rw [ih₁]
    simp
  case layer l =>
    my_coherence

@[reassoc]
lemma associator_naturality_right : ∀ {X Y Z : N C} (h : Z ⟶ Z'),
    whiskerLeft ⟨X.as ⊗ Y.as⟩ h ≫ mkBraid (α_ X.as Y.as Z'.as).hom =
      mkBraid (α_ X.as Y.as Z.as).hom ≫ whiskerLeft X (whiskerLeft Y h) := by
  intro X Y Z h
  induction h using Quotient.inductionOn
  rename_i h
  induction h <;> simp_all
  case layer l =>
    rcases l with ⟨L, X', Y', s, x, R⟩
    my_coherence
  case comp f g ih₁ ih₂ =>
    rw [← Category.assoc]
    rw [ih₁]
    simp

@[reassoc]
lemma associator_naturality_middle : ∀ {X Y Z : N C} (g : Y ⟶ Y'),
    whiskerRight (whiskerLeft X g) Z ≫ mkBraid (α_ X.as Y'.as Z.as).hom =
      mkBraid (α_ X.as Y.as Z.as).hom ≫ whiskerLeft X (whiskerRight g Z) := by
  intro X Y Z g
  induction g using Quotient.inductionOn
  rename_i g
  induction g <;> simp_all
  case layer l =>
    rcases l with ⟨L, X', Y', s, x, R⟩
    my_coherence
  case comp f g ih₁ ih₂ =>
    rw [← Category.assoc]
    rw [ih₁]
    simp

@[reassoc]
lemma associator_naturality_left : ∀ {X Y Z : N C} (f : X ⟶ X'),
    whiskerRight (whiskerRight f Y) Z ≫ mkBraid (α_ X'.as Y.as Z.as).hom =
      mkBraid (α_ X.as Y.as Z.as).hom ≫ whiskerRight f ⟨Y.as ⊗ Z.as⟩ := by
  intro X Y Z f
  induction f using Quotient.inductionOn
  rename_i f
  induction f <;> simp_all
  case layer l =>
    rcases l with ⟨L, X', Y', s, x, R⟩
    my_coherence
  case comp f g ih₁ ih₂ =>
    rw [← Category.assoc]
    rw [ih₁]
    simp

@[reassoc]
lemma associator_naturality : ∀ {X Y Z : N C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
  tensorHom (tensorHom f g) h ≫ mkBraid (α_ X'.as Y'.as Z'.as).hom =
    mkBraid (α_ X.as Y.as Z.as).hom ≫ tensorHom f (tensorHom g h) := by
  intros X Y Z f g h
  unfold tensorHom
  simp
  rw [associator_naturality_right]
  rw [associator_naturality_middle_assoc]
  rw [associator_naturality_left_assoc]

instance : MonoidalCategory (N C) where
  tensorObj := tensor
  tensorHom := tensorHom
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
  tensorHom_def f g := rfl
  id_tensorHom_id X Y := by simp
  whiskerLeft_id f Y := by simp
  id_whiskerRight X f := by simp
  tensorHom_comp_tensorHom := by simp [tensorHom_comp_tensorHom]
  associator_naturality := associator_naturality
  leftUnitor_naturality := leftUnitor_naturality
  rightUnitor_naturality := rightUnitor_naturality
  pentagon := by simp
  triangle := by simp

end CategoryTheory.NatDefinition

