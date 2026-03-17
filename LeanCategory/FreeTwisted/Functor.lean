import LeanCategory.FreeTwisted.Instance
import LeanCategory.FreeTwistedQuiver.Instance

namespace CategoryTheory.FreeTwistedCategory

variable {C : Type u}

variable {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [InvolutiveCategory D] [TwistedCategory D] (m : C → D)

open MonoidalCategory
open InvolutiveCategory
open TwistedCategory

open Hom

@[simp]
def projectMapAux : ∀ {X Y : T C}, (X ⟶t Y) → (X.projectObj m ⟶ Y.projectObj m)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, l_hom _ => (λ_ _).hom
  | _, _, l_inv _ => (λ_ _).inv
  | _, _, ρ_hom _ => (ρ_ _).hom
  | _, _, ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.comp f g => projectMapAux f ≫ projectMapAux g
  | _, _, Hom.whiskerLeft X p => X.projectObj m ◁ projectMapAux p
  | _, _, Hom.whiskerRight p X => projectMapAux p ▷ X.projectObj m
  | _, _, Hom.tensor f g => projectMapAux f ⊗ₘ projectMapAux g
  | _, _, Hom.star f => (projectMapAux f)⋆
  | _, _, χ_hom _ _ => (χ_ _ _).hom
  | _, _, χ_inv _ _ => (χ_ _ _).inv
  | _, _, ε_hom _ => (e_ _).hom
  | _, _, ε_inv _ => (e_ _).inv
  | _, _, twist_hom _ => (ς_ _).hom
  | _, _, twist_inv _ => (ς_ _).inv

lemma projectMapAux_Pure : ∀ {X Y : T C} (f : X ⟶t Y),
    f.Pure → InvolutiveCoherence (projectMapAux m f) := by
  intro X Y f hf
  induction f <;> simp_all
  all_goals constructor <;> assumption

@[simp]
def projectMap {X Y : T C} : (X ⟶ Y) → (X.projectObj m ⟶ Y.projectObj m) :=
  _root_.Quotient.lift (projectMapAux m) <| by
    intro f g h
    induction h with
    | refl => rfl
    | symm _ _ _ hfg' => exact hfg'.symm
    | trans _ _ hfg hgh => exact hfg.trans hgh
    | comp _ _ hf hg => dsimp only [projectMapAux]; rw [hf, hg]
    | whiskerLeft _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
    | whiskerRight _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
    | tensor _ _ hfg hfg' => dsimp only [projectMapAux]; rw [hfg, hfg']
    | tensorHom_def f g =>
        dsimp only [projectMapAux]; rw [MonoidalCategory.tensorHom_def]; simp
    | comp_id => dsimp only [projectMapAux]; rw [Category.comp_id]
    | id_comp => dsimp only [projectMapAux]; rw [Category.id_comp]
    | assoc => dsimp only [projectMapAux]; rw [Category.assoc]
    /- | id_tensorHom_id => dsimp only [projectMapAux]; rw [MonoidalCategory.id_tensorHom_id]; rfl -/
    | tensorHom_comp_tensorHom =>
      dsimp only [projectMapAux]; rw [MonoidalCategory.tensorHom_comp_tensorHom]
    | whiskerLeft_id =>
        dsimp only [projectMapAux]; simp
    | id_whiskerRight =>
        dsimp only [projectMapAux]; simp
    /- | α_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id] -/
    /- | α_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id] -/
    | associator_naturality =>
        dsimp only [projectMapAux]; rw [MonoidalCategory.associator_naturality]
    /- | ρ_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id] -/
    /- | ρ_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id] -/
    | ρ_naturality f =>
        dsimp only [projectMapAux]; simp
    /- | l_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id] -/
    /- | l_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id] -/
    | l_naturality =>
        dsimp only [projectMapAux]; simp
    /- | pentagon => -/
    /-     dsimp only [projectMapAux, FreeTwistedCategory.project] -/
    /-     rw [MonoidalCategory.pentagon] -/
    /- | triangle => -/
    /-     dsimp only [projectMapAux, FreeTwistedCategory.project] -/
    /-     rw [MonoidalCategory.triangle] -/
    -- START NAT'S STUFF
    | star _ hf => dsimp only [projectMapAux]; rw [hf]
    | starHom_comp_starHom _ hf =>
        dsimp only [projectMapAux]; rw [InvolutiveCategory.starHom_comp_starHom]
    /- | starHom_id => -/
    /-     dsimp only [projectMapAux, FreeTwistedCategory.project] -/
    /-     rw [InvolutiveCategory.starHom_id] -/
    /- | ε_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id] -/
    /- | ε_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id] -/
    | ε_naturality =>
        dsimp only [projectMapAux]
        exact InvolutiveCategory.involutor_naturality _
    /- | χ_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id] -/
    /- | χ_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id] -/
    | χ_naturality =>
        dsimp only [projectMapAux, projectObj]
        exact InvolutiveCategory.skewator_naturality _ _
    /- | f3 => -/
    /-     dsimp only [projectMapAux, FreeTwistedCategory.project] -/
    /-     exact f3 _ _ _ -/
    /- | n2 => -/
    /-     dsimp only [projectMapAux, FreeTwistedCategory.project] -/
    /-     exact n2 _ _ -/
    /- | a => -/
    /-     dsimp only [projectMapAux, FreeTwistedCategory.project] -/
    /-     exact a _ -/
    | twist_hom_inv => dsimp only [projectMapAux]; simp
    | twist_inv_hom => dsimp only [projectMapAux]; simp
    | twist_naturality =>
        dsimp only [projectMapAux, projectObj]
        exact TwistedCategory.twist_naturality _
    | tℓ =>
        dsimp only [projectMapAux, projectObj]
        exact TwistedCategory.tℓ _ _ _
    | coherence X Y f g hf hg =>
        apply coherence <;> apply projectMapAux_Pure <;> assumption

def project : T C ⥤ D where
  obj := projectObj m
  map := projectMap m
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

variable {D : Type u'} (m : C → D)

def projectFree : T C ⥤ T D := project (fun c ↦ (of (m c)))

open FreeTwistedCategoryQuiver

def Tcat : Category.{u} (T C) := inferInstance
scoped infixr:10 " ⟶T " => Tcat.Hom

variable [Quiver.{v} (T C)]

@[simp]
def embedMapAux : ∀ {X Y : T C}, (X ⟶t Y) → ((FreeTwistedCategoryQuiver.mk X) ⟶ ⟨Y⟩)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, l_hom _ => (λ_ _).hom
  | _, _, l_inv _ => (λ_ _).inv
  | _, _, ρ_hom _ => (ρ_ _).hom
  | _, _, ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.comp f g => embedMapAux f ≫ embedMapAux g
  | _, _, Hom.whiskerLeft X p => ⟨X⟩ ◁ embedMapAux p
  | _, _, Hom.whiskerRight p X => embedMapAux p ▷ ⟨X⟩
  | _, _, Hom.tensor f g => embedMapAux f ⊗ₘ embedMapAux g
  | _, _, Hom.star f => (embedMapAux f)⋆
  | _, _, χ_hom _ _ => (χ_ _ _).hom
  | _, _, χ_inv _ _ => (χ_ _ _).inv
  | _, _, ε_hom _ => (e_ _).hom
  | _, _, ε_inv _ => (e_ _).inv
  | _, _, twist_hom _ => (ς_ _).hom
  | _, _, twist_inv _ => (ς_ _).inv

lemma embedMapAux_Pure : ∀ {X Y : T C} (f : X ⟶t Y),
    f.Pure → InvolutiveCoherence (embedMapAux f) := by
  intro X Y f hf
  induction f <;> simp_all
  all_goals constructor <;> assumption

#check MonoidalCategory.leftUnitor_naturality

@[simp]
def embedMap {X Y : T C} : (X ⟶T Y) → (FreeTwistedCategoryQuiver.mk X ⟶ ⟨Y⟩) :=
  _root_.Quotient.lift embedMapAux <| by
    intro f g h
    induction h with
    | refl => rfl
    | symm _ _ _ hfg' => exact hfg'.symm
    | trans _ _ hfg hgh => exact hfg.trans hgh
    | comp _ _ hf hg => dsimp only [embedMapAux]; rw [hf, hg]
    | whiskerLeft _ _ _ _ hf => dsimp only [embedMapAux]; rw [hf]
    | whiskerRight _ _ _ _ hf => dsimp only [embedMapAux]; rw [hf]
    | tensor _ _ hfg hfg' => dsimp only [embedMapAux]; rw [hfg, hfg']
    | tensorHom_def f g =>
        dsimp only [embedMapAux]; rw [MonoidalCategory.tensorHom_def]
    | comp_id => dsimp only [embedMapAux]; rw [Category.comp_id]
    | id_comp => dsimp only [embedMapAux]; rw [Category.id_comp]
    | assoc => dsimp only [embedMapAux]; rw [Category.assoc]
    /- | id_tensorHom_id => dsimp only [embedMapAux]; rw [MonoidalCategory.id_tensorHom_id]; rfl -/
    | tensorHom_comp_tensorHom =>
      dsimp only [embedMapAux]; rw [MonoidalCategory.tensorHom_comp_tensorHom]
    | whiskerLeft_id =>
        dsimp only [embedMapAux]; simp; rfl
    | id_whiskerRight =>
        dsimp only [embedMapAux]; simp; rfl
    /- | α_hom_inv => dsimp only [embedMapAux]; rw [Iso.hom_inv_id] -/
    /- | α_inv_hom => dsimp only [embedMapAux]; rw [Iso.inv_hom_id] -/
    | associator_naturality =>
        dsimp only [embedMapAux]; rw [MonoidalCategory.associator_naturality]
    /- | ρ_hom_inv => dsimp only [embedMapAux]; rw [Iso.hom_inv_id] -/
    /- | ρ_inv_hom => dsimp only [embedMapAux]; rw [Iso.inv_hom_id] -/
    | ρ_naturality f =>
        simp
        rw [← MonoidalCategory.rightUnitor_naturality]
        rfl
    /- | l_hom_inv => dsimp only [embedMapAux]; rw [Iso.hom_inv_id] -/
    /- | l_inv_hom => dsimp only [embedMapAux]; rw [Iso.inv_hom_id] -/
    | l_naturality =>
        simp
        rw [← MonoidalCategory.leftUnitor_naturality]
        rfl
    /- | pentagon => -/
    /-     dsimp only [embedMapAux, FreeTwistedCategory.embed] -/
    /-     rw [MonoidalCategory.pentagon] -/
    /- | triangle => -/
    /-     dsimp only [embedMapAux, FreeTwistedCategory.embed] -/
    /-     rw [MonoidalCategory.triangle] -/
    -- START NAT'S STUFF
    | star _ hf => dsimp only [embedMapAux]; rw [hf]
    | starHom_comp_starHom _ hf =>
        dsimp only [embedMapAux]; rw [InvolutiveCategory.starHom_comp_starHom]
    /- | starHom_id => -/
    /-     dsimp only [embedMapAux, FreeTwistedCategory.embed] -/
    /-     rw [InvolutiveCategory.starHom_id] -/
    /- | ε_hom_inv => dsimp only [embedMapAux]; rw [Iso.hom_inv_id] -/
    /- | ε_inv_hom => dsimp only [embedMapAux]; rw [Iso.inv_hom_id] -/
    | ε_naturality =>
        dsimp only [embedMapAux]
        exact InvolutiveCategory.involutor_naturality _
    /- | χ_hom_inv => dsimp only [embedMapAux]; rw [Iso.hom_inv_id] -/
    /- | χ_inv_hom => dsimp only [embedMapAux]; rw [Iso.inv_hom_id] -/
    | χ_naturality =>
        dsimp only [embedMapAux]
        exact InvolutiveCategory.skewator_naturality _ _
    /- | f3 => -/
    /-     dsimp only [embedMapAux, FreeTwistedCategory.embed] -/
    /-     exact f3 _ _ _ -/
    /- | n2 => -/
    /-     dsimp only [embedMapAux, FreeTwistedCategory.embed] -/
    /-     exact n2 _ _ -/
    /- | a => -/
    /-     dsimp only [embedMapAux, FreeTwistedCategory.embed] -/
    /-     exact a _ -/
    | twist_hom_inv => dsimp only [embedMapAux]; simp
    | twist_inv_hom => dsimp only [embedMapAux]; simp
    | twist_naturality =>
        dsimp only [embedMapAux]
        exact TwistedCategory.twist_naturality _
    | tℓ =>
        dsimp only [embedMapAux]
        exact TwistedCategory.tℓ _ _ _
    | coherence X Y f g hf hg =>
        apply coherence <;> apply embedMapAux_Pure <;> assumption

def embed : T C ⥤ TQ C where
  obj := FreeTwistedCategoryQuiver.mk
  map := embedMap
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

@[simp] lemma embed_map_associator_hom (X Y Z : T C) :
    embed.map (α_ X Y Z).hom = (α_ _ _ _).hom := rfl
@[simp] lemma embed_map_associator_inv (X Y Z : T C) :
    embed.map (α_ X Y Z).inv = (α_ _ _ _).inv := rfl
@[simp] lemma embed_map_leftUnitor_hom (X : T C) :
    embed.map (λ_ X).hom = (λ_ _).hom := rfl
@[simp] lemma embed_map_leftUnitor_inv (X : T C) :
    embed.map (λ_ X).inv = (λ_ _).inv := rfl
@[simp] lemma embed_map_rightUnitor_hom (X : T C) :
    embed.map (ρ_ X).hom = (ρ_ _).hom := rfl
@[simp] lemma embed_map_rightUnitor_inv (X : T C) :
    embed.map (ρ_ X).inv = (ρ_ _).inv := rfl
@[simp] lemma embed_map_skewator_hom (X Y : T C) :
    embed.map (χ_ X Y).hom = (χ_ _ _).hom := rfl
@[simp] lemma embed_map_skewator_inv (X Y : T C) :
    embed.map (χ_ X Y).inv = (χ_ _ _).inv := rfl
@[simp] lemma embed_map_involutor_hom (X : T C) :
    embed.map (e_ X).hom = (e_ _).hom := rfl
@[simp] lemma embed_map_involutor_inv (X : T C) :
    embed.map (e_ X).inv = (e_ _).inv := rfl
@[simp] lemma embed_map_twist_hom (X : T C) :
    embed.map (ς_ X).hom = (ς_ _).hom := rfl
@[simp] lemma embed_map_twist_inv (X : T C) :
    embed.map (ς_ X).inv = (ς_ _).inv := rfl
@[simp] lemma embed_map_braid_hom (X Y : T C) :
    embed.map (σ_ X Y).hom = (σ_ _ _).hom := rfl
@[simp] lemma embed_map_braid_inv (X Y : T C) :
    embed.map (σ_ X Y).inv = (σ_ _ _).inv := rfl
@[simp] lemma embed_map_star (X Y : T C) (f : X ⟶T Y) :
    embed.map f⋆ = (embed.map f)⋆ := by
  induction f using Quotient.inductionOn
  unfold embed
  unfold InvolutiveCategoryStruct.starHom
  unfold instInvolutiveCategoryStruct
  simp
  unfold InvolutiveCategoryStruct.starHom
  unfold FreeTwistedCategoryQuiver.instInvolutiveCategoryStruct
  simp
@[simp] lemma embed_map_tensor (W X Y Z : T C) (f : W ⟶T Y) (g : X ⟶T Z) :
    embed.map (f ⊗ₘ g) = (embed.map f) ⊗ₘ (embed.map g) := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  unfold embed
  unfold MonoidalCategory.tensorHom
  unfold instMonoidalCategory
  simp
  unfold MonoidalCategory.tensorHom
  unfold FreeTwistedCategoryQuiver.instMonoidalCategory
  simp
@[simp] lemma embed_map_comp (X Y Z : T C) (f : X ⟶T Y) (g : Y ⟶T Z) :
    embed.map (f ≫ g) = (embed.map f) ≫ (embed.map g) := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  simp
@[simp] lemma embed_map_id (X : T C) :
    embed.map (𝟙 X) = 𝟙 (embed.obj X) := rfl
@[simp] lemma embed_map_whiskerLeft (X : T C) {Y₁ Y₂ : T C} (f : Y₁ ⟶T Y₂) :
    embed.map (X ◁ f) = (embed.obj X) ◁ (embed.map f) := by
  induction f using Quotient.inductionOn
  unfold embed
  unfold MonoidalCategory.whiskerLeft
  unfold instMonoidalCategory
  simp
  unfold MonoidalCategory.whiskerLeft
  unfold FreeTwistedCategoryQuiver.instMonoidalCategory
  simp
@[simp] lemma embed_map_whiskerRight {X₁ X₂ : T C} (f : X₁ ⟶T X₂) (Y : T C) :
    embed.map (f ▷ Y) = (embed.map f) ▷ (embed.obj Y) := by
  induction f using Quotient.inductionOn
  unfold embed
  unfold MonoidalCategory.whiskerRight
  unfold instMonoidalCategory
  simp
  unfold MonoidalCategory.whiskerRight
  unfold FreeTwistedCategoryQuiver.instMonoidalCategory
  simp

@[simp] lemma embed_obj (X : T C) : embed.obj X = ⟨X⟩ := rfl

end CategoryTheory.FreeTwistedCategory

