import LeanCategory.FreeTwistedQuiver.Instance
import LeanCategory.FreeTwisted.Instance

namespace CategoryTheory.FreeTwistedCategoryQuiver

open scoped FreeTwistedCategory -- just the T notation
variable {C : Type u} [Quiver.{v} (T C)]

variable {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [InvolutiveCategory D] [TwistedCategory D] (m : C → D)

open MonoidalCategory
open InvolutiveCategory
open TwistedCategory

variable (M : {X Y : T C} → (X ⟶ Y) → ((X.projectObj m) ⟶ (Y.projectObj m)))

open Hom

@[simp]
def projectMapAux : ∀ {X Y : TQ C}, (X ⟶tq Y) → (X.projectObj m ⟶ Y.projectObj m)
  | _, _, Hom.of f => M f
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

lemma projectMapAux_Pure : ∀ {X Y : TQ C} (f : X ⟶tq Y),
    f.Pure → InvolutiveCoherence (projectMapAux m M f) := by
  intro X Y f hf
  induction f <;> simp_all
  all_goals constructor <;> assumption

@[simp]
def projectMap {X Y : TQ C} : (X ⟶ Y) → (X.projectObj m ⟶ Y.projectObj m) :=
  _root_.Quotient.lift (projectMapAux m M) <| by
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
    | tensorHom_comp_tensorHom =>
      dsimp only [projectMapAux]; rw [MonoidalCategory.tensorHom_comp_tensorHom]
    | whiskerLeft_id =>
        dsimp only [projectMapAux]; simp
    | id_whiskerRight =>
        dsimp only [projectMapAux]; simp
    | associator_naturality =>
        dsimp only [projectMapAux]; rw [MonoidalCategory.associator_naturality]
    | ρ_naturality f =>
        dsimp only [projectMapAux]; simp
    | l_naturality =>
        dsimp only [projectMapAux]; simp
    -- START NAT'S STUFF
    | star _ hf => dsimp only [projectMapAux]; rw [hf]
    | starHom_comp_starHom _ hf =>
        dsimp only [projectMapAux]; rw [InvolutiveCategory.starHom_comp_starHom]
    | ε_naturality =>
        dsimp only [projectMapAux]
        exact InvolutiveCategory.involutor_naturality _
    | χ_naturality =>
        dsimp only [projectMapAux, projectObj]
        exact InvolutiveCategory.skewator_naturality _ _
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

def project : TQ C ⥤ D where
  obj := projectObj m
  map := projectMap m M
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

variable {D : Type u'} [Quiver.{v'} (T D)] (m : C → D)

variable (M : {X Y : T C} → (X ⟶ Y) → ((X.map m) ⟶ (Y.map m)))

def projectFree : TQ C ⥤ TQ D := project (fun c ↦ (of (m c))) <| fun f ↦ homMk <| .of <| by
  simp
  exact M f

end CategoryTheory.FreeTwistedCategoryQuiver

