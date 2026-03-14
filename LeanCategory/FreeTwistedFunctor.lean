import LeanCategory.FreeTwistedCategory
import LeanCategory.FreeTwistedCategoryQuiver

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

variable (M : {X Y : T C} → (X ⟶ Y) → ((X.map m) ⟶ (Y.map m)))

def projectFree : T C ⥤ T D := project (fun c ↦ (of (m c)))

open FreeTwistedCategoryQuiver

def embed : T C ⥤ TQ C := project FreeTwistedCategoryQuiver.of

end CategoryTheory.FreeTwistedCategory

