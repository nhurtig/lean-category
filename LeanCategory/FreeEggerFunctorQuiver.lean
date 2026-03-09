import LeanCategory.FreeEggerQuiver

namespace CategoryTheory.FreeTwistedCategoryQuiver

variable {C : Type u} [Quiver.{v} (FQ C)]

variable {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [InvolutiveCategory D] [TwistedCategory D] (m : C → D)

open MonoidalCategory
open InvolutiveCategory
open TwistedCategory

def projectObj : FQ C → D
  | .of X => m X
  | .unit => 𝟙_ D
  | .tensor X Y => X.projectObj ⊗ Y.projectObj
  | .star X => X.projectObj⋆

variable (M : {X Y : FQ C} → (X ⟶ Y) → ((X.projectObj m) ⟶ (Y.projectObj m)))

open Hom

def projectMapAux : ∀ {X Y : FQ C}, (X ⟶ᵐ Y) → (projectObj m X ⟶ projectObj m Y)
  | _, _, Hom.of f => M f
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, l_hom _ => (λ_ _).hom
  | _, _, l_inv _ => (λ_ _).inv
  | _, _, ρ_hom _ => (ρ_ _).hom
  | _, _, ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.comp f g => projectMapAux f ≫ projectMapAux g
  | _, _, Hom.whiskerLeft X p => projectObj m X ◁ projectMapAux p
  | _, _, Hom.whiskerRight p X => projectMapAux p ▷ projectObj m X
  | _, _, Hom.tensor f g => projectMapAux f ⊗ₘ projectMapAux g
  | _, _, Hom.star f => (projectMapAux f)⋆
  | _, _, χ_hom _ _ => (χ_ _ _).hom
  | _, _, χ_inv _ _ => (χ_ _ _).inv
  | _, _, ε_hom _ => (e_ _).hom
  | _, _, ε_inv _ => (e_ _).inv
  | _, _, twist_hom _ => (ς_ _).hom
  | _, _, twist_inv _ => (ς_ _).inv

@[simp]
def projectMap (X Y : FQ C) : (categoryFreeTwistedCategoryQuiver.Hom X Y) →
    (projectObj m X ⟶ projectObj m Y) :=
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
        dsimp only [projectMapAux, projectObj]; rw [MonoidalCategory.tensorHom_def]
    | comp_id => dsimp only [projectMapAux]; rw [Category.comp_id]
    | id_comp => dsimp only [projectMapAux]; rw [Category.id_comp]
    | assoc => dsimp only [projectMapAux]; rw [Category.assoc]
    | id_tensorHom_id => dsimp only [projectMapAux]; rw [MonoidalCategory.id_tensorHom_id]; rfl
    | tensorHom_comp_tensorHom =>
      dsimp only [projectMapAux]; rw [MonoidalCategory.tensorHom_comp_tensorHom]
    | whiskerLeft_id =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.whiskerLeft_id]
    | id_whiskerRight =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.id_whiskerRight]
    | α_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | α_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | associator_naturality =>
        dsimp only [projectMapAux]; rw [MonoidalCategory.associator_naturality]
    | ρ_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | ρ_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | ρ_naturality =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.rightUnitor_naturality]
    | l_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | l_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | l_naturality =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.leftUnitor_naturality]
    | pentagon =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.pentagon]
    | triangle =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.triangle]
    -- START NAT'S STUFF
    | star _ hf => dsimp only [projectMapAux]; rw [hf]
    | starHom_comp_starHom _ hf =>
      dsimp only [projectMapAux]; rw [InvolutiveCategory.starHom_comp_starHom]
    | starHom_id => dsimp only [projectMapAux, projectObj]; rw [InvolutiveCategory.starHom_id]
    | ε_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | ε_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | ε_naturality =>
        dsimp only [projectMapAux, projectObj]
        exact InvolutiveCategory.involutor_naturality _
    | χ_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | χ_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | χ_naturality =>
        dsimp only [projectMapAux, projectObj]
        exact InvolutiveCategory.skewator_naturality _ _
    | f3 =>
        dsimp only [projectMapAux, projectObj]
        exact f3 _ _ _
    | n2 =>
        dsimp only [projectMapAux, projectObj]
        exact n2 _ _
    | a =>
        dsimp only [projectMapAux, projectObj]
        exact a _
    | twist_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | twist_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | twist_naturality =>
        dsimp only [projectMapAux, projectObj]
        exact TwistedCategory.twist_naturality _
    | tℓ =>
        dsimp only [projectMapAux, projectObj]
        exact TwistedCategory.tℓ _ _ _

def project : FQ C ⥤ D where
  obj := projectObj m
  map := projectMap m M _ _
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

variable {D : Type u'} [Quiver.{v'} (FQ D)] (m : C → D)

variable (M : {X Y : FQ C} → (X ⟶ Y) →
  ((X.projectObj (FreeTwistedCategoryQuiver.of <| m ·)) ⟶ (Y.projectObj (.of <| m ·))))

def projectFree : FQ C ⥤ FQ D := project (.of <| m ·) (⟦Hom.of <| M ·⟧)

end CategoryTheory.FreeTwistedCategoryQuiver

