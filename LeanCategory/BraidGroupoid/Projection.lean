import Mathlib
import LeanCategory.BraidGroupoid.Instances

/-!
# Projection functor

This file defines the projection of labels along a partial map, as a functor on
`MonoidalWord` and on braid morphisms.
-/

open CategoryTheory
#check Functor.op

universe u

namespace BraidGroupoid

open CategoryTheory
open scoped MonoidalCategory
open scoped BraidGroupoid

/-- Map a braid morphism by projecting its labels with a partial function. -/
def Hom.project (map : α → Option β) : (X ⟶ᵇ Y) → (X.project map ⟶ᵇ Y.project map)
    | Hom.id X => Hom.id (X.project map)
    | Hom.α_hom X Y Z => Hom.α_hom (X.project map) (Y.project map) (Z.project map)
    | Hom.α_inv X Y Z => Hom.α_inv (X.project map) (Y.project map) (Z.project map)
    | Hom.l_hom X => Hom.l_hom (X.project map)
    | Hom.l_inv X => Hom.l_inv (X.project map)
    | Hom.ρ_hom X => Hom.ρ_hom (X.project map)
    | Hom.ρ_inv X => Hom.ρ_inv (X.project map)
    | Hom.σ X Y => Hom.σ (X.project map) (Y.project map)
    | Hom.σ_inv X Y => Hom.σ_inv (X.project map) (Y.project map)
    | Hom.comp f g => Hom.comp (f.project map) (g.project map)
    | Hom.tensor f g => Hom.tensor (f.project map) (g.project map)

/-- Project braid relations along a label map. -/
def HomEquiv.project {α β : Type u} {X Y : MonoidalWord α} (map : α → Option β)
        {f g : X ⟶ᵇ Y} : HomEquiv f g → HomEquiv (f.project map) (g.project map) := by
    intro h
    induction h with
    | refl f => exact HomEquiv.refl _
    | symm h ih => exact HomEquiv.symm ih
    | trans hfg hgh ihfg ihgh => exact HomEquiv.trans ihfg ihgh
    | comp hf hg ihf ihg => exact HomEquiv.comp ihf ihg
    | tensor hf hg ihf ihg => exact HomEquiv.tensor ihf ihg
    | comp_id f => exact HomEquiv.comp_id (f.project map)
    | id_comp f => exact HomEquiv.id_comp (f.project map)
    | assoc f g h => exact HomEquiv.assoc (f.project map) (g.project map) (h.project map)
    | id_tensorHom_id => exact HomEquiv.id_tensorHom_id
    | tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ =>
        exact HomEquiv.tensorHom_comp_tensorHom (f₁.project map) (f₂.project map)
            (g₁.project map) (g₂.project map)
    | α_hom_inv => exact HomEquiv.α_hom_inv
    | α_inv_hom => exact HomEquiv.α_inv_hom
    | α_naturality f₁ f₂ f₃ =>
        exact HomEquiv.α_naturality (f₁.project map) (f₂.project map) (f₃.project map)
    | ρ_hom_inv => exact HomEquiv.ρ_hom_inv
    | ρ_inv_hom => exact HomEquiv.ρ_inv_hom
    | ρ_naturality f => exact HomEquiv.ρ_naturality (f.project map)
    | l_hom_inv => exact HomEquiv.l_hom_inv
    | l_inv_hom => exact HomEquiv.l_inv_hom
    | l_naturality f => exact HomEquiv.l_naturality (f.project map)
    | pentagon => exact HomEquiv.pentagon
    | triangle => exact HomEquiv.triangle
    | σ_inv_left => exact HomEquiv.σ_inv_left
    | σ_inv_right => exact HomEquiv.σ_inv_right
    | braiding_naturality_right f =>
        exact HomEquiv.braiding_naturality_right (f.project map)
    | braiding_naturality_left f Z =>
        exact HomEquiv.braiding_naturality_left (f.project map) (Z.project map)
    | hexagon_forward => exact HomEquiv.hexagon_forward
    | hexagon_reverse => exact HomEquiv.hexagon_reverse

/--
The projection functor induced by a partial label map.
-/
@[simp]
def projectFunctor {α β : Type u} (map : α → Option β) : MonoidalWord α ⥤ MonoidalWord β where
    obj X := X.project map
    map {X Y} f :=
        Quotient.lift (fun g => ⟦g.project map⟧) (by
            intro g h hg
            exact Quotient.sound (HomEquiv.project map hg)) f
    map_comp {X Y Z} := by
        rintro ⟨f⟩ ⟨g⟩
        rfl

/-- The projection functor is lax monoidal with identity unit and tensorator. -/
@[simp]
instance projectFunctor_laxMonoidal {α β : Type u} (map : α → Option β) :
        (projectFunctor map).LaxMonoidal where
    ε := 𝟙 _
    μ _ _ := 𝟙 _
    μ_natural_left := by
        rintro X Y ⟨f⟩ X'
        cat_disch
    μ_natural_right := by
        rintro X Y X' ⟨f⟩
        cat_disch

/-- The projection functor preserves braiding strictly. -/
instance projectFunctor_laxBraided {α β : Type u} (map : α → Option β) :
        (projectFunctor map).LaxBraided where

end BraidGroupoid
