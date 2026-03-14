import Mathlib
import LeanCategory.Instances

/-!
# Projection functor

This file defines the projection of labels along a partial map, as a functor on
`MonoidalWord` and on braid morphisms.
-/

open CategoryTheory

universe u

namespace BraidGroupoid

open CategoryTheory
open scoped MonoidalCategory
open scoped BraidGroupoid

-- TODO look into defining Hom.map
/-- Map a braid morphism by projecting its labels with a partial function. -/
def Hom.project (map : α → Option β) : (X ⟶ᵇ Y) → (X.project map ⟶ᵇ Y.project map)
    | .id X => 1
    | .α_hom X Y Z => .α_hom (X.project map) (Y.project map) (Z.project map)
    | .α_inv X Y Z => .α_inv (X.project map) (Y.project map) (Z.project map)
    | .l_hom X => .l_hom (X.project map)
    | .l_inv X => .l_inv (X.project map)
    | .ρ_hom X => .ρ_hom (X.project map)
    | .ρ_inv X => .ρ_inv (X.project map)
    | .σ_hom X Y => .σ_hom (X.project map) (Y.project map)
    | .σ_inv X Y => .σ_inv (X.project map) (Y.project map)
    | .comp f g => .comp (f.project map) (g.project map)
    | .tensor f g => .tensor (f.project map) (g.project map)

/-- Project braid relations along a label map. -/
def HomEquiv.project {α β : Type u} {X Y : MonoidalWord α} (map : α → Option β)
    {f g : X ⟶ᵇ Y} : HomEquiv f g → HomEquiv (f.project map) (g.project map) := by
  intro h
  induction h with
  | refl f => rfl
  | symm h ih => symm; assumption
  | trans hfg hgh ihfg ihgh => apply trans ihfg ihgh
  | comp hf hg ihf ihg => apply comp ihf ihg
  | tensor hf hg ihf ihg => apply tensor ihf ihg
  | comp_id f => apply comp_id (f.project map)
  | id_comp f => apply id_comp (f.project map)
  | assoc f g h =>
      apply assoc (f.project map) (g.project map) (h.project map)
  | id_tensorHom_id => apply id_tensorHom_id
  | tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ =>
      apply tensorHom_comp_tensorHom (f₁.project map) (f₂.project map)
        (g₁.project map) (g₂.project map)
  | α_hom_inv => apply α_hom_inv
  | α_inv_hom => apply α_inv_hom
  | α_naturality f₁ f₂ f₃ =>
      apply α_naturality (f₁.project map) (f₂.project map) (f₃.project map)
  | ρ_hom_inv => apply ρ_hom_inv
  | ρ_inv_hom => apply ρ_inv_hom
  | ρ_naturality f => apply ρ_naturality (f.project map)
  | l_hom_inv => apply l_hom_inv
  | l_inv_hom => apply l_inv_hom
  | l_naturality f => apply l_naturality (f.project map)
  | pentagon => apply pentagon
  | triangle => apply triangle
  | σ_inv_left => apply σ_inv_left
  | σ_inv_right => apply σ_inv_right
  | braiding_naturality_right f =>
      apply braiding_naturality_right (f.project map)
  | braiding_naturality_left f Z =>
      apply braiding_naturality_left (f.project map) (Z.project map)
  | hexagon_forward => apply hexagon_forward
  | hexagon_reverse => apply hexagon_reverse

/--
The projection functor induced by a partial label map.
-/
@[simp]
def projectFunctor {α β : Type u} (map : α → Option β) : MonoidalWord α ⥤ MonoidalWord β where
    obj X := X.project map
    map {X Y} f :=
        Quotient.lift (⟦·.project map⟧) (by
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
