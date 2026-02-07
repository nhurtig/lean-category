import Mathlib
import LeanCategory.BraidGroupoid.Morphisms

/-!
# Braid groupoid relations

This file defines the congruence relation on formal braid morphisms.
-/

universe u

namespace BraidGroupoid

open scoped BraidGroupoid

/-- Relations for the braid groupoid. -/
inductive HomEquiv {α : Type u} : ∀ {X Y : MonoidalWord α}, (X ⟶ᵇ Y) → (X ⟶ᵇ Y) → Prop
    | refl {X Y} (f : X ⟶ᵇ Y) : HomEquiv f f
    | symm {X Y} (f g : X ⟶ᵇ Y) : HomEquiv f g → HomEquiv g f
    | trans {X Y} {f g h : X ⟶ᵇ Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h
    | comp {X Y Z} {f f' : X ⟶ᵇ Y} {g g' : Y ⟶ᵇ Z} :
        HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
    | whiskerLeft (X) {Y Z} (f f' : Y ⟶ᵇ Z) :
        HomEquiv f f' → HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
    | whiskerRight {Y Z} (f f' : Y ⟶ᵇ Z) (X) :
        HomEquiv f f' → HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
    | tensor {W X Y Z} {f f' : W ⟶ᵇ X} {g g' : Y ⟶ᵇ Z} :
        HomEquiv f f' → HomEquiv g g' → HomEquiv (f.tensor g) (f'.tensor g')
    | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶ᵇ Y₁) (g : X₂ ⟶ᵇ Y₂) :
        HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
    | comp_id {X Y} (f : X ⟶ᵇ Y) : HomEquiv (f.comp (Hom.id _)) f
    | id_comp {X Y} (f : X ⟶ᵇ Y) : HomEquiv ((Hom.id _).comp f) f
    | assoc {X Y U V : MonoidalWord α} (f : X ⟶ᵇ U) (g : U ⟶ᵇ V) (h : V ⟶ᵇ Y) :
        HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
    | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
    | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : MonoidalWord α}
        (f₁ : X₁ ⟶ᵇ Y₁) (f₂ : X₂ ⟶ᵇ Y₂) (g₁ : Y₁ ⟶ᵇ Z₁) (g₂ : Y₂ ⟶ᵇ Z₂) :
        HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂))
            ((f₁.comp g₁).tensor (f₂.comp g₂))
    | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
    | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
    | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
    | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
    | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃}
        (f₁ : X₁ ⟶ᵇ Y₁) (f₂ : X₂ ⟶ᵇ Y₂) (f₃ : X₃ ⟶ᵇ Y₃) :
        HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
            ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
    | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
    | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
    | ρ_naturality {X Y} (f : X ⟶ᵇ Y) :
        HomEquiv ((f.whiskerRight MonoidalWord.unit).comp (Hom.ρ_hom Y))
            ((Hom.ρ_hom X).comp f)
    | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
    | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
    | l_naturality {X Y} (f : X ⟶ᵇ Y) :
        HomEquiv ((f.whiskerLeft MonoidalWord.unit).comp (Hom.l_hom Y))
            ((Hom.l_hom X).comp f)
    | pentagon {W X Y Z} :
        HomEquiv
            (((Hom.α_hom W X Y).whiskerRight Z).comp
                ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
            ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
    | triangle {X Y} :
        HomEquiv ((Hom.α_hom X MonoidalWord.unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
            ((Hom.ρ_hom X).whiskerRight Y)
    | σ_inv_left {X Y} : HomEquiv ((Hom.σ X Y).comp (Hom.σ_inv X Y)) (Hom.id _)
    | σ_inv_right {X Y} : HomEquiv ((Hom.σ_inv X Y).comp (Hom.σ X Y)) (Hom.id _)
    | braiding_naturality_right {X Y Z} (f : Y ⟶ᵇ Z) :
        HomEquiv
            ((Hom.whiskerLeft X f).comp (Hom.σ X Z))
            ((Hom.σ X Y).comp (Hom.whiskerRight f X))
    | braiding_naturality_left {X Y} (f : X ⟶ᵇ Y) (Z) :
        HomEquiv
            ((Hom.whiskerRight f Z).comp (Hom.σ Y Z))
            ((Hom.σ X Z).comp (Hom.whiskerLeft Z f))
    | hexagon_forward {X Y Z} :
        HomEquiv
            ((Hom.α_hom X Y Z).comp
                ((Hom.σ X (Y.tensor Z)).comp (Hom.α_hom Y Z X)))
            (((Hom.σ X Y).whiskerRight Z).comp
                ((Hom.α_hom Y X Z).comp ((Hom.σ X Z).whiskerLeft Y)))
    | hexagon_reverse {X Y Z} :
        HomEquiv
            ((Hom.α_inv X Y Z).comp
                ((Hom.σ (X.tensor Y) Z).comp (Hom.α_inv Z X Y)))
            (((Hom.σ Y Z).whiskerLeft X).comp
                ((Hom.α_inv X Z Y).comp ((Hom.σ X Z).whiskerRight Y)))

/-! ## Enrichment -/

/-- `Hom.newMatch` is invariant under `HomEquiv`. -/
def HomEquiv.newMatch {α β : Type u} {X Y : MonoidalWord α}
    {f g : X ⟶ᵇ Y} (h : HomEquiv f g) (A : X.Match β) :
    Hom.newMatch f A = Hom.newMatch g A := by
  induction h
  any_goals match_simplify A
  all_goals cat_disch

/-- Enrich braid relations by replacing labels with a chosen assignment. -/
def HomEquiv.enrich {α β : Type u} {X Y : MonoidalWord α}
        {f g : X ⟶ᵇ Y} (h : HomEquiv f g) (A : X.Match β) :
        HomEquiv (Hom.enrich f A) ((by (have x : g.newCod A = f.newCod A := by simp [Hom.newCod]; rw [HomEquiv.newMatch h A]); exact x) ▸ Hom.enrich g A) := by
    induction h
    all_goals sorry
  -- | refl f =>
  --     exact HomEquiv.refl _
  -- | symm f g h ih =>
  --     exact HomEquiv.symm _ _ (ih A)
  -- | trans hfg hgh ihfg ihgh =>
  --     exact HomEquiv.trans (ihfg A) (ihgh A)
  -- | comp hf hg ihf ihg =>
  --     have hA : Hom.newMatch _ A = Hom.newMatch _ A := HomEquiv.newMatch hf A
  --     cases hA
  --     exact HomEquiv.comp (ihf A) (ihg (Hom.newMatch _ A))
  -- | whiskerLeft X f f' hf ih =>
  --     cases A with
  --     | tensor A1 A2 =>
  --         exact HomEquiv.whiskerLeft _ _ _ (ih A2)
  -- | whiskerRight f f' X hf ih =>
  --     cases A with
  --     | tensor A1 A2 =>
  --         exact HomEquiv.whiskerRight _ _ _ (ih A1)
  -- | tensor hf hg ihf ihg =>
  --     cases A with
  --     | tensor A1 A2 =>
  --         exact HomEquiv.tensor (ihf A1) (ihg A2)
  -- | tensorHom_def f g =>
  --     cases A with
  --     | tensor A1 A2 =>
  --         exact HomEquiv.tensorHom_def (Hom.enrich f A1) (Hom.enrich g A2)
  -- | comp_id f =>
  --     exact HomEquiv.comp_id _
  -- | id_comp f =>
  --     exact HomEquiv.id_comp _
  -- | assoc f g h =>
  --     exact HomEquiv.assoc _ _ _
  -- | id_tensorHom_id =>
  --     exact HomEquiv.id_tensorHom_id
  -- | tensorHom_comp_tensorHom f1 f2 g1 g2 =>
  --     exact HomEquiv.tensorHom_comp_tensorHom _ _ _ _
  -- | whiskerLeft_id X Y =>
  --     exact HomEquiv.whiskerLeft_id _ _
  -- | id_whiskerRight X Y =>
  --     exact HomEquiv.id_whiskerRight _ _
  -- | α_hom_inv =>
  --     exact HomEquiv.α_hom_inv
  -- | α_inv_hom =>
  --     exact HomEquiv.α_inv_hom
  -- | associator_naturality f1 f2 f3 =>
  --     exact HomEquiv.associator_naturality _ _ _
  -- | ρ_hom_inv =>
  --     exact HomEquiv.ρ_hom_inv
  -- | ρ_inv_hom =>
  --     exact HomEquiv.ρ_inv_hom
  -- | ρ_naturality f =>
  --     exact HomEquiv.ρ_naturality _
  -- | l_hom_inv =>
  --     exact HomEquiv.l_hom_inv
  -- | l_inv_hom =>
  --     exact HomEquiv.l_inv_hom
  -- | l_naturality f =>
  --     exact HomEquiv.l_naturality _
  -- | pentagon =>
  --     exact HomEquiv.pentagon
  -- | triangle =>
  --     exact HomEquiv.triangle
  -- | σ_inv_left =>
  --     exact HomEquiv.σ_inv_left
  -- | σ_inv_right =>
  --     exact HomEquiv.σ_inv_right
  -- | braiding_naturality_right f =>
  --     exact HomEquiv.braiding_naturality_right _
  -- | braiding_naturality_left f Z =>
  --     exact HomEquiv.braiding_naturality_left _ _
  -- | hexagon_forward =>
  --     exact HomEquiv.hexagon_forward
  -- | hexagon_reverse =>
  --     exact HomEquiv.hexagon_reverse


end BraidGroupoid
