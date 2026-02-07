import Mathlib
import LeanCategory.Morphisms

/-!
# Braid groupoid relations

This file defines the congruence relation on formal braid morphisms.
-/

universe u

namespace BraidGroupoid

open scoped BraidGroupoid

/-- Relations for the braid groupoid. -/
@[grind]
inductive HomEquiv {α : Type u} : ∀ {X Y : MonoidalWord α}, (X ⟶ᵇ Y) → (X ⟶ᵇ Y) → Prop
    | refl {X Y} (f : X ⟶ᵇ Y) : HomEquiv f f
    | comp {X Y Z} {f f' : X ⟶ᵇ Y} {g g' : Y ⟶ᵇ Z} :
        HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
    | tensor {W X Y Z} {f f' : W ⟶ᵇ X} {g g' : Y ⟶ᵇ Z} :
        HomEquiv f f' → HomEquiv g g' → HomEquiv (f.tensor g) (f'.tensor g')
    | comp_id {X Y} (f : X ⟶ᵇ Y) : HomEquiv (f.comp (Hom.id _)) f
    | id_comp {X Y} (f : X ⟶ᵇ Y) : HomEquiv ((Hom.id _).comp f) f
    | assoc {X Y U V : MonoidalWord α} (f : X ⟶ᵇ U) (g : U ⟶ᵇ V) (h : V ⟶ᵇ Y) :
        HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
    | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
    | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : MonoidalWord α}
        (f₁ : X₁ ⟶ᵇ Y₁) (f₂ : X₂ ⟶ᵇ Y₂) (g₁ : Y₁ ⟶ᵇ Z₁) (g₂ : Y₂ ⟶ᵇ Z₂) :
        HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂))
            ((f₁.comp g₁).tensor (f₂.comp g₂))
    | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
    | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
    | α_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃}
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
    | symm {X Y} {f g : X ⟶ᵇ Y} : HomEquiv f g → HomEquiv g f
    | trans {X Y} {f g h : X ⟶ᵇ Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h

instance : HasEquiv (X ⟶ᵇ Y) where
    Equiv := HomEquiv

@[grind]
lemma HomEquiv.equiv' : HomEquiv f g → f ≈ g := id

/-- Reflexivity for `HomEquiv`. -/
@[refl]
def HomEquiv.refl' {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵇ Y) : HomEquiv f f := .refl f

/-- Reflexivity for `HomEquiv`. -/
@[refl]
def HomEquiv.refl'' {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵇ Y) : f ≈ f := .refl f

/-- Symmetry for `HomEquiv`. -/
@[symm]
def HomEquiv.symm' {α : Type u} {X Y : MonoidalWord α} {f g : X ⟶ᵇ Y}
    (h : f ≈ g) : HomEquiv g f := .symm h

/-- Symmetry for `HomEquiv`. -/
@[symm]
def HomEquiv.symm'' {α : Type u} {X Y : MonoidalWord α} {f g : X ⟶ᵇ Y}
    (h : f ≈ g) : g ≈ f := .symm h

instance : Trans (HomEquiv (α := α) (X := X) (Y := Y)) (HomEquiv) (HomEquiv) where
    trans := HomEquiv.trans

instance : Trans (α := X ⟶ᵇ Y) (· ≈ ·) (· ≈ ·) (· ≈ ·) where
  trans := .trans

instance : Equivalence (HomEquiv (α := α) (X := X) (Y := Y)) where
    refl := HomEquiv.refl
    symm := HomEquiv.symm
    trans := HomEquiv.trans

/-- Congruence under left whiskering. -/
@[grind]
lemma HomEquiv.whiskerLeft (X : MonoidalWord α) {Y Z} (f f' : Y ⟶ᵇ Z) :
        f ≈ f' → f.whiskerLeft X ≈ f'.whiskerLeft X :=
    by
        intro h
        exact HomEquiv.tensor (by rfl) h

/-- Congruence under right whiskering. -/
@[grind]
lemma HomEquiv.whiskerRight {X Y} (f f' : X ⟶ᵇ Y) (Z : MonoidalWord α) :
        f ≈ f' → f.whiskerRight Z ≈ f'.whiskerRight Z :=
    by
        intro h
        exact HomEquiv.tensor h (by rfl)

/-- Relation between tensoring and whiskering in the quotient. -/
@[grind]
lemma HomEquiv.tensorHom_def {X₁ Y₁ X₂ Y₂ : MonoidalWord α} (f : X₁ ⟶ᵇ Y₁)
    (g : X₂ ⟶ᵇ Y₂) :
    f.tensor g ≈ ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁)) := by
  simp
  symm
  exact calc
    _ ≈ _ := by
      apply tensorHom_comp_tensorHom
    _ ≈ f * g := by
      apply tensor
      · apply comp_id
      · apply id_comp

/-- Left whiskering by identity is identity on the tensor. -/
@[grind]
lemma HomEquiv.whiskerLeft_id (X Y : MonoidalWord α) :
        ((1 : (Y ⟶ᵇ Y)).whiskerLeft X) ≈ 1 :=
    id_tensorHom_id

/-- Right whiskering by identity is identity on the tensor. -/
@[grind]
lemma HomEquiv.id_whiskerRight (X Y : MonoidalWord α) :
        ((1 : (X ⟶ᵇ X)).whiskerRight Y) ≈ 1 :=
    id_tensorHom_id

/-! ## Enrichment -/

/-- `Hom.transport` is invariant under `HomEquiv`. -/
def HomEquiv.transport {α β : Type u} {X Y : MonoidalWord α}
    {f g : X ⟶ᵇ Y} (h : f ≈ g) (A : X.Match β) :
    f.transport A = g.transport A := by
  induction h
  any_goals match_simplify A
  all_goals cat_disch

end BraidGroupoid
