import Mathlib
import LeanCategory.BraidGroupoid.Relations

/-!
# Braid groupoid instances

This file builds the category, monoidal, braided, and groupoid structures on
`MonoidalWord` by quotienting formal morphisms by `HomEquiv`.
-/

universe u

namespace BraidGroupoid

open CategoryTheory
open MonoidalCategory
open scoped BraidGroupoid

/-- Setoid for braid morphisms. -/
def setoidHom {α : Type u} (X Y : MonoidalWord α) : Setoid (X ⟶ᵇ Y) :=
    ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

section BraidInstance

open HomEquiv

/-- The category structure on `MonoidalWord`, quotienting by braid relations. -/
instance (α : Type u) : Category.{u} (MonoidalWord α) where
    Hom X Y := Quotient (BraidGroupoid.setoidHom X Y)
    id X := ⟦Hom.id X⟧
    comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg)
    id_comp := by
        rintro X Y ⟨f⟩
        exact Quotient.sound (id_comp f)
    comp_id := by
        rintro X Y ⟨f⟩
        exact Quotient.sound (comp_id f)
    assoc := by
        rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
        exact Quotient.sound (assoc f g h)

/-- The monoidal structure induced by formal tensoring of words and morphisms. -/
instance (α : Type u) : MonoidalCategory (MonoidalWord α) where
    tensorObj X Y := MonoidalWord.tensor X Y
    tensorHom := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg)
    whiskerLeft X _ _ f :=
        Quot.map (fun f ↦ Hom.whiskerLeft X f) (fun f f' ↦ .whiskerLeft X f f') f
    whiskerRight f Y :=
        Quot.map (fun f ↦ Hom.whiskerRight f Y) (fun f f' ↦ .whiskerRight f f' Y) f
    tensorHom_def {W X Y Z} := by
        rintro ⟨f⟩ ⟨g⟩
        exact Quotient.sound (tensorHom_def _ _)
    id_tensorHom_id _ _ := Quot.sound id_tensorHom_id
    tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} := by
        rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
        exact Quotient.sound (tensorHom_comp_tensorHom _ _ _ _)
    whiskerLeft_id X Y := Quot.sound (HomEquiv.whiskerLeft_id X Y)
    id_whiskerRight X Y := Quot.sound (HomEquiv.id_whiskerRight X Y)
    tensorUnit := MonoidalWord.unit
    associator X Y Z :=
        ⟨⟦Hom.α_hom X Y Z⟧, ⟦Hom.α_inv X Y Z⟧, Quotient.sound α_hom_inv,
            Quotient.sound α_inv_hom⟩
    associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} := by
        rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
        exact Quotient.sound (associator_naturality _ _ _)
    leftUnitor X :=
        ⟨⟦Hom.l_hom X⟧, ⟦Hom.l_inv X⟧, Quotient.sound l_hom_inv,
            Quotient.sound l_inv_hom⟩
    leftUnitor_naturality {X Y} := by
        rintro ⟨f⟩
        exact Quotient.sound (l_naturality _)
    rightUnitor X :=
        ⟨⟦Hom.ρ_hom X⟧, ⟦Hom.ρ_inv X⟧, Quotient.sound ρ_hom_inv,
            Quotient.sound ρ_inv_hom⟩
    rightUnitor_naturality {X Y} := by
        rintro ⟨f⟩
        exact Quotient.sound (ρ_naturality _)
    pentagon _ _ _ _ := Quotient.sound pentagon
    triangle _ _ := Quotient.sound triangle

/-- The braided structure coming from the formal crossing generators. -/
instance (α : Type u) : BraidedCategory (MonoidalWord α) where
    braiding X Y :=
        ⟨⟦Hom.σ X Y⟧, ⟦Hom.σ_inv X Y⟧,
            Quotient.sound σ_inv_left, Quotient.sound σ_inv_right⟩
    braiding_naturality_right := by
        rintro X Y Z ⟨f⟩
        exact Quotient.sound (HomEquiv.braiding_naturality_right f)
    braiding_naturality_left := by
        rintro X Y ⟨f⟩ Z
        exact Quotient.sound (HomEquiv.braiding_naturality_left f Z)
    hexagon_forward := by
        intro X Y Z
        exact Quotient.sound (HomEquiv.hexagon_forward (X := X) (Y := Y) (Z := Z))
    hexagon_reverse := by
        intro X Y Z
        exact Quotient.sound (HomEquiv.hexagon_reverse (X := X) (Y := Y) (Z := Z))

end BraidInstance

/-- Quotient computation for the braiding. -/
@[simp]
theorem mk_σ {α : Type u} {X Y : MonoidalWord α} :
        (⟦Hom.σ X Y⟧ : (X ⊗ Y) ⟶ (Y ⊗ X)) = (β_ X Y).hom :=
    rfl

/-- Quotient computation for the inverse braiding. -/
@[simp]
theorem mk_σ_inv {α : Type u} {X Y : MonoidalWord α} :
        (⟦Hom.σ_inv X Y⟧ : (Y ⊗ X) ⟶ (X ⊗ Y)) = (β_ X Y).inv :=
  rfl

/-- The abbreviation for `⟦f⟧` as a morphism. -/
abbrev homMk {α : Type u} {X Y : MonoidalWord α} (f : Hom X Y) : X ⟶ Y := ⟦f⟧

/-- Induction principle for morphisms in the quotient category. -/
theorem Hom.inductionOn {α : Type u}
        {motive : {X Y : MonoidalWord α} → (X ⟶ Y) → Prop} {X Y : MonoidalWord α} (t : X ⟶ Y)
        (id : (X : MonoidalWord α) → motive (𝟙 X))
        (α_hom : (X Y Z : MonoidalWord α) → motive (α_ X Y Z).hom)
        (α_inv : (X Y Z : MonoidalWord α) → motive (α_ X Y Z).inv)
        (l_hom : (X : MonoidalWord α) → motive (λ_ X).hom)
        (l_inv : (X : MonoidalWord α) → motive (λ_ X).inv)
        (ρ_hom : (X : MonoidalWord α) → motive (ρ_ X).hom)
        (ρ_inv : (X : MonoidalWord α) → motive (ρ_ X).inv)
        (σ_hom : (X Y : MonoidalWord α) → motive (⟦Hom.σ X Y⟧))
        (σ_inv : (X Y : MonoidalWord α) → motive (⟦Hom.σ_inv X Y⟧))
        (comp : {X Y Z : MonoidalWord α} → (f : X ⟶ Y) → (g : Y ⟶ Z) →
            motive f → motive g → motive (f ≫ g))
        (whiskerLeft : {Y Z : MonoidalWord α} → (X : MonoidalWord α) → (f : Y ⟶ Z) →
            motive f → motive (X ◁ f))
        (whiskerRight : {X Y : MonoidalWord α} → (f : X ⟶ Y) → (Z : MonoidalWord α) →
            motive f → motive (f ▷ Z)) :
        motive t := by
    apply Quotient.inductionOn
    intro f
    induction f with
    | id X => exact id X
    | α_hom X Y Z => exact α_hom X Y Z
    | α_inv X Y Z => exact α_inv X Y Z
    | l_hom X => exact l_hom X
    | l_inv X => exact l_inv X
    | ρ_hom X => exact ρ_hom X
    | ρ_inv X => exact ρ_inv X
    | σ X Y => exact σ_hom X Y
    | σ_inv X Y => exact σ_inv X Y
    | comp f g hf hg => exact comp _ _ (hf ⟦f⟧) (hg ⟦g⟧)
    | whiskerLeft X f hf => exact whiskerLeft X _ (hf ⟦f⟧)
    | whiskerRight f X hf => exact whiskerRight _ X (hf ⟦f⟧)
    | @tensor W X Y Z f g hf hg =>
        have : homMk f ⊗ₘ homMk g = homMk f ▷ X ≫ Y ◁ homMk g :=
            Quotient.sound (HomEquiv.tensorHom_def f g)
        change motive (homMk f ⊗ₘ homMk g)
        rw [this]
        exact comp _ _ (whiskerRight _ _ (hf ⟦f⟧)) (whiskerLeft _ _ (hg ⟦g⟧))

/-- Every morphism in the braid groupoid is an isomorphism. -/
theorem isIso_quot {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ Y) : IsIso f := by
    refine Hom.inductionOn (α := α) (t := f)
        (id := fun X => by simpa using (inferInstance : IsIso (𝟙 X)))
        (α_hom := fun X Y Z => by
            simpa using (inferInstance : IsIso (α_ X Y Z).hom))
        (α_inv := fun X Y Z => by
            simpa using (inferInstance : IsIso (α_ X Y Z).inv))
        (l_hom := fun X => by
            simpa using (inferInstance : IsIso (λ_ X).hom))
        (l_inv := fun X => by
            simpa using (inferInstance : IsIso (λ_ X).inv))
        (ρ_hom := fun X => by
            simpa using (inferInstance : IsIso (ρ_ X).hom))
        (ρ_inv := fun X => by
            simpa using (inferInstance : IsIso (ρ_ X).inv))
        (σ_hom := fun X Y => by
            simpa [mk_σ] using (inferInstance : IsIso (β_ X Y).hom))
        (σ_inv := fun X Y => by
            simpa [mk_σ_inv] using (inferInstance : IsIso (β_ X Y).inv))
        (comp := fun f g hf hg ↦ by
            simpa using (inferInstance : IsIso (f ≫ g)))
        (whiskerLeft := fun X f hf => by
            simpa using (inferInstance : IsIso (X ◁ f)))
        (whiskerRight := fun f Z hf ↦ by
            simpa using (inferInstance : IsIso (f ▷ Z)))

/-- The braid groupoid instance on `MonoidalWord`. -/
noncomputable instance (α : Type u) : Groupoid (MonoidalWord α) :=
    Groupoid.ofIsIso (C := MonoidalWord α) (fun f => isIso_quot (α := α) f)

/-- A shorthand class for braided monoidal groupoids. -/
class BraidedGroupoid (C : Type u) [Category C] [MonoidalCategory C]
    [BraidedCategory C] [Groupoid C]

/-- The free braided monoidal groupoid on a type of labels. -/
instance (α : Type u) : BraidedGroupoid (MonoidalWord α) where

end BraidGroupoid
