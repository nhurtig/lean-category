import Mathlib
import LeanCategory.Basic
import LeanCategory.FreeInvolutive.Base

namespace CategoryTheory.FreeInvolutiveCategory

/--
The relation that we quotient premorphisms by to get the actual morphisms
in the free involutive category. Because of coherence, every morphism
is commutative with every other morphism.
-/
def HomEquiv : ∀ {X Y : FreeInvolutiveCategory C}, (X ⟶i Y) → (X ⟶i Y) → Prop := fun _ _ ↦ True

instance setoidHom (X Y : FreeInvolutiveCategory C) : Setoid (X ⟶i Y) :=
  ⟨HomEquiv, ⟨fun _ ↦ True.intro, fun _ ↦ True.intro, fun _ _ ↦ True.intro⟩⟩

/--
Any two morphisms, after quotienting, with the same source and target are equal.
-/
@[simp, aesop safe]
lemma coherence {X Y : FreeInvolutiveCategory C} {f g : _root_.Quotient (setoidHom X Y)} :
    f = g := by
      rcases f with ⟨f⟩
      rcases g with ⟨g⟩
      exact _root_.Quotient.sound True.intro

instance : Category (FreeInvolutiveCategory C) where
  Hom := fun X Y ↦ _root_.Quotient (setoidHom X Y)
  id X := ⟦Hom.id X⟧
  comp := Quotient.map₂ Hom.comp <| by intros; trivial

instance : MonoidalCategory (FreeInvolutiveCategory C) where
  tensorUnit := FreeInvolutiveCategory.unit
  tensorObj := FreeInvolutiveCategory.tensor
  whiskerLeft X := Quotient.map (Hom.whiskerLeft X) <| by intros; trivial
  whiskerRight f Y := Quotient.map (Hom.whiskerRight · Y) (by intros; trivial) f
  tensorHom := Quotient.map₂ Hom.tensor <| by intros; trivial
  associator := fun X Y Z ↦ {
    hom := ⟦Hom.α_hom X Y Z⟧
    inv := ⟦Hom.α_inv X Y Z⟧
    hom_inv_id := coherence
    inv_hom_id := coherence
  }
  leftUnitor := fun X ↦ {
    hom := ⟦Hom.l_hom X⟧
    inv := ⟦Hom.l_inv X⟧
    hom_inv_id := coherence
    inv_hom_id := coherence
  }
  rightUnitor := fun X ↦ {
    hom := ⟦Hom.ρ_hom X⟧
    inv := ⟦Hom.ρ_inv X⟧
    hom_inv_id := coherence
    inv_hom_id := coherence
  }
  whiskerLeft_id := by intros; exact coherence
  id_whiskerRight := by intros; exact coherence
  tensorHom_def := by intros; exact coherence
  id_tensorHom_id := by intros; exact coherence
  tensorHom_comp_tensorHom := by intros; exact coherence
  associator_naturality := by intros; exact coherence
  leftUnitor_naturality := by intros; exact coherence
  rightUnitor_naturality := by intros; exact coherence
  pentagon := by intros; exact coherence
  triangle := by intros; exact coherence

instance : InvolutiveCategory (FreeInvolutiveCategory C) where
  starObj := FreeInvolutiveCategory.star
  starHom := Quotient.map Hom.star (by intros; trivial)
  skewator := fun X Y ↦ {
    hom := ⟦Hom.χ_hom X Y⟧
    inv := ⟦Hom.χ_inv X Y⟧
    hom_inv_id := coherence
    inv_hom_id := coherence
  }
  involutor := fun X ↦ {
    hom := ⟦Hom.ε_hom X⟧
    inv := ⟦Hom.ε_inv X⟧
    hom_inv_id := coherence
    inv_hom_id := coherence
  }
  starHom_id := by intros; exact coherence
  starHom_comp_starHom := by intros; exact coherence
  skewator_naturality := by intros; exact coherence
  involutor_naturality := by intros; exact coherence
  coherence := by intros; exact coherence

section

variable {C : Type u} {D : Type u'} (m : C → D)

open MonoidalCategory InvolutiveCategory

@[simp] lemma map_tensorUnit : map m (𝟙_ _) = 𝟙_ _ := rfl
@[simp] lemma map_tensorObj (X Y : I C) : map m (X ⊗ Y) = map m X ⊗ map m Y := rfl
@[simp] lemma map_starObj (X : I C) : map m X⋆ = (map m X)⋆ := rfl

variable [Category.{v'} D] [MonoidalCategory D] [InvolutiveCategory D]

@[simp] lemma projectObj_tensorUnit : projectObj m (𝟙_ _)= 𝟙_ _ := rfl
@[simp] lemma projectObj_tensorObj (X Y : I C) :
    projectObj m (X ⊗ Y) = projectObj m X ⊗ projectObj m Y := rfl
@[simp] lemma projectObj_starObj (X : I C) : projectObj m X⋆ = (projectObj m X)⋆ := rfl

end

instance : Groupoid (FreeInvolutiveCategory C) where
  inv := Quotient.map Hom.inv (by intros; trivial)
  inv_comp := by intros; exact coherence
  comp_inv := by intros; exact coherence

end CategoryTheory.FreeInvolutiveCategory

