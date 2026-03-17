import Mathlib
import LeanCategory.FreeInvolutive.Base
import LeanCategory.FreeTwisted.Base
import LeanCategory.FreeTwistedQuiver.Base

open CategoryTheory

open Category MonoidalCategory

namespace CategoryTheory

class InvolutiveCategoryStruct (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  starObj : C → C
  starHom : (X ⟶ Y) → (starObj X ⟶ starObj Y)
  skewator : ∀ X Y : C, (starObj X ⊗ starObj Y) ≅ starObj (Y ⊗ X)
  involutor : ∀ X : C, starObj (starObj X) ≅ X

namespace InvolutiveCategory

scoped postfix:max "⋆" => InvolutiveCategoryStruct.starObj
scoped postfix:max "⋆" => InvolutiveCategoryStruct.starHom
scoped notation "χ_" => InvolutiveCategoryStruct.skewator
scoped notation "e_" => InvolutiveCategoryStruct.involutor

variable {C : Type u} [𝒞 : Category.{v} C] [MonoidalCategory C] [InvolutiveCategoryStruct C]

-- involutive coherences are isomorphisms made up of the
-- skewator/involutor, and monoidal associator/unitors.
-- We define these here so we can "cheat" in the involutive
-- category definition by stating coherence instead of proving
-- it from a couple of diagrams. If involutive categories are indeed
-- coherent (as many have proved by hand), this is equivalent to
-- the usual definition
inductive InvolutiveCoherence : {X Y : C} → (X ⟶ Y) → Prop where
  | id : InvolutiveCoherence (𝟙 X)
  | comp : InvolutiveCoherence f → InvolutiveCoherence g → InvolutiveCoherence (f ≫ g)
  | tensor : InvolutiveCoherence f → InvolutiveCoherence g → InvolutiveCoherence (f ⊗ₘ g)
  | whiskerLeft : InvolutiveCoherence f → InvolutiveCoherence (X ◁ f)
  | whiskerRight : InvolutiveCoherence f → InvolutiveCoherence (f ▷ Y)
  | starHom : InvolutiveCoherence f → InvolutiveCoherence f⋆
  | associator_hom : ∀ X Y Z : C, InvolutiveCoherence (α_ X Y Z).hom
  | associator_inv : ∀ X Y Z : C, InvolutiveCoherence (α_ X Y Z).inv
  | leftUnitor_hom : ∀ X : C, InvolutiveCoherence (λ_ X).hom
  | leftUnitor_inv : ∀ X : C, InvolutiveCoherence (λ_ X).inv
  | rightUnitor_hom : ∀ X : C, InvolutiveCoherence (ρ_ X).hom
  | rightUnitor_inv : ∀ X : C, InvolutiveCoherence (ρ_ X).inv
  | skewator_hom : ∀ X Y : C, InvolutiveCoherence (χ_ X Y).hom
  | skewator_inv : ∀ X Y : C, InvolutiveCoherence (χ_ X Y).inv
  | involutor_hom : ∀ X : C, InvolutiveCoherence (e_ X).hom
  | involutor_inv : ∀ X : C, InvolutiveCoherence (e_ X).inv

end InvolutiveCategory

open InvolutiveCategory

class InvolutiveCategory (C : Type u)
    [Category.{v} C] [MonoidalCategory C] extends InvolutiveCategoryStruct C where
  -- starObj on monoidal identity 𝟙_?
  starHom_id : ∀ X : C, (𝟙 X)⋆ = 𝟙 X⋆ := by cat_disch
  starHom_comp_starHom : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      (f ≫ g)⋆ = f⋆ ≫ g⋆ := by cat_disch
  skewator_naturality : ∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      (f⋆ ⊗ₘ g⋆) ≫ (χ_ Y₁ Y₂).hom = (χ_ X₁ X₂).hom ≫ (g ⊗ₘ f)⋆ := by cat_disch
  involutor_naturality : ∀ {X Y : C} (f : X ⟶ Y),
      f⋆⋆ ≫ (e_ Y).hom = (e_ X).hom ≫ f
  coherence : ∀ {X Y : C} (f g : X ⟶ Y),
      InvolutiveCoherence f → InvolutiveCoherence g → f = g := by cat_disch

attribute [reassoc (attr := simp), simp] InvolutiveCategory.starHom_id
attribute [reassoc (attr := simp), simp] InvolutiveCategory.starHom_comp_starHom
attribute [reassoc] InvolutiveCategory.skewator_naturality
attribute [reassoc] InvolutiveCategory.involutor_naturality

namespace InvolutiveCategory

variable {C : Type u} [𝒞 : Category.{v} C] [MonoidalCategory C] [InvolutiveCategory C]

@[reassoc]
theorem skewator_inv_naturality : 
    ∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      (g ⊗ₘ f)⋆ ≫ (χ_ Y₁ Y₂).inv = (χ_ X₁ X₂).inv ≫ (f⋆ ⊗ₘ g⋆) := by
  intros _ _ _ _ f g
  rw [← id_comp (_ ≫ _)]
  rw [← (χ_ _ _).inv_hom_id]
  simp only [Category.assoc]
  rw [← skewator_naturality_assoc f g]
  simp

@[reassoc]
theorem involutor_inv_naturality :
    ∀ {X Y : C} (f : X ⟶ Y),
      f ≫ (e_ Y).inv = (e_ X).inv ≫ f⋆⋆ := by
  intros _ _ f
  rw [← id_comp (_ ≫ _)]
  rw [← (e_ _).inv_hom_id]
  simp only [Category.assoc]
  rw [← involutor_naturality_assoc f]
  simp

@[reassoc (attr := simp)]
theorem hom_inv_star {X Y : C} (f : X ≅ Y) :
    f.hom⋆ ≫ f.inv⋆ = 𝟙 X⋆ := by
  rw [← starHom_comp_starHom]
  simp

@[reassoc (attr := simp)]
theorem hom_inv_star' {X Y : C} (f : X ⟶ Y) [IsIso f] :
    f⋆ ≫ (inv f)⋆ = 𝟙 X⋆ := by
  rw [← starHom_comp_starHom]
  simp

@[reassoc (attr := simp)]
theorem inv_hom_star {X Y : C} (f : X ≅ Y) :
    f.inv⋆ ≫ f.hom⋆ = 𝟙 Y⋆ := by
  rw [← starHom_comp_starHom]
  simp

@[reassoc (attr := simp)]
theorem inv_hom_star' {X Y : C} (f : X ⟶ Y) [IsIso f] :
    (inv f)⋆ ≫ f⋆ = 𝟙 Y⋆ := by
  rw [← starHom_comp_starHom]
  simp

@[simps!]
def starIso {X Y : C} (f : X ≅ Y) : X⋆ ≅ Y⋆ where
  hom := f.hom⋆
  inv := f.inv⋆

instance star_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso f⋆ :=
  (starIso (asIso f)).isIso_hom

@[simp]
theorem inv_star {X Y : C} (f : X ⟶ Y) [hf : IsIso f] :
    inv f⋆ = (inv f)⋆ := by
  rw [← id_comp (inv f⋆)]
  rw [← starHom_id]
  rw [← hf.inv_hom_id]
  cat_disch

@[reassoc (attr := simp), simp]
theorem starHom_tensorHom {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g)⋆ = (χ_ _ _).inv ≫ (g⋆ ⊗ₘ f⋆) ≫ (χ_ _ _).hom := by
  rw [skewator_naturality, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp), simp]
theorem starHom_whiskerLeft {X X' Y : C} (f : X ⟶ X') :
    (Y ◁ f)⋆ = (χ_ _ _).inv ≫ (f⋆ ▷ Y⋆) ≫ (χ_ _ _).hom := by
  rw [← id_tensorHom, starHom_tensorHom]
  simp

@[reassoc (attr := simp), simp]
theorem starHom_whiskerRight {X X' Y : C} (f : X ⟶ X') :
    (f ▷ Y)⋆ = (χ_ _ _).inv ≫ ((InvolutiveCategoryStruct.starObj Y) ◁ f⋆) ≫ (χ_ _ _).hom := by
  rw [← tensorHom_id, starHom_tensorHom]
  simp

theorem whiskerRight_star {W X Y Z : C} (f : W ⟶ Z) :
    f ▷ (X ⊗ Y)⋆ = _ ◁ (χ_ _ _).inv ≫ f ▷ (Y⋆ ⊗ X⋆) ≫ _ ◁ (χ_ _ _).hom := by
  rw [← whisker_exchange]
  simp

theorem whiskerLeft_star {W X Y Z : C} (f : W ⟶ Z) :
    (X ⊗ Y)⋆ ◁ f = (χ_ _ _).inv ▷ _ ≫ _ ◁ f ≫ (χ_ _ _).hom ▷ _ := by
  rw [whisker_exchange]
  simp

@[reassoc (attr := simp), simp]
theorem involutor_conjugation {X X' : C} (f : X ⟶ X') :
    f⋆⋆ = (e_ _).hom ≫ f ≫ (e_ _).inv := by
  rw [involutor_inv_naturality, Iso.hom_inv_id_assoc]

def star_tensorObj : (𝟙_ C)⋆ ≅ 𝟙_ C :=
  (ρ_ _).symm ≪≫ whiskerLeftIso _ (e_ _).symm ≪≫ χ_ _ _ ≪≫ starIso (ρ_ _) ≪≫ e_ _

@[reassoc (attr := simp), simp]
theorem star_involutor_hom (X : C) : (e_ X).hom⋆ = (e_ X⋆).hom := by
  apply coherence <;> repeat' constructor

@[reassoc (attr := simp), simp]
theorem star_involutor_inv (X : C) : (e_ X).inv⋆ = (e_ X⋆).inv := by
  apply coherence <;> repeat' constructor

@[reassoc (attr := simp), simp]
theorem star_involutor (X : C) : starIso (e_ X) = (e_ X⋆) := by
  ext
  exact star_involutor_hom X

end InvolutiveCategory

namespace TwistedCategory

class TwistedCategoryStruct (C : Type u)
    [Category.{v} C] [MonoidalCategory C] [InvolutiveCategory C] where
  twist : ∀ X : C, InvolutiveCategoryStruct.starObj X ≅ X

scoped notation "ς_" => TwistedCategoryStruct.twist

variable {C : Type u}
    [𝒞 : Category.{v} C] [MonoidalCategory C] [InvolutiveCategory C] [TwistedCategoryStruct C]

def braid (X Y : C) : X ⊗ Y ≅ Y ⊗ X where
  hom := ((ς_ _).inv ⊗ₘ (ς_ _).inv) ≫
    (χ_ _ _).hom ≫
    (ς_ _).hom
  inv := (ς_ _).inv ≫
    (χ_ _ _).inv ≫
    ((ς_ _).hom ⊗ₘ (ς_ _).hom)

-- could show braid agrees with hexagon identity (it follows from tℓ)
scoped notation "σ_" => braid

end TwistedCategory

open TwistedCategory

class TwistedCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] [InvolutiveCategory C]
    extends TwistedCategoryStruct C where
  twist_naturality : ∀ {X Y : C} (f : X ⟶ Y),
      f⋆ ≫ (ς_ Y).hom = (ς_ X).hom ≫ f := by cat_disch
  tℓ : ∀ P Q R : C,
      (χ_ P⋆ Q⋆).hom ▷ R⋆⋆ ≫ (ς_ (Q⋆ ⊗ P⋆)).hom ▷ R⋆⋆ ≫ (α_ Q⋆ P⋆ R⋆⋆).hom ≫
       Q⋆ ◁ (χ_ P R⋆).hom ≫ Q⋆ ◁ (ς_ (R⋆ ⊗ P)).hom ≫ (α_ Q⋆ R⋆ P).inv ≫
       (χ_ Q R).hom ▷ P ≫ (ς_ (R ⊗ Q)).hom ▷ P ≫ (α_ R Q P).hom =
      (((ς_ P⋆).hom ⊗ₘ (ς_ Q⋆).hom) ⊗ₘ (ς_ R⋆).hom) ≫ ((χ_ P Q).hom ▷ R⋆) ≫
        (χ_ (Q ⊗ P) R).hom ≫ (ς_ (R ⊗ Q ⊗ P)).hom := by cat_disch

attribute [reassoc] TwistedCategory.twist_naturality
attribute [reassoc (attr := simp), simp] TwistedCategory.tℓ

namespace TwistedCategory

variable {C : Type u}
    [𝒞 : Category.{v} C] [MonoidalCategory C] [InvolutiveCategory C] [TwistedCategory C]

@[reassoc]
theorem twist_inv_naturality :
    ∀ {X Y : C} (f : X ⟶ Y),
      f ≫ (ς_ Y).inv = (ς_ X).inv ≫ f⋆ := by
  intros _ _ f
  rw [← id_comp (_ ≫ _)]
  rw [← (ς_ _).inv_hom_id]
  simp only [Category.assoc]
  rw [← twist_naturality_assoc f]
  simp

@[reassoc]
theorem braid_naturality :
    ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      (f ⊗ₘ g) ≫ (σ_ Y₁ Y₂).hom = (σ_ X₁ X₂).hom ≫ (g ⊗ₘ f) := by
  intros _ _ _ _ f g
  unfold braid; simp only
  rw [tensorHom_comp_tensorHom_assoc]
  repeat1 rw [twist_inv_naturality]
  rw [← tensorHom_comp_tensorHom_assoc]
  rw [skewator_naturality_assoc]
  rw [twist_naturality]
  simp

@[reassoc]
theorem braid_inv_naturality :
    ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      (f ⊗ₘ g) ≫ (σ_ Y₂ Y₁).inv = (σ_ X₂ X₁).inv ≫ (g ⊗ₘ f) := by
  intros _ _ _ _ f g
  unfold braid; simp only
  rw [twist_inv_naturality_assoc]
  rw [skewator_inv_naturality_assoc]
  rw [tensorHom_comp_tensorHom]
  simp [twist_naturality]

@[reassoc (attr := simp), simp]
theorem tℓ_inv : ∀ P Q R : C,
    (α_ R Q P).inv ≫  
      (ς_ (R ⊗ Q)).inv ▷ P ≫ (χ_ Q R).inv ▷ P ≫ (α_ Q⋆ R⋆ P).hom ≫ 
      Q⋆ ◁ (ς_ (R⋆ ⊗ P)).inv ≫ Q⋆ ◁ (χ_ P R⋆).inv ≫ (α_ Q⋆ P⋆ R⋆⋆).inv ≫ 
      (ς_ (Q⋆ ⊗ P⋆)).inv ▷ R⋆⋆ ≫ (χ_ P⋆ Q⋆).inv ▷ R⋆⋆ =
    (ς_ (R ⊗ Q ⊗ P)).inv ≫ (χ_ (Q ⊗ P) R).inv ≫ (χ_ P Q).inv ▷ R⋆ ≫
      (((ς_ P⋆).inv ⊗ₘ (ς_ Q⋆).inv) ⊗ₘ (ς_ R⋆).inv) := by
  intros P Q R
  exact eq_of_inv_eq_inv (by simp)

theorem twist_triple {P Q R : C} : (ς_ (R ⊗ Q ⊗ P)).hom =
    (χ_ (Q ⊗ P) R).inv ≫
      (χ_ P Q).inv ▷ R⋆ ≫
        (((ς_ P⋆).inv ⊗ₘ (ς_ Q⋆).inv) ⊗ₘ (ς_ R⋆).inv) ≫ 
          (χ_ P⋆ Q⋆).hom ▷ R⋆⋆ ≫ (ς_ (Q⋆ ⊗ P⋆)).hom ▷ R⋆⋆ ≫ (α_ Q⋆ P⋆ R⋆⋆).hom ≫
                 Q⋆ ◁ (χ_ P R⋆).hom ≫ Q⋆ ◁ (ς_ (R⋆ ⊗ P)).hom ≫ (α_ Q⋆ R⋆ P).inv ≫
                 (χ_ Q R).hom ▷ P ≫ (ς_ (R ⊗ Q)).hom ▷ P ≫ (α_ R Q P).hom := by
  simp

theorem twist_triple_inv {P Q R : C} : (ς_ (R ⊗ Q ⊗ P)).inv =
    (α_ R Q P).inv ≫ (ς_ (R ⊗ Q)).inv ▷ P ≫ (χ_ Q R).inv ▷ P ≫ (α_ Q⋆ R⋆ P).hom ≫
       Q⋆ ◁ (ς_ (R⋆ ⊗ P)).inv ≫ Q⋆ ◁ (χ_ P R⋆).inv ≫ (α_ Q⋆ P⋆ R⋆⋆).inv ≫
       (ς_ (Q⋆ ⊗ P⋆)).inv ▷ R⋆⋆ ≫ (χ_ P⋆ Q⋆).inv ▷ R⋆⋆ ≫
       (((ς_ P⋆).hom ⊗ₘ (ς_ Q⋆).hom) ⊗ₘ (ς_ R⋆).hom) ≫ ((χ_ P Q).hom ▷ R⋆) ≫
        (χ_ (Q ⊗ P) R).hom := by
  simp

@[simp, reassoc (attr := simp)]
theorem twist_star_hom : ∀ X : C, (ς_ X).hom⋆ = (ς_ X⋆).hom := by
  intro X
  have := twist_naturality (ς_ X).hom
  simp at this ⊢
  exact this

@[simp, reassoc (attr := simp)]
theorem twist_star_inv : ∀ X : C, (ς_ X).inv⋆ = (ς_ X⋆).inv := by
  intro X
  have := twist_inv_naturality (ς_ X).inv
  simp at this ⊢
  exact this.symm

@[simp, reassoc (attr := simp)]
theorem twist_star : ∀ X : C, starIso (ς_ X) = (ς_ X⋆) := by
  intro X
  ext
  exact twist_star_hom X

@[simp, reassoc (attr := simp)]
theorem star_braid_hom : ∀ X Y : C,
    (σ_ X Y).hom⋆ = (χ_ Y X).inv ≫ (σ_ Y⋆ X⋆).hom ≫ (χ_ X Y).hom := by
  intro X Y
  unfold braid
  simp
  rw [twist_naturality]

@[simp, reassoc (attr := simp)]
theorem star_braid_inv : ∀ X Y : C,
    (σ_ X Y).inv⋆ = (χ_ X Y).inv ≫ (σ_ Y⋆ X⋆).inv ≫ (χ_ Y X).hom := by
  intro X Y
  unfold braid
  simp
  rw [twist_inv_naturality_assoc]

@[simp, reassoc (attr := simp)]
theorem star_braid : ∀ X Y : C, starIso (σ_ X Y) = (χ_ Y X).symm ≪≫ (σ_ Y⋆ X⋆) ≪≫ (χ_ X Y) := by
  intro X Y
  ext
  unfold braid
  simp
  rw [twist_naturality]

end TwistedCategory

variable {C : Type u} {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [InvolutiveCategory D]
namespace FreeInvolutiveCategory

def projectObj (m : C → D) : I C → D
  | of c => m c
  | unit => 𝟙_ _
  | tensor X Y => X.projectObj m ⊗ Y.projectObj m
  | star X => (X.projectObj m)⋆

@[simp] lemma projectObj_of (m : C → D) (c : C) : projectObj m (of c) = m c := rfl
@[simp] lemma projectObj_unit (m : C → D) : projectObj m unit = 𝟙_ D := rfl
@[simp] lemma projectObj_tensor (m : C → D) (X Y : I C) :
    projectObj m (tensor X Y) = projectObj m X ⊗ projectObj m Y := rfl
@[simp] lemma projectObj_star (m : C → D) (X : I C) :
    projectObj m (star X) = (projectObj m X)⋆ := rfl

end FreeInvolutiveCategory

namespace FreeTwistedCategory

def projectObj (m : C → D) (X : T C) : D := X.as.projectObj m

@[simp] lemma projectObj_of (m : C → D) : projectObj m (of c) = m c := rfl
@[simp] lemma projectObj_unit (m : C → D) : projectObj m (unit : T C) = 𝟙_ D := rfl
@[simp] lemma projectObj_tensor (m : C → D) (X Y : T C) :
    projectObj m (tensor X Y) = projectObj m X ⊗ projectObj m Y := rfl
@[simp] lemma projectObj_star (m : C → D) (X : T C) :
    projectObj m (star X) = (projectObj m X)⋆ := rfl
@[simp] lemma projectObj_as (m : C → D) (X : T C) : X.as.projectObj m = projectObj m X := rfl

end FreeTwistedCategory

namespace FreeTwistedCategoryQuiver

def projectObj (m : C → D) (X : TQ C) : D := X.as.projectObj m

@[simp] lemma projectObj_of (m : C → D) : projectObj m (of c) = m c := rfl
@[simp] lemma projectObj_unit (m : C → D) : projectObj m (unit : TQ C) = 𝟙_ D := rfl
@[simp] lemma projectObj_tensor (m : C → D) (X Y : TQ C) :
    projectObj m (tensor X Y) = projectObj m X ⊗ projectObj m Y := rfl
@[simp] lemma projectObj_star (m : C → D) (X : TQ C) :
    projectObj m (star X) = (projectObj m X)⋆ := rfl
@[simp] lemma projectObj_as (m : C → D) (X : TQ C) : X.as.projectObj m = projectObj m X := rfl

end FreeTwistedCategoryQuiver

end CategoryTheory

