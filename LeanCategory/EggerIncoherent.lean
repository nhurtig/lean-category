import Mathlib
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

end InvolutiveCategory

open InvolutiveCategory

class InvolutiveCategory (C : Type u)
    [Category.{v} C] [MonoidalCategory C] extends InvolutiveCategoryStruct C where
  starHom_id : ∀ X : C, (𝟙 X)⋆ = 𝟙 X⋆ := by cat_disch
  starHom_comp_starHom : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      (f ≫ g)⋆ = f⋆ ≫ g⋆ := by cat_disch
  skewator_naturality : ∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      (f⋆ ⊗ₘ g⋆) ≫ (χ_ Y₁ Y₂).hom = (χ_ X₁ X₂).hom ≫ (g ⊗ₘ f)⋆ := by cat_disch
  involutor_naturality : ∀ {X Y : C} (f : X ⟶ Y),
      f⋆⋆ ≫ (e_ Y).hom = (e_ X).hom ≫ f
  f3 : ∀ P Q R : C,
      (α_ P⋆ Q⋆ R⋆).hom ≫ (P⋆ ◁ (χ_ Q R).hom) ≫ (χ_ P (R ⊗ Q)).hom ≫ (α_ R Q P).hom⋆ =
        ((χ_ P Q).hom ▷ R⋆) ≫ (χ_ (Q ⊗ P) R).hom := by cat_disch
  n2 : ∀ P Q : C,
      (χ_ P⋆ Q⋆).hom ≫ (χ_ Q P).hom⋆ ≫ (e_ (P ⊗ Q)).hom =
        (e_ P).hom ⊗ₘ (e_ Q).hom := by cat_disch
  a : ∀ R : C,
      (e_ R).hom⋆ = (e_ R⋆).hom := by cat_disch

attribute [reassoc (attr := simp), simp] InvolutiveCategory.starHom_id
attribute [reassoc (attr := simp), simp] InvolutiveCategory.starHom_comp_starHom
attribute [reassoc] InvolutiveCategory.skewator_naturality
attribute [reassoc] InvolutiveCategory.involutor_naturality
attribute [reassoc (attr := simp), simp] InvolutiveCategory.f3
attribute [reassoc (attr := simp), simp] InvolutiveCategory.n2
attribute [reassoc (attr := simp), simp] InvolutiveCategory.a

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
def starIso {X Y : C} (f : X ≅ Y) : X⋆≅ Y⋆ where
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

@[reassoc (attr := simp), simp]
theorem involutor_conjugation {X X' : C} (f : X ⟶ X') :
    f⋆⋆ = (e_ _).hom ≫ f ≫ (e_ _).inv := by
  rw [involutor_inv_naturality, Iso.hom_inv_id_assoc]

def star_tensorObj : (𝟙_ C)⋆ ≅ 𝟙_ C :=
  (ρ_ _).symm ≪≫ whiskerLeftIso _ (e_ _).symm ≪≫ χ_ _ _ ≪≫ starIso (ρ_ _) ≪≫ e_ _

@[reassoc (attr := simp), simp]
theorem f3_inv : ∀ P Q R : C,
    (α_ R Q P).inv⋆ ≫ (χ_ P (R ⊗ Q)).inv ≫ (P⋆ ◁ (χ_ Q R).inv) ≫ (α_ P⋆ Q⋆ R⋆).inv =
      (χ_ (Q ⊗ P) R).inv ≫ ((χ_ P Q).inv ▷ R⋆) := by
  intros P Q R
  exact eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp), simp]
theorem n2_inv : ∀ P Q : C,
      (e_ (P ⊗ Q)).inv ≫ (χ_ Q P).inv⋆ ≫ (χ_ P⋆ Q⋆).inv =
        (e_ P).inv ⊗ₘ (e_ Q).inv := by
  intros P Q
  exact eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp), simp]
theorem a_inv : ∀ R : C,
    (e_ R).inv⋆ = (e_ R⋆).inv := by
  intros R
  exact eq_of_inv_eq_inv (by simp)

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

-- TODO show braid has hexagon identity (follows from tℓ)
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

end TwistedCategory
end CategoryTheory

