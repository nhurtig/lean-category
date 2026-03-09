import Mathlib

open CategoryTheory

-- class StarMonoid (R : Type u) [Monoid R] extends InvolutiveStar R where
--   /-- `star` skew-distributes over multiplication. -/
--   star_mul : ∀ r s : R, star (r * s) = star s * star r

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

#check InvolutiveCategoryStruct.involutor

#check MonoidalCategoryStruct.tensorHom
#check MonoidalCategory.tensorHom

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
  f3 : ∀ P Q R : C,
      (α_ P⋆ Q⋆ R⋆).hom ≫ ((𝟙 P⋆) ⊗ₘ (χ_ Q R).hom) ≫ (χ_ P (R ⊗ Q)).hom ≫ (α_ R Q P).hom⋆ =
        ((χ_ P Q).hom ⊗ₘ (𝟙 R⋆)) ≫ (χ_ (Q ⊗ P) R).hom := by cat_disch
  n2 : ∀ P Q : C,
      (χ_ P⋆ Q⋆).hom ≫ (χ_ Q P).hom⋆ ≫ (e_ (P ⊗ Q)).hom =
        (e_ P).hom ⊗ₘ (e_ Q).hom := by cat_disch
  a : ∀ R : C,
      (e_ R).hom⋆ = (e_ R⋆).hom := by cat_disch

/- attribute  MonoidalCategory.tensorHom_def -/
/- attribute [reassoc, simp] MonoidalCategory.whiskerLeft_id -/
/- attribute [reassoc, simp] MonoidalCategory.id_whiskerRight -/
/- attribute [reassoc (attr := simp),] MonoidalCategory.tensorHom_comp_tensorHom -/
/- attribute [reassoc] MonoidalCategory.associator_naturality -/
/- attribute [reassoc] MonoidalCategory.leftUnitor_naturality -/
/- attribute [reassoc] MonoidalCategory.rightUnitor_naturality -/
/- attribute [reassoc (attr := simp)] MonoidalCategory.pentagon -/
/- attribute [reassoc (attr := simp)] MonoidalCategory.triangle -/

attribute [reassoc (attr := simp), simp] InvolutiveCategory.starHom_id
attribute [reassoc (attr := simp), simp] InvolutiveCategory.starHom_comp_starHom
attribute [reassoc (attr := simp), simp] InvolutiveCategory.skewator_naturality
attribute [reassoc (attr := simp), simp] InvolutiveCategory.involutor_naturality
attribute [reassoc (attr := simp), simp] InvolutiveCategory.f3
attribute [reassoc (attr := simp), simp] InvolutiveCategory.n2
attribute [reassoc (attr := simp), simp] InvolutiveCategory.a


#check MonoidalCategory


-- TODO from last night, 3/8: fill in the remaining naturality lemmas for the twist and the involutor.
-- use "eq_of_inv_eq_inv" for the non-naturality diagrams, like they did for
-- pentagon:
/-
@[reassoc (attr := simp)]
theorem pentagon_inv :
    W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
  eq_of_inv_eq_inv (by simp)
-/
#check MonoidalCategory.pentagon
namespace InvolutiveCategory

variable {C : Type u} [𝒞 : Category.{v} C] [MonoidalCategory C] [InvolutiveCategory C]

@[reassoc (attr := simp), simp]
theorem skewator_inv_naturality :
    ∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      (g ⊗ₘ f)⋆ ≫ (χ_ Y₁ Y₂).inv = (χ_ X₁ X₂).inv ≫ (f⋆ ⊗ₘ g⋆) := by
  intros _ _ _ _ f g
  rw [← id_comp (_ ≫ _)]
  rw [← (χ_ _ _).inv_hom_id]
  simp only [Category.assoc]
  rw [← skewator_naturality_assoc f g]
  simp

@[reassoc (attr := simp), simp]
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

/-
  f3 : ∀ P Q R : C,
      (α_ P⋆ Q⋆ R⋆).hom ≫ ((𝟙 P⋆) ⊗ₘ (χ_ Q R).hom) ≫ (χ_ P (R ⊗ Q)).hom ≫ (α_ R Q P).hom⋆ =
        ((χ_ P Q).hom ⊗ₘ (𝟙 R⋆)) ≫ (χ_ (Q ⊗ P) R).hom := by cat_disch
  n2 : ∀ P Q : C,
      (χ_ P⋆ Q⋆).hom ≫ (χ_ Q P).hom⋆ ≫ (e_ (P ⊗ Q)).hom =
        (e_ P).hom ⊗ₘ (e_ Q).hom := by cat_disch
        -/
/- variable {c : C} -/
/- #synth IsIso ((e_ c).inv ⊗ₘ (e_ c).inv) -/
/- #synth InvolutiveCategory C -/
/- #synth MonoidalCategory C -/
/- #check tensor_isIso -/
/- instance tensor_isIso' {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : IsIso (f ⊗ₘ g) := -/
/-   sorry -/
/- #synth IsIso ((e_ c).inv ⊗ₘ (e_ c).inv) -/

-- difficult b/c f3 isn't presented in normal form
@[reassoc (attr := simp), simp]
theorem f3_inv : ∀ P Q R : C,
    (α_ R Q P).inv⋆ ≫ (χ_ P (R ⊗ Q)).inv ≫ ((𝟙 P⋆) ⊗ₘ (χ_ Q R).inv) ≫ (α_ P⋆ Q⋆ R⋆).inv =
      (χ_ (Q ⊗ P) R).inv ≫ ((χ_ P Q).inv ⊗ₘ (𝟙 R⋆)) := by
  intros P Q R
  apply eq_of_inv_eq_inv
  simp only [IsIso.inv_comp]
  simp only [inv_star]
  simp only [inv_tensor]
  simp only [IsIso.Iso.inv_inv]
  simp only [IsIso.inv_id]
  simp only [assoc]
  exact f3 P Q R

@[reassoc (attr := simp), simp]
theorem n2_inv : ∀ P Q : C,
      (e_ (P ⊗ Q)).inv ≫ (χ_ Q P).inv⋆ ≫ (χ_ P⋆ Q⋆).inv =
        (e_ P).inv ⊗ₘ (e_ Q).inv := by
  intros P Q
  apply eq_of_inv_eq_inv
  simp only [IsIso.inv_comp]
  simp only [inv_star]
  simp only [inv_tensor]
  simp only [IsIso.Iso.inv_inv]
  simp only [assoc]
  exact n2 P Q

@[reassoc (attr := simp), simp]
theorem a_inv : ∀ R : C,
    (e_ R).inv⋆ = (e_ R⋆).inv := by
  intros R
  apply eq_of_inv_eq_inv
  simp only [inv_star]
  simp only [IsIso.Iso.inv_inv]
  exact a R

/-
  skewator_naturality : ∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      (f⋆ ⊗ₘ g⋆) ≫ (χ_ Y₁ Y₂).hom = (χ_ X₁ X₂).hom ≫ (g ⊗ₘ f)⋆ := by cat_disch
  involutor_naturality : ∀ {X Y : C} (f : X ⟶ Y),
      f⋆⋆ ≫ (e_ Y).hom = (e_ X).hom ≫ f
      -/

end InvolutiveCategory

namespace TwistedCategory

class TwistedCategoryStruct (C : Type u)
    [Category.{v} C] [MonoidalCategory C] [InvolutiveCategory C] where
  twist : ∀ X : C, InvolutiveCategoryStruct.starObj X ≅ X

#check TwistedCategoryStruct.twist

/- #check InvolutiveCategoryStruct.tensorObj -/
/- #check TwistedCategoryStruct.tensorObj -/
/- #check TwistedCategoryStruct.starHom -/
/- #check MonoidalCategoryStruct.starObj -/
/- #check InvolutiveCategoryStruct.tensorObj -/
/- #check TwistedCategoryStruct.tensorHom -/

scoped notation "ς_" => TwistedCategoryStruct.twist

end TwistedCategory

open TwistedCategory

class TwistedCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] [InvolutiveCategory C]
    extends TwistedCategoryStruct C where
  twist_naturality : ∀ {X Y : C} (f : X ⟶ Y),
      f⋆ ≫ (ς_ Y).hom = (ς_ X).hom ≫ f := by cat_disch
  tℓ : ∀ P Q R : C,
      (((χ_ P⋆ Q⋆).hom ≫ (ς_ (Q⋆ ⊗ P⋆)).hom) ⊗ₘ (𝟙 R⋆⋆)) ≫ (α_ Q⋆ P⋆ R⋆⋆).hom ≫
       ((𝟙 Q⋆) ⊗ₘ ((χ_ P R⋆).hom ≫ (ς_ (R⋆ ⊗ P)).hom)) ≫ (α_ Q⋆ R⋆ P).inv ≫
       (((χ_ Q R).hom ≫ (ς_ (R ⊗ Q)).hom) ⊗ₘ (𝟙 P)) ≫ (α_ R Q P).hom =
      (((ς_ P⋆).hom ⊗ₘ (ς_ Q⋆).hom) ⊗ₘ (ς_ R⋆).hom) ≫ ((χ_ P Q).hom ⊗ₘ (𝟙 R⋆)) ≫
        (χ_ (Q ⊗ P) R).hom ≫ (ς_ (R ⊗ Q ⊗ P)).hom := by cat_disch

attribute [reassoc (attr := simp), simp] TwistedCategory.twist_naturality
attribute [reassoc (attr := simp), simp] TwistedCategory.tℓ

namespace TwistedCategory

variable {C : Type u}
    [𝒞 : Category.{v} C] [MonoidalCategory C] [InvolutiveCategory C] [TwistedCategory C]

@[reassoc (attr := simp), simp]
theorem twist_inv_naturality :
    ∀ {X Y : C} (f : X ⟶ Y),
      f ≫ (ς_ Y).inv = (ς_ X).inv ≫ f⋆ := by
  intros _ _ f
  rw [← id_comp (_ ≫ _)]
  rw [← (ς_ _).inv_hom_id]
  simp only [Category.assoc]
  rw [← twist_naturality_assoc f]
  simp

@[reassoc (attr := simp), simp]
theorem tℓ_inv : ∀ P Q R : C,
    (α_ R Q P).inv ≫  
      (((ς_ (R ⊗ Q)).inv ≫ (χ_ Q R).inv) ⊗ₘ (𝟙 P)) ≫ (α_ Q⋆ R⋆ P).hom ≫ 
      ((𝟙 Q⋆) ⊗ₘ ((ς_ (R⋆ ⊗ P)).inv ≫ (χ_ P R⋆).inv)) ≫ (α_ Q⋆ P⋆ R⋆⋆).inv ≫ 
      (((ς_ (Q⋆ ⊗ P⋆)).inv ≫ (χ_ P⋆ Q⋆).inv) ⊗ₘ (𝟙 R⋆⋆)) =
    (ς_ (R ⊗ Q ⊗ P)).inv ≫ (χ_ (Q ⊗ P) R).inv ≫ ((χ_ P Q).inv ⊗ₘ (𝟙 R⋆)) ≫
      (((ς_ P⋆).inv ⊗ₘ (ς_ Q⋆).inv) ⊗ₘ (ς_ R⋆).inv) := by
  intros P Q R
  apply eq_of_inv_eq_inv
  simp only [IsIso.inv_comp]
  simp only [inv_tensor]
  simp only [IsIso.Iso.inv_inv]
  simp only [IsIso.Iso.inv_hom]
  simp only [IsIso.inv_id]
  simp only [assoc]
  simp only [IsIso.inv_comp]
  simp only [IsIso.Iso.inv_inv]
  exact tℓ P Q R

end TwistedCategory
end CategoryTheory

