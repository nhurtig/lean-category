import Mathlib

open CategoryTheory

-- class StarMonoid (R : Type u) [Monoid R] extends InvolutiveStar R where
--   /-- `star` skew-distributes over multiplication. -/
--   star_mul : ∀ r s : R, star (r * s) = star s * star r

namespace MonoidalCategory

scoped infixr:70 " ⊗ " => MonoidalCategoryStruct.tensorHom

end MonoidalCategory

open Category MonoidalCategory

namespace CategoryTheory

class InvolutiveCategoryStruct (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
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
    [Category.{v} C] [MonoidalCategory.{v} C] extends InvolutiveCategoryStruct C where
  -- starObj on monoidal identity 𝟙_?
  starHom_id : ∀ X : C, (𝟙 X)⋆ = 𝟙 X⋆ := by cat_disch
  starHom_comp_starHom : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    f⋆ ≫ g⋆ = (f ≫ g)⋆ := by cat_disch
  skewator_naturality : ∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      (f⋆ ⊗ g⋆) ≫ (χ_ Y₁ Y₂).hom = (χ_ X₁ X₂).hom ≫ (g ⊗ f)⋆ := by cat_disch
  involutor_naturality : ∀ {X Y : C} (f : X ⟶ Y),
      f⋆⋆ ≫ (e_ Y).hom = (e_ X).hom ≫ f
  f3 : ∀ P Q R : C,
      (α_ P⋆ Q⋆ R⋆).hom ≫ ((𝟙 P⋆) ⊗ (χ_ Q R).hom) ≫ (χ_ P (R ⊗ Q)).hom ≫ (α_ R Q P).hom⋆ =
        ((χ_ P Q).hom ⊗ (𝟙 R⋆)) ≫ (χ_ (Q ⊗ P) R).hom := by cat_disch
  n2 : ∀ P Q : C,
      (χ_ P⋆ Q⋆).hom ≫ (χ_ Q P).hom⋆ ≫ (e_ (P ⊗ Q)).hom =
        (e_ P).hom ⊗ (e_ Q).hom := by cat_disch
  a : ∀ R : C,
      (e_ R).hom⋆ = (e_ R⋆).hom := by cat_disch

class TwistedCategoryStruct (C : Type u)
    [Category.{v} C] [MonoidalCategory.{v} C] [InvolutiveCategory C] where
  twist : ∀ X : C, X⋆ ≅ X

namespace TwistedCategory

scoped notation "ς_" => TwistedCategoryStruct.twist

end TwistedCategory

open TwistedCategory

class TwistedCategory (C : Type u) [Category.{v} C]
    [MonoidalCategory.{v} C] [InvolutiveCategory C] extends TwistedCategoryStruct C where
  twist_naturality : ∀ {X Y : C} (f : X ⟶ Y),
      f⋆ ≫ (ς_ Y).hom = (ς_ X).hom ≫ f := by cat_disch
  tℓ : ∀ P Q R : C,
      (((χ_ P⋆ Q⋆).hom ≫ (ς_ (Q⋆ ⊗ P⋆)).hom) ⊗ (𝟙 R⋆⋆)) ≫ (α_ Q⋆ P⋆ R⋆⋆).hom ≫
       ((𝟙 Q⋆) ⊗ ((χ_ P R⋆).hom ≫ (ς_ (R⋆ ⊗ P)).hom)) ≫ (α_ Q⋆ R⋆ P).inv ≫
       (((χ_ Q R).hom ≫ (ς_ (R ⊗ Q)).hom) ⊗ (𝟙 P)) ≫ (α_ R Q P).hom =
      (((ς_ P⋆).hom ⊗ (ς_ Q⋆).hom) ⊗ (ς_ R⋆).hom) ≫ ((χ_ P Q).hom ⊗ (𝟙 R⋆)) ≫
        (χ_ (Q ⊗ P) R).hom ≫ (ς_ (R ⊗ Q ⊗ P)).hom := by cat_disch

end CategoryTheory
