import Mathlib

namespace CategoryTheory

section

variable (C : Type u)

-- we will NOT be defining notation for
-- this type, as it conflicts with the later
-- monoidal/involutive category notations
inductive FreeInvolutiveCategory : Type u
  | of : C → FreeInvolutiveCategory
  | unit : FreeInvolutiveCategory
  | tensor : FreeInvolutiveCategory → FreeInvolutiveCategory → FreeInvolutiveCategory
  | star : FreeInvolutiveCategory → FreeInvolutiveCategory
  deriving Inhabited

end

namespace FreeInvolutiveCategory

variable {C : Type u}

scoped notation "I" => FreeInvolutiveCategory

def sizeOf : I C → ℕ
  | of _ => 0
  | unit => 0
  | tensor X Y => X.sizeOf + Y.sizeOf + 1
  | star X => X.sizeOf + 1

inductive Hom : I C → I C → Type u
  | id (X) : Hom X X
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : FreeInvolutiveCategory C) {Y₁ Y₂} (f : Hom Y₁ Y₂) :
      Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : FreeInvolutiveCategory C) :
      Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)
  | α_hom (X Y Z : FreeInvolutiveCategory C) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : FreeInvolutiveCategory C) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : Hom (FreeInvolutiveCategory.unit.tensor X) X
  | l_inv (X) : Hom X (FreeInvolutiveCategory.unit.tensor X)
  | ρ_hom (X : FreeInvolutiveCategory C) : Hom (X.tensor .unit) X
  | ρ_inv (X : FreeInvolutiveCategory C) : Hom X (X.tensor .unit)
  | star {X Y} (f : Hom X Y) : Hom X.star Y.star
  | χ_hom (X Y : FreeInvolutiveCategory C) : Hom (X.star.tensor  Y.star) (Y.tensor X).star
  | χ_inv (X Y : FreeInvolutiveCategory C) : Hom (Y.tensor X).star (X.star.tensor Y.star)
  | ε_hom (X : FreeInvolutiveCategory C) : Hom X.star.star X
  | ε_inv (X : FreeInvolutiveCategory C) : Hom X X.star.star

scoped infixr:10 " ⟶i " => Hom -- i for "involutive"

@[simp]
def Hom.inv {X Y : I C} : (X ⟶i Y) → (Y ⟶i X)
  | id X => id X
  | comp f g => comp (g.inv) (f.inv)
  | whiskerLeft X f => whiskerLeft X (f.inv)
  | whiskerRight f Y => whiskerRight (f.inv) Y
  | tensor f g => tensor (f.inv) (g.inv)
  | α_hom X Y Z => α_inv X Y Z
  | α_inv X Y Z => α_hom X Y Z
  | l_hom X => l_inv X
  | l_inv X => l_hom X
  | ρ_hom X => ρ_inv X
  | ρ_inv X => ρ_hom X
  | star f => star (f.inv)
  | χ_hom X Y => χ_inv X Y
  | χ_inv X Y => χ_hom X Y
  | ε_hom X => ε_inv X
  | ε_inv X => ε_hom X

end CategoryTheory.FreeInvolutiveCategory

