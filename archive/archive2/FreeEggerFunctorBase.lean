import LeanCategory.FreeEggerQuiver

namespace CategoryTheory.FreeTwistedCategory

variable {C : Type u} [userQuiver : Quiver.{v} (F C)]

variable {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [InvolutiveCategory D] (m : C → D)

open MonoidalCategory
open InvolutiveCategory
open TwistedCategory

def projectObj : F C → D
  | .of X => m X
  | .unit => 𝟙_ D
  | .tensor X Y => X.projectObj ⊗ Y.projectObj
  | .star X => X.projectObj⋆

omit userQuiver in
@[simp]
lemma projectObj_of (X : C) : projectObj m (.of X) = m X := rfl

@[simp]
lemma projectObj_unit : projectObj m (𝟙_ _) = 𝟙_ D := rfl

@[simp]
lemma projectObj_tensor (X Y : F C) : projectObj m (X ⊗ Y) =
    projectObj m X ⊗ projectObj m Y := rfl

@[simp]
lemma projectObj_star (X : F C) : projectObj m X⋆ = (projectObj m X)⋆ := rfl

end CategoryTheory.FreeTwistedCategory

