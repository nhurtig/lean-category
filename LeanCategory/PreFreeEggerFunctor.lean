import LeanCategory.PreFreeEggerGood
/- import LeanCategory.FreeEggerGood -/

@[simp]
lemma dist_mul [StarMonoid P] [StarMonoid Q] {x : P} {m : P →⋆* Q} : m (x * y) = (m x) * (m y) := by sorry

variable {P Q : Type u}
variable [StarMonoid P] [userP : Quiver.{v} P] [StarMonoid Q] [userQ : Quiver.{v} Q]

variable (m : P →⋆* Q)
variable (M : {X Y : P} → (X ⟶ Y) → (m X ⟶ m Y))

open CategoryTheory

@[simp]
def Hom.proj {X Y : P} : (X ⟶ᵥ Y) → ((m X) ⟶ᵥ (m Y))
  | .of f => .of <| M f
  | .id X => 𝟙 <| m X
  | .comp f g => f.proj ≫ g.proj
  /- | .tensor f g => by simpa using f.myfunct ⊗ᵥ g.myfunct -/
  | tensor f g => eqToHom (by simp) ≫ (f.proj ⊗ᵥ g.proj) ≫ eqToHom (by simp)
  /- | .star f => by simpa using f.myfunct⋆ᵥ -/
  | .star f => eqToHom (by simp) ≫ f.proj⋆ᵥ ≫ eqToHom (by simp)
  /- | .twist_hom X => by simpa using .twist_hom (m X) -/
  | .twist_hom X => eqToHom (by simp) ≫ .twist_hom (m X) ≫ eqToHom (by simp)
  | .twist_inv X => eqToHom (by simp) ≫ .twist_inv (m X) ≫ eqToHom (by simp)

@[simp]
def Hom.proj_eqToHom {X Y : P} {h : X = Y} : (eqToHom h).proj m M = eqToHom (by simp [h]) := by
  cases h
  rfl

