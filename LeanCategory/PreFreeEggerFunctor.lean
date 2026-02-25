import LeanCategory.PreFreeEggerGood
import LeanCategory.FreeEggerGood

@[simp]
lemma dist_mul [StarMonoid P] [StarMonoid Q] {x : P} {m : P →⋆* Q} : m (x * y) = (m x) * (m y) := by sorry

variable {P Q : Type u}
variable [StarMonoid P] [userP : Quiver.{v} P] [StarMonoid Q] [userQ : Quiver.{v} Q]

variable (m : P →⋆* Q)
variable (M : {X Y : P} → (X ⟶ Y) → (m X ⟶ m Y))

open CategoryTheory

@[simp]
def Hom.myfunct {X Y : P} : (X ⟶ᵥ Y) → ((m X) ⟶ᵥ (m Y))
  | .of f => .of <| M f
  | .id X => 𝟙 <| m X
  | .comp f g => f.myfunct ≫ g.myfunct
  /- | .tensor f g => by simpa using f.myfunct ⊗ᵥ g.myfunct -/
  | tensor f g => eqToHom (by simp) ≫ (f.myfunct ⊗ᵥ g.myfunct) ≫ eqToHom (by simp)
  /- | .star f => by simpa using f.myfunct⋆ᵥ -/
  | .star f => eqToHom (by simp) ≫ f.myfunct⋆ᵥ ≫ eqToHom (by simp)
  /- | .twist_hom X => by simpa using .twist_hom (m X) -/
  | .twist_hom X => eqToHom (by simp) ≫ .twist_hom (m X) ≫ eqToHom (by simp)
  | .twist_inv X => eqToHom (by simp) ≫ .twist_inv (m X) ≫ eqToHom (by simp)

-- TODO maybe we should just prove it straight up on the quotient? That way, we can use
-- simp to rewrite stuff... just like the monoidal file!
-- See the mk_* lemmas here:
#check FreeMonoidalCategory
-- then the normalizing lemmas here:
#check MonoidalCategory

-- we'll need to completely redo the mk_* lemmas, but we can use the normalizing lemmas for monoidal (just needs
-- updating w/ the involution/star/twist stuff)

instance proj : P ⥤ Q where
  obj := m
  map {X Y} := Quotient.lift (⟦·.myfunct m M⟧) <| by
    intros f g h
    simp
    induction h
    any_goals simp
    any_goals grind
    sorry

def HomEquiv.myfunct {X Y : P} {f g : X ⟶ᵥ Y} (h : f ≈ g) :
    ((f.myfunct m M) ≈ (g.myfunct m M)) := by
  induction h
  any_goals simp
  any_goals constructor; done
  any_goals grind
  /- any_goals constructor <;> grind -/
  case id_tensor_id =>
    eqToHom_eq_eqToHom
  case tensor_comp_tensor =>
    simp
    sorry
  sorry

