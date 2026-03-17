import Mathlib
import LeanCategory.NatDefinition.ToNat
import LeanCategory.NatDefinition.FromNat

namespace CategoryTheory.NatDefinition

open FreeTwistedCategoryQuiver

lemma its_just_mkObj' (X : TQ C) : FreeTwistedCategoryQuiver.projectObj mkObj X = ⟨X.as⟩ := by
  induction X using FreeTwistedCategoryQuiver.recOn'
  case unit => rfl
  case of => rfl
  case star ih =>
    simp
    rw [ih]
    rfl
  case tensor ihX ihY =>
    simp
    rw [ihX, ihY]
    rfl

open CategoryTheory MonoidalCategory InvolutiveCategory TwistedCategory

theorem comp_eq : toNat ⋙ fromNat = 𝟭 (TQ C) := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intros X
    simp
    unfold toNat fromNat project
    simp
    rw [its_just_mkObj']
  case h_map =>
    intro X Y f
    induction f using Quotient.inductionOn
    rename_i f
    simp
    induction f <;> try simp_all
    all_goals sorry

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {F : C ⥤ D} {G : D ⥤ C}

def decidable_carry {X Y : D} (decider : DecidableEq (G.obj X ⟶ G.obj Y)) (h : G ⋙ F = 𝟭 D) :
    DecidableEq (X ⟶ Y) := by
  intros f g
  have decided := decider (G.map f) (G.map g)
  cases decided
  case isTrue eq =>
    apply isTrue
    have eq' : (G ⋙  F).map f = (G ⋙  F).map g := by
      simp
      rw [eq]
    rw [h] at eq'
    exact eq'
  case isFalse neq =>
    apply isFalse
    intros hfalse
    rw [hfalse] at neq
    simp at neq

-- the actually-proven result of the paper
def Nat_decider : ∀ X Y : N C, DecidableEq (X ⟶ Y) := sorry

def TQ_decider : ∀ X Y : TQ C, DecidableEq (X ⟶ Y) := fun X Y ↦
  decidable_carry (Nat_decider (toNat.obj X) (toNat.obj Y)) comp_eq

end CategoryTheory.NatDefinition

