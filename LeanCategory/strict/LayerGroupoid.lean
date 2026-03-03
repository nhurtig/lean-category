import Mathlib
import LeanCategory.Instances
import LeanCategory.Inverse

universe u

open CategoryTheory

/- A SwapObj is either a κ (representing a box) or an r (a free strand) -/
inductive SwapObj (α : Type u) where
| kappa : MonoidalWord α → SwapObj α
| r : α → SwapObj α
deriving Repr

/-- The semantics of a single SwapObj -/
def SwapObj.toMonoidalWord {α} : SwapObj α → MonoidalWord α
  | .kappa w => w
  | .r a => MonoidalWord.of a

/-- Reverse a SwapObj's κ; do nothing to the free r strands -/
def SwapObj.reverse_kappa {α} : SwapObj α → SwapObj α
  | .kappa w => .kappa w.reverse
  | .r a => .r a

/-- Reversing a SwapObj's κ reverses its MonoidalWord representation -/
lemma SwapObj.reverse_monoidal (X : SwapObj α) : X.reverse_kappa.toMonoidalWord = X.toMonoidalWord.reverse := by
  cases X
  all_goals simp [reverse_kappa, toMonoidalWord, MonoidalWord.reverse]

-- TODO document tiny helper
def MonoidalWord.flatten_swap {α} (X : MonoidalWord (SwapObj α)) : MonoidalWord α :=
  X.map SwapObj.toMonoidalWord |> MonoidalWord.flatten

-- TODO document tiny helper
def MonoidalWord.reverse_kappa {α} (X : MonoidalWord (SwapObj α)) : MonoidalWord (SwapObj α) :=
  X.map SwapObj.reverse_kappa

/-- The very simple groupoid for the twist part of the layer subgroupoid.
There are only two objects, and two non-identity morphisms. It's thin, and
the objects are isomorphic. -/
@[simp]
def TwistGroupoid : Groupoid Bool where
  Hom _ _ := Unit -- one morphism between any two objects → 4 morphisms total
  id _ := ()
  comp _ _ := ()
  inv _ := ()

@[simp]
def LayerGroupoid.obj (α : Type u) := ((MonoidalWord (SwapObj α)) × Bool)

/-- LayerGroupoid is the direct product of the swap and twist groupoids -/
@[simp]
instance LayerGroupoid (α) : Groupoid (LayerGroupoid.obj α) := @groupoidProd _ _ (BraidGroupoid.BraidGroupoid_groupoid (SwapObj α)) TwistGroupoid

/-- If the bool is true, call f. Otherwise, do nothing. -/
@[simp]
def Bool.apply_if (f : α → α) (a : α) : Bool → α
  | true => f a
  | false => a

namespace BraidGroupoid

/-- The swap portion of the ϕ reconstruction functor, on raw Hom words -/
def Hom.phi_swap : (X ⟶ᵇ Y) → (X.flatten_swap ⟶ᵇ Y.flatten_swap)
  | .id _ => 1
  | .α_hom X Y Z => .α_hom _ _ _
  | .α_inv X Y Z => .α_inv _ _ _
  | .l_hom X => .l_hom _
  | .l_inv X => .l_inv _
  | .ρ_hom X => .ρ_hom _
  | .ρ_inv X => .ρ_inv _
  | .σ_hom X Y => .σ_hom _ _
  | .σ_inv X Y => .σ_inv _ _
  | .comp f g => f.phi_swap.comp g.phi_swap
  | .tensor f g => f.phi_swap * g.phi_swap

/-- The swap portion of the ϕ reconstruction functor preserves equivalence -/
lemma HomEquiv.phi_swap {f g : X ⟶ᵇ Y} : f ≈ g → f.phi_swap ≈ g.phi_swap := by
  intro h
  induction h
  any_goals (constructor; done)
  case symm ih => symm; assumption
  case trans ih₁ ih₂ => exact .trans ih₁ ih₂
  case comp ihf ihg => apply comp ihf ihg
  case tensor ihf ihg => apply tensor ihf ihg

/-- The positive delta twist -/
def Hom.delta : (X : MonoidalWord α) → X ⟶ᵇ X.reverse
  | .unit => .id .unit
  | .of a => .id (.of a)
  | X * Y => (σ_hom X Y).comp (delta Y * delta X)

/-- Perform a positive delta twist on every κ in the word -/
def Hom.delta_kappa : (X : MonoidalWord (SwapObj α)) → X.flatten_swap ⟶ᵇ X.reverse_kappa.flatten_swap
  | .unit => .id .unit
  | .of (SwapObj.r a) => .id (.of a)
  | .of (SwapObj.kappa w) => delta w
  | X * Y => delta_kappa X * delta_kappa Y

/-- The swap portion of the ϕ reconstruction functor -/
def phi_swap : (MonoidalWord (SwapObj α)) ⥤ MonoidalWord α where
  obj X := X.flatten_swap
  map {X Y} f := Quotient.lift (fun f => ⟦f.phi_swap⟧) (by
    intro f g h
    apply Quotient.sound
    apply HomEquiv.phi_swap
    assumption) f
  map_comp f g := by
    rcases f with ⟨f⟩
    rcases g with ⟨g⟩
    apply Quotient.sound
    rfl

@[simp]
lemma phi_swap_obj (X : MonoidalWord (SwapObj α)) :
    phi_swap.obj X = X.flatten_swap := rfl

@[simp]
lemma phi_swap_map {X Y : MonoidalWord (SwapObj α)} (f : X ⟶ᵇ Y) :
    phi_swap.map ⟦f⟧ = ⟦f.phi_swap⟧ := rfl

@[simp]
lemma phi_swap_map_id {X : MonoidalWord (SwapObj α)} :
    phi_swap.map (𝟙 X) = 𝟙 (phi_swap.obj X) := rfl

/-- The abbreviation for `⟦f⟧` as a morphism. -/
abbrev homMk {α : Type u} {X Y : MonoidalWord α} (f : Hom X Y) : X ⟶ Y := ⟦f⟧

/-- The ϕ reconstruction functor -/
def phi : (LayerGroupoid.obj α) ⥤ MonoidalWord α where
  obj := fun (X, b) => (b.apply_if (·.reverse_kappa) X).flatten_swap
  map {X Y} f := match X, Y with
    | (X, false), (Y, false) =>
      phi_swap.map f.1 -- no twisting
    | (X, true), (Y, true) =>
      (Groupoid.inv (homMk (Hom.delta_kappa X))) ≫ phi_swap.map f.1 ≫ homMk (Hom.delta_kappa Y)
    | (X, true), (Y, false) =>
      (Groupoid.inv (homMk (Hom.delta_kappa X))) ≫ phi_swap.map f.1
    | (X, false), (Y, true) =>
      phi_swap.map f.1 ≫ homMk (Hom.delta_kappa Y)
  -- map {X Y} f := match X, Y, f with
  --   | (X, false), (Y, false), (f, ()) =>
  --     phi_swap.map f -- no twisting
  --   | (X, true), (Y, true), (f, ()) =>
  --     inv (homMk (Hom.delta_kappa X)) ≫ phi_swap.map f ≫ homMk (Hom.delta_kappa Y)
  --   | (X, true), (Y, false), (f, ()) =>
  --     inv (homMk (Hom.delta_kappa X)) ≫ phi_swap.map f
  --   | (X, false), (Y, true), (f, ()) =>
  --     phi_swap.map f ≫ homMk (Hom.delta_kappa Y)
  map_id X := by
    rcases X with ⟨X, b⟩
    cases b
    all_goals simp
  map_comp {X Y Z} f g := by
    rcases X with ⟨X, b₁⟩
    rcases Y with ⟨Y, b₂⟩
    rcases Z with ⟨Z, b₃⟩
    cases b₁ <;> cases b₂ <;> cases b₃
    all_goals simp

end BraidGroupoid

-- TODO make τ
-- TODO we'll have the SwapObj carry BOTH the above and below information, project out for ϕ/τ
-- TODO make the layer subgroupoid thingy: a "contravariant" function (not functor) from
-- LayerGroupoid to KnitCategory.Hom, putting ϕ on top, τ⁻¹ on bottom, modified layer in the middle
-- TODO make that a commutative diagram in KnitCategory.HomEquiv
