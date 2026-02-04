import Mathlib
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

-- explicit, obvious groupoid defn first

-- use list-of-generator
structure BraidGenerator α where
  left : List α
  sign : Bool -- true is left over right
  a : α
  b : α
  right : List α

def BraidGenerator.dom (g : BraidGenerator α) :=
  g.left ++ [g.a, g.b] ++ g.right

def BraidGenerator.cod (g : BraidGenerator α) :=
  g.left ++ [g.b, g.a] ++ g.right

structure BraidWord α where
  word : List (BraidGenerator α)
  dom : List α
  cod : List α

-- instance {dom mid cod : List α} : HAppend (BraidWord α dom mid) (BraidWord α mid cod) (BraidWord α dom cod) where
--   hAppend := List.append
@[simp]
instance : HAppend (BraidWord α) (BraidWord α) (BraidWord α) where
  hAppend x y := ⟨List.append x.word y.word, x.dom, y.cod⟩

-- lemma BraidWord.id_left (x : BraidWord α) : ([] : BraidWord α) ++ x = x := by grind

inductive BraidEquiv : BraidWord α → BraidWord α → Prop where
  | refl (x : BraidWord α) : BraidEquiv x x
  | symm {x y : BraidWord α} : BraidEquiv x y → BraidEquiv y x
  | trans {x y z : BraidWord α} : BraidEquiv x y → BraidEquiv y z → BraidEquiv x z
  | ignore_head {h x y : BraidWord α} (hdom : x.dom = y.dom := by grind) : BraidEquiv x y → BraidEquiv (h ++ x) (h ++ y)
  -- could peel these suckers open
  | ignore_tail {x y t : BraidWord α} : BraidEquiv x y → BraidEquiv (x ++ t) (y ++ t)
  | inv : s₁ ≠ s₂ → BraidEquiv ⟨[⟨l, s₁, a, b, r⟩, ⟨l, s₂, b, a, r⟩], l ++ [a, b] ++ r, l ++ [b, a] ++ r⟩ ⟨[], l ++ [a, b] ++ r, l ++ [b, a] ++ r⟩
  | comm : BraidEquiv
    ⟨[⟨l, s₁, w, x, m ++ [y, z] ++ r⟩, ⟨l ++ [x, w] ++ m, s₂, y, z, r⟩], d, c⟩
    ⟨[⟨l ++ [w, x] ++ m, s₂, y, z, r⟩, ⟨l, s₁, w, x, m ++ [z, y] ++ r⟩], d, c⟩
  | yb : BraidEquiv
    ⟨[⟨l, s, x, y, [z] ++ r⟩,
     ⟨l ++ [y], s, x, z, r⟩,
     ⟨l, s, y, z, [x] ++ r⟩], d, c⟩
    ⟨[⟨l ++ [x], s, y, z, r⟩,
     ⟨l, s, x, z, [y] ++ r⟩,
     ⟨l ++ [z], s, x, y, r⟩], d, c⟩

@[simp]
def BraidWord.TypesHelper (dom cod : List α) : (List (BraidGenerator α)) → Prop
  | [] => dom = cod
  | g :: gs =>
    g.dom = dom ∧ BraidWord.TypesHelper g.cod cod gs

@[simp]
def BraidWord.Types (w : BraidWord α) : Prop :=
  BraidWord.TypesHelper w.dom w.cod w.word

/-
-- use list-of-generator
structure BraidGenerator α where
  left : List α
  sign : Bool -- true is left over right
  a : α
  b : α
  right : List α
  -- hdom : dom = left ++ [a, b] ++ right := by grind

abbrev BraidWord α (dom cod : List α) := List (BraidGenerator α)

def BraidWord.mk (dom cod : List α) (word : List (BraidGenerator α)) : BraidWord α dom cod :=
  word

-- instance {dom mid cod : List α} : HAppend (BraidWord α dom mid) (BraidWord α mid cod) (BraidWord α dom cod) where
--   hAppend := List.append
instance {dom mid cod : List α} : HAppend (BraidWord α dom mid) (BraidWord α mid cod) (BraidWord α dom cod) where
  hAppend := List.append

-- lemma BraidWord.id_left (x : BraidWord α) : ([] : BraidWord α) ++ x = x := by grind

inductive BraidEquiv : {dom cod : List α} → BraidWord α dom cod → BraidWord α dom cod → Prop where
  | refl (x : BraidWord α d c) : BraidEquiv x x
  | symm {x y : BraidWord α d c} : BraidEquiv x y → BraidEquiv y x
  | trans {x y z : BraidWord α d c} : BraidEquiv x y → BraidEquiv y z → BraidEquiv x z
  | ignore_head {h : BraidWord α d m} {x y : BraidWord α m c} : BraidEquiv x y → BraidEquiv (h ++ x) (h ++ y)
  | ignore_tail {x y : BraidWord α d m} {t : BraidWord α m c} : BraidEquiv x y → BraidEquiv (x ++ t) (y ++ t)
  | inv : s₁ ≠ s₂ → BraidEquiv [⟨l, s₁, a, b, r⟩, ⟨l, s₂, b, a, r⟩] (BraidWord.mk d c [])
  -- | inv : s₁ ≠ s₂ → BraidEquiv [⟨l, s₁, a, b, r⟩, ⟨l, s₂, b, a, r⟩] []
  | comm : BraidEquiv
    (BraidWord.mk d c [⟨l, s₁, w, x, m ++ [y, z] ++ r⟩, ⟨l ++ [x, w] ++ m, s₂, y, z, r⟩])
    (BraidWord.mk d c [⟨l ++ [w, x] ++ m, s₂, y, z, r⟩, ⟨l, s₁, w, x, m ++ [z, y] ++ r⟩])
  -- | comm : BraidEquiv
  --   [⟨l, s₁, a, b, m ++ [c, d] ++ r⟩, ⟨l ++ [b, a] ++ m, s₂, c, d, r⟩]
  --   [⟨l ++ [a, b] ++ m, s₂, c, d, r⟩, ⟨l, s₁, a, b, m ++ [d, c] ++ r⟩]
  | yb : BraidEquiv
    (BraidWord.mk d c [⟨l, s, x, y, [z] ++ r⟩,
     ⟨l ++ [y], s, x, z, r⟩,
     ⟨l, s, y, z, [x] ++ r⟩])
    (BraidWord.mk d c [⟨l ++ [x], s, y, z, r⟩,
     ⟨l, s, x, z, [y] ++ r⟩,
     ⟨l ++ [z], s, x, y, r⟩])
  -- | yb : BraidEquiv
  --   [⟨l, s, a, b, [c] ++ r⟩,
  --    ⟨l ++ [b], s, a, c, r⟩,
  --    ⟨l, s, b, c, [a] ++ r⟩]
  --   [⟨l ++ [a], s, b, c, r⟩,
  --    ⟨l, s, a, c, [b] ++ r⟩,
  --    ⟨l ++ [c], s, a, b, r⟩]

def BraidGenerator.dom (g : BraidGenerator α) :=
  g.left ++ [g.a, g.b] ++ g.right

def BraidGenerator.cod (g : BraidGenerator α) :=
  g.left ++ [g.b, g.a] ++ g.right

def BraidWord.TypesHelper (dom cod : List α) : (List (BraidGenerator α)) → Prop
  | [] => dom = cod
  | g :: gs =>
    g.dom = dom ∧ BraidWord.TypesHelper g.cod cod gs

def BraidWord.Types {dom cod : List α} (w : BraidWord α dom cod) : Prop :=
  BraidWord.TypesHelper dom cod w

-- def BraidWord.HasType (x : BraidWord α) : Prop :=
--   ∃ d c, x.Typed d c
-/

@[simp]
-- not entirely sure this is true -- what if the middles are garbage?
-- yup, this was false. Fixed w/ right direction
lemma BraidWord.append_types {x y : BraidWord α} : (x.Types ∧ y.Types) → (x ++ y).Types  := by
  sorry

-- TODO this is false -- need ⊗ to be defined
-- lemma BraidWord.typed_add {x y : BraidWord α} : (x ++ y).Typed d c →
--     ∃ d₁ d₂ c₁ c₂, d = d₁ ++ d₂ ∧ c = c₁ ++ c₂ ∧ x.Typed d₁ c₁ ∧ y.Typed d₂ c₂ := by
--   intro htyped
--   induction x generalizing d c
--   case nil =>
--     simp at htyped
--     exists [], d, [], c
--   case cons g gs ih =>
--     simp [BraidWord.Typed] at htyped
--     rcases htyped with ⟨hg, hrest⟩
--     subst d
--     specialize ih hrest
--     rcases ih with ⟨dgs, dy, cgs, cy, hd, hc, hxtyped, hytyped⟩
--     exists g.dom, d₂, cgs, cy
--     simp [hd, hc, hgd]

-- lemma BraidWord.type_unique {x : BraidWord α} : x.Typed d c₁ → x.Typed d c₂ → c₁ = c₂ := by
--   intros h₁ h₂
--   induction x generalizing d c₁ c₂
--   all_goals simp [BraidWord.Typed] at h₁ h₂
  -- all_goals aesop

-- yeah, this is the right way to state it
@[simp]
lemma BraidWord.type_mid {x y : BraidWord α} : (x ++ y).Types ↔ ∃ m, BraidWord.TypesHelper x.dom m x.word ∧ BraidWord.TypesHelper m y.cod y.word := by
  rcases x with ⟨x, dom, m₁⟩
  rcases y with ⟨y, m₂, cod⟩
  unfold HAppend.hAppend
  simp
  induction x generalizing dom
  all_goals simp
  aesop

-- this is false:
-- [] => something that cancels that doesn't line up
lemma BraidWord.type_preserve : BraidEquiv x y → (x.Types ↔ y.Types) := by
  intros heq
  -- unfold BraidWord.HasType at htype
  induction heq
  all_goals try grind
  -- case symm ih =>
  --   rw [Or.comm] at htype
  --   grind
  -- case trans ih₁ ih₂ =>
  --   cases htype with
  --   | inl hx =>
  --     specialize ih₁ (Or.inl hx)

  --     sorry
  --   sorry
  case ignore_head heq ih =>
    repeat rw [BraidWord.type_mid]
    -- simp
    -- apply exists_congr; intros d
    apply exists_congr; intros m
    simp; intros _
    -- apply exists_congr; intros c
    grind
    aesop
  case ignore_tail x y tail heq ih =>
    -- repeat rw [BraidWord.type_mid]
    simp [BraidWord.type_mid]
    aesop
  case inv =>

    sorry

structure TypedBraidWord α (dom cod : List α) where
  val : BraidWord α
  typed : val.Typed dom cod
