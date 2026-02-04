import Mathlib
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

-- explicit, obvious groupoid defn first
-- no need for explicit composition, but
-- we need to have all types at the same
-- level (typed list)


-- use list-of-generator
structure BraidGenerator (α : Type) (dom cod : List α) where
  left : List α
  sign : Bool -- true is left over right
  a : α
  b : α
  right : List α
  hdom : dom = left ++ [a, b] ++ right := by simp
  hcod : cod = left ++ [b, a] ++ right := by simp

class Extend {α : Type} (β : α → α → Type) [Append α] where
  extendLeft : (a : α) → (β d c) → (β (a ++ d) (a ++ c))
  extendRight : (a : α) → (β d c) → (β (d ++ a) (c ++ a))

instance : Extend (BraidGenerator α) where
  extendLeft a g := ⟨a ++ g.left, g.sign, g.a, g.b, g.right, by simp [g.hdom], by simp [g.hcod]⟩
  extendRight a g := ⟨g.left, g.sign, g.a, g.b, g.right ++ a, by simp [g.hdom], by simp [g.hcod]⟩

inductive TypedList {α : Type} (β : α → α → Type) : (dom cod : α) → Type where
  | nil (obj : α) : TypedList β obj obj
  | cons (head : β d m) (tail : TypedList β m c) : TypedList β d c

def TypedList.append :
    TypedList β d m → TypedList β m c → TypedList β d c
  | .nil d, ys => ys
  | .cons h t, ys => .cons h (t.append ys)

def TypedList.extendLeft {β : α → α → Type} [Append α] [Extend β] (a : α) : TypedList β d c → TypedList β (a ++ d) (a ++ c)
  | .nil obj => .nil (a ++ obj)
  | .cons head tail => .cons (Extend.extendLeft a head) (tail.extendLeft a)

def TypedList.extendRight {β : α → α → Type} [Append α] [Extend β] (a : α) : TypedList β d c → TypedList β (d ++ a) (c ++ a)
  | .nil obj => .nil (obj ++ a)
  | .cons head tail => .cons (Extend.extendRight a head) (tail.extendRight a)

@[simp]
instance : HAppend (TypedList β d m) (TypedList β m c) (TypedList β d c)  where
  hAppend := TypedList.append

def TypedList.prod {α : Type} {β : α → α → Type} [Append α] [Extend β] {d₁ c₁ d₂ c₂ : α} (left : TypedList β d₁ c₁) (right : TypedList β d₂ c₂) : TypedList β (d₁ ++ d₂) (c₁ ++ c₂) :=
  (left.extendRight d₂) ++ (right.extendLeft c₁)

-- use ⊗ for prod
notation x " ⊗ " y => TypedList.prod x y

abbrev BraidWord α := TypedList (BraidGenerator α)

-- instance {dom mid cod : List α} : HAppend (BraidWord α dom mid) (BraidWord α mid cod) (BraidWord α dom cod) where
--   hAppend := List.append

-- lemma BraidWord.id_left (x : BraidWord α) : ([] : BraidWord α) ++ x = x := by grind

inductive BraidEquiv : BraidWord α d c → BraidWord α d c → Prop where
  -- | refl (x : BraidWord α) : BraidEquiv x x
  | refl (x : BraidWord α d c) : BraidEquiv x x
  -- | symm {x y : BraidWord α} : BraidEquiv x y → BraidEquiv y x
  | symm {x y : BraidWord α d c} : BraidEquiv x y → BraidEquiv y x
  -- | trans {x y z : BraidWord α} : BraidEquiv x y → BraidEquiv y z → BraidEquiv x z
  | trans {x y z : BraidWord α d c} : BraidEquiv x y → BraidEquiv y z → BraidEquiv x z
  -- | ignore_head {h x y : BraidWord α} (hdom : x.dom = y.dom := by grind) : BraidEquiv x y → BraidEquiv (h ++ x) (h ++ y)
  | ignore_head {h : BraidWord α d m} {x y : BraidWord α m c} : BraidEquiv x y → BraidEquiv (h ++ x) (h ++ y)
  -- -- could peel these suckers open
  -- | ignore_tail {x y t : BraidWord α} : BraidEquiv x y → BraidEquiv (x ++ t) (y ++ t)
  | ignore_tail {x y : BraidWord α d m} {t : BraidWord α m c} : BraidEquiv x y → BraidEquiv (x ++ t) (y ++ t)
  -- | inv : s₁ ≠ s₂ → BraidEquiv ⟨[⟨l, s₁, a, b, r⟩, ⟨l, s₂, b, a, r⟩], l ++ [a, b] ++ r, l ++ [b, a] ++ r⟩ ⟨[], l ++ [a, b] ++ r, l ++ [b, a] ++ r⟩
  | inv : s₁ ≠ s₂ → BraidEquiv
    (TypedList.cons ⟨l, s₁, a, b, r, by rfl, by rfl⟩ (TypedList.cons ⟨l, s₂, b, a, r, by rfl, by rfl⟩ (TypedList.nil (l ++ [a, b] ++ r))))
    (TypedList.nil (l ++ [a, b] ++ r))
  -- | comm : BraidEquiv
  --   ⟨[⟨l, s₁, w, x, m ++ [y, z] ++ r⟩, ⟨l ++ [x, w] ++ m, s₂, y, z, r⟩], d, c⟩
  --   ⟨[⟨l ++ [w, x] ++ m, s₂, y, z, r⟩, ⟨l, s₁, w, x, m ++ [z, y] ++ r⟩], d, c⟩
  | comm : BraidEquiv
    (TypedList.cons ⟨l, s₁, w, x, m ++ [y, z] ++ r, by rfl, by rfl⟩
      (TypedList.cons ⟨l ++ [x, w] ++ m, s₂, y, z, r, by simp, by rfl⟩
        (TypedList.nil (l ++ [x, w] ++ m ++ [z, y] ++ r))))
    (TypedList.cons ⟨l ++ [w, x] ++ m, s₂, y, z, r, by simp, by rfl⟩
      (TypedList.cons ⟨l, s₁, w, x, m ++ [z, y] ++ r, by simp, by simp⟩
        (TypedList.nil (l ++ [x, w] ++ m ++ [z, y] ++ r))))
  -- | yb : BraidEquiv
  --   ⟨[⟨l, s, x, y, [z] ++ r⟩,
  --    ⟨l ++ [y], s, x, z, r⟩,
  --    ⟨l, s, y, z, [x] ++ r⟩], d, c⟩
  --   ⟨[⟨l ++ [x], s, y, z, r⟩,
  --    ⟨l, s, x, z, [y] ++ r⟩,
  --    ⟨l ++ [z], s, x, y, r⟩], d, c⟩
  | yb : BraidEquiv
    (TypedList.cons ⟨l, s, x, y, [z] ++ r, by rfl, by rfl⟩
      (TypedList.cons ⟨l ++ [y], s, x, z, r, by simp, by rfl⟩
        (TypedList.cons ⟨l, s, y, z, [x] ++ r, by simp, by simp⟩
          (TypedList.nil (l ++ [z, y, x] ++ r)))))
    (TypedList.cons ⟨l ++ [x], s, y, z, r, by simp, by rfl⟩
      (TypedList.cons ⟨l, s, x, z, [y] ++ r, by simp, by rfl⟩
        (TypedList.cons ⟨l ++ [z], s, x, y, r, by simp, by simp⟩
          (TypedList.nil (l ++ [z, y, x] ++ r)))))

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

-- @[simp]
-- -- not entirely sure this is true -- what if the middles are garbage?
-- -- yup, this was false. Fixed w/ right direction
-- lemma BraidWord.append_types {x y : BraidWord α} : (x.Types ∧ y.Types) → (x ++ y).Types  := by
--   sorry

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
-- @[simp]
-- lemma BraidWord.type_mid {x y : BraidWord α} : (x ++ y).Types ↔ ∃ m, BraidWord.TypesHelper x.dom m x.word ∧ BraidWord.TypesHelper m y.cod y.word := by
--   rcases x with ⟨x, dom, m₁⟩
--   rcases y with ⟨y, m₂, cod⟩
--   unfold HAppend.hAppend
--   simp
--   induction x generalizing dom
--   all_goals simp
--   aesop

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
