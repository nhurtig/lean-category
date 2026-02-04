import Mathlib
import Mathlib.CategoryTheory.Category.Basic

macro "easy" : tactic => `(tactic| first | (rfl; done) | (simp; done) | (aesop; done))

syntax "qind" Lean.Parser.Tactic.elimTarget : tactic
macro_rules
| `(tactic| qind $x) => `(tactic| induction $x using Quotient.ind)

-- syntax "quotind" Lean.Parser.Tactic.elimTarget : tactic
-- macro_rules
--   | `(tactic| quotind $x) => `(tactic| induction $x using Quotient.ind <;> induction $x using Quotient.ind <;> easy)

syntax "quotinds" (Lean.Parser.Tactic.elimTarget)+ : tactic
macro_rules
  | `(tactic| quotinds $xs*) => `(tactic| $[induction $xs using Quotient.ind];*)

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
  hdom : dom = left ++ a :: b :: right := by easy
  hcod : cod = left ++ b :: a :: right := by easy

@[simp]
def BraidGenerator.inv {α : Type} {dom cod : List α} (g : BraidGenerator α dom cod) : BraidGenerator α cod dom :=
  ⟨g.left, !g.sign, g.b, g.a, g.right, by simp [g.hcod], by simp [g.hdom]⟩

class Extend {α : Type} (β : α → α → Type) [Append α] where
  extendLeft : (a : α) → (β d c) → (β (a ++ d) (a ++ c))
  extendRight : (a : α) → (β d c) → (β (d ++ a) (c ++ a))

instance : Extend (BraidGenerator α) where
  extendLeft a g := ⟨a ++ g.left, g.sign, g.a, g.b, g.right, by simp [g.hdom], by simp [g.hcod]⟩
  extendRight a g := ⟨g.left, g.sign, g.a, g.b, g.right ++ a, by simp [g.hdom], by simp [g.hcod]⟩

inductive TypedList {α : Type} (β : α → α → Type) : (dom cod : α) → Type where
  | nil (obj : α) : TypedList β obj obj
  -- | cons (head : β d m₁) (tail : TypedList β m₂ c) (hm : m₁ = m₂ := by first | rfl | simp | aesop | grind) : TypedList β d c
  | cons (head : β d m) (tail : TypedList β m c) : TypedList β d c

@[simp]
def TypedList.append :
    TypedList β d m → TypedList β m c → TypedList β d c
  | .nil d, ys => ys
  | .cons h t, ys => .cons h (t.append ys)

instance : HAppend (TypedList β d m) (TypedList β m c) (TypedList β d c)  where
  hAppend := TypedList.append

@[grind, simp]
lemma TypedList.append_nil_left :
    {x : TypedList β d c} → (TypedList.nil (β := β) d) ++ x = x := by
  intros x
  induction x
  all_goals simp [HAppend.hAppend, TypedList.append]

@[grind, simp]
lemma TypedList.append_nil_right :
    {x : TypedList β d c} → x ++ (TypedList.nil (β := β) c) = x := by
  intros x
  induction x
  all_goals simp [HAppend.hAppend, TypedList.append]
  aesop

@[grind, simp]
lemma TypedList.cons_append {x : TypedList β d m} {y : TypedList β m c} {head : β h d} :
    (TypedList.cons head x) ++ y = TypedList.cons head (x ++ y) := by
  induction x
  all_goals simp [HAppend.hAppend, TypedList.append]

@[grind, simp]
lemma TypedList.append_assoc {x : TypedList β d m} {y : TypedList β m n} {z : TypedList β n c} :
    x ++ y ++ z = x ++ (y ++ z) := by
  induction x
  case nil obj => simp
  case cons head tail ih =>
    simp [HAppend.hAppend, TypedList.append] at ⊢ ih
    rw [ih]

@[simp]
def TypedList.extendLeft {β : α → α → Type} [Append α] [Extend β] (a : α) : TypedList β d c → TypedList β (a ++ d) (a ++ c)
  | .nil obj => .nil (a ++ obj)
  | .cons head tail => .cons (Extend.extendLeft a head) (tail.extendLeft a)

@[simp]
def TypedList.extendRight {β : α → α → Type} [Append α] [Extend β] (a : α) : TypedList β d c → TypedList β (d ++ a) (c ++ a)
  | .nil obj => .nil (obj ++ a)
  | .cons head tail => .cons (Extend.extendRight a head) (tail.extendRight a)

@[simp]
def TypedList.prod {α : Type} {β : α → α → Type} [Append α] [Extend β] {d₁ c₁ d₂ c₂ : α} (left : TypedList β d₁ c₁) (right : TypedList β d₂ c₂) : TypedList β (d₁ ++ d₂) (c₁ ++ c₂) :=
  (left.extendRight d₂) ++ (right.extendLeft c₁)

-- use ⊗ for prod
notation x " ⊗ " y => TypedList.prod x y

@[simp, grind]
def TypedList.inv (g_inv : {c d : α} → (β d c) → (β c d)) : TypedList β d c → TypedList β c d
  | .nil obj => .nil obj
  | .cons head tail => (tail.inv g_inv) ++ (TypedList.cons (g_inv head) (TypedList.nil d))

@[simp, grind]
lemma TypedList.inv_append {α : Type} {β : α → α → Type} {d m c : α} {g_inv} {x : TypedList β d m} {y : TypedList β m c} :
    (x ++ y).inv g_inv = (y.inv g_inv) ++ (x.inv g_inv) := by
  induction x generalizing c
  all_goals aesop

abbrev BraidWord α := TypedList (BraidGenerator α)

@[simp]
def BraidWord.inv (w : BraidWord α d c) : BraidWord α c d :=
  TypedList.inv BraidGenerator.inv w

@[simp, grind]
lemma BraidWord.inv_append {α : Type} {d m c : List α} {x : BraidWord α d m} {y : BraidWord α m c} : BraidWord.inv (x ++ y) = (y.inv ++ x.inv) := by
  simp

-- def BraidWord.inv_idem {α : Type} {d c : List α} (w : BraidWord α d c) : BraidWord.inv (BraidWord.inv w) = w := by
--   induction w
--   case nil obj => simp
--   case cons head tail ih =>
--     simp [BraidWord.inv_append, ih]

@[grind]
inductive BraidEquiv : BraidWord α d c → BraidWord α d c → Prop where
  | refl (x : BraidWord α d c) : BraidEquiv x x
  | symm {x y : BraidWord α d c} : BraidEquiv x y → BraidEquiv y x
  | trans {x y z : BraidWord α d c} : BraidEquiv x y → BraidEquiv y z → BraidEquiv x z
  | ignore_head {h : BraidWord α d m} {x y : BraidWord α m c} : BraidEquiv x y → BraidEquiv (h ++ x) (h ++ y)
  | ignore_tail {x y : BraidWord α d m} {t : BraidWord α m c} : BraidEquiv x y → BraidEquiv (x ++ t) (y ++ t)
  | inv : s₁ ≠ s₂ → BraidEquiv
    (TypedList.cons ⟨l, s₁, a, b, r, by easy, by easy⟩ (TypedList.cons ⟨l, s₂, b, a, r, by easy, by easy⟩ (TypedList.nil (l ++ a :: b :: r))))
    (TypedList.nil (l ++ a :: b :: r))
  | comm : BraidEquiv
    (TypedList.cons ⟨l, s₁, w, x, m ++ y :: z :: r, by easy, by easy⟩
      (TypedList.cons ⟨l ++ x :: w :: m, s₂, y, z, r, by easy, by easy⟩
        (TypedList.nil (l ++ x :: w :: (m ++ z :: y :: r)))))
    (TypedList.cons ⟨l ++ w :: x :: m, s₂, y, z, r, by easy, by easy⟩
      (TypedList.cons ⟨l, s₁, w, x, m ++ z :: y :: r, by easy, by easy⟩
        (TypedList.nil (l ++ x :: w :: (m ++ z :: y :: r)))))
  | yb : BraidEquiv
    (TypedList.cons ⟨l, s, x, y, z :: r, by easy, by easy⟩
      (TypedList.cons ⟨l ++ [y], s, x, z, r, by easy, by easy⟩
        (TypedList.cons ⟨l, s, y, z, x :: r, by easy, by easy⟩
          (TypedList.nil (l ++ z :: y :: x :: r)))))
    (TypedList.cons ⟨l ++ [x], s, y, z, r, by easy, by easy⟩
      (TypedList.cons ⟨l, s, x, z, y :: r, by easy, by easy⟩
        (TypedList.cons ⟨l ++ [z], s, x, y, r, by easy, by easy⟩
          (TypedList.nil (l ++ z :: y :: x :: r)))))

def BraidWord.inv_cancel {α : Type} {d c : List α} (w : BraidWord α d c) : BraidEquiv (w ++ w.inv) (TypedList.nil d) := by
  induction w
  case nil obj =>
    simp [HAppend.hAppend]
    grind
  case cons d m c head tail ih =>
    apply BraidEquiv.trans (y := (TypedList.cons head (TypedList.cons head.inv (TypedList.nil d))))
    · apply BraidEquiv.trans (y := ((TypedList.cons head (TypedList.nil m)) ++ ((tail ++ BraidWord.inv tail) ++ TypedList.cons head.inv (TypedList.nil d))))
      · simp
        apply BraidEquiv.refl
      · apply BraidEquiv.trans
        · exact BraidEquiv.ignore_head <| BraidEquiv.ignore_tail ih
        · apply BraidEquiv.refl
    · cases head
      simp
      grind only [BraidEquiv.inv]

@[simp, grind]
def setoidBraid (α d c) : Setoid (BraidWord α d c) :=
  ⟨BraidEquiv, ⟨BraidEquiv.refl, BraidEquiv.symm, BraidEquiv.trans⟩⟩

def Braid (α d c) := Quotient (setoidBraid α d c)

@[simp]
def Braid.comp {X Y Z : List α} (f : Braid α X Y) (g : Braid α Y Z) : Braid α X Z :=
  Quotient.liftOn₂ f g
    (fun x y => ⟦x ++ y⟧)
    (by
      intros a₁ a₂ b₁ b₂ ha hb
      simp
      apply Quotient.sound ?_
      apply BraidEquiv.trans (y := a₁ ++ b₂)
      · exact BraidEquiv.ignore_head hb
      · exact BraidEquiv.ignore_tail ha)

@[simp]
def Braid.inv {X Y : List α} (f : Braid α X Y) : Braid α Y X :=
  Quotient.liftOn f
    (fun x => ⟦BraidWord.inv x⟧)
    (by
      intros a b hab
      simp
      clear f
      apply Quotient.sound ?_
      induction hab
      -- all_goals try simp
      -- all_goals try (first | grind | apply BraidEquiv.symm; grind)
      case refl x => exact BraidEquiv.refl x.inv
      case symm ih =>
        exact BraidEquiv.symm ih
      case trans ih₁ ih₂ =>
        apply BraidEquiv.trans ih₁ ih₂
      case ignore_head ih =>
        simp
        exact BraidEquiv.ignore_tail ih
      case ignore_tail ih =>
        simp
        exact BraidEquiv.ignore_head ih
      case inv =>
        exact BraidEquiv.inv <| by aesop
      case comm =>
        simp
        apply BraidEquiv.symm
        grind
      case yb =>
        simp
        apply BraidEquiv.symm
        grind)

instance : CategoryTheory.Groupoid (List α) where
  Hom := Braid α
  id obj := ⟦TypedList.nil obj⟧
  comp := Braid.comp
  inv := Braid.inv
  id_comp x := by qind x; easy
  comp_id x := by qind x; easy
  assoc x y z := by qind x; qind y; qind z; easy
  inv_comp x := by
    qind x
    simp
    sorry
  -- comp_inv x := by quotind
