import Mathlib
import Mathlib.CategoryTheory.Category.Basic

macro "easy" : tactic => `(tactic| first | (rfl; done) | (simp; done) | (aesop; done) | (grind; done))

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
def BraidGenerator.inv {dom cod : List α} (g : BraidGenerator α dom cod) : BraidGenerator α cod dom :=
  ⟨g.left, !g.sign, g.b, g.a, g.right, by simp [g.hcod], by simp [g.hdom]⟩

@[simp, grind]
lemma BraidGenerator.inv_inv {dom cod : List α} (g : BraidGenerator α dom cod) : g.inv.inv = g := by easy

class Extend {α : Type} (β : α → α → Type) [Append α] where
  extendLeft : (a : α) → (β d c) → (β (a ++ d) (a ++ c))
  extendRight : (a : α) → (β d c) → (β (d ++ a) (c ++ a))

instance : Extend (BraidGenerator α) where
  extendLeft a g := ⟨a ++ g.left, g.sign, g.a, g.b, g.right, by simp [g.hdom], by simp [g.hcod]⟩
  extendRight a g := ⟨g.left, g.sign, g.a, g.b, g.right ++ a, by simp [g.hdom], by simp [g.hcod]⟩

@[simp]
def BraidGenerator.forget (g : BraidGenerator α d c) : BraidGenerator Unit (d.map (fun _ => ())) (c.map (fun _ => ())) :=
  ⟨g.left.map (fun _ => ()), g.sign, (), (), g.right.map (fun _ => ()), by simp [g.hdom], by simp [g.hcod]⟩

inductive TypedList {α : Type} (β : α → α → Type) : (dom cod : α) → Type where
  | nil (obj : α) : TypedList β obj obj
  -- | cons (head : β d m₁) (tail : TypedList β m₂ c) (hm : m₁ = m₂ := by first | rfl | simp | aesop | grind) : TypedList β d c
  | cons (head : β d m) (tail : TypedList β m c) : TypedList β d c

@[simp]
def TypedList.length {d c : α} : TypedList β d c → Nat
  | .nil obj => 0
  | .cons head tail => 1 + tail.length

@[simp]
def TypedList.append :
    TypedList β d m → TypedList β m c → TypedList β d c
  | .nil d, ys => ys
  | .cons h t, ys => .cons h (t.append ys)

instance : HAppend (TypedList β d m) (TypedList β m c) (TypedList β d c)  where
  hAppend := TypedList.append

@[simp, grind =]
lemma TypedList.length_append {d m c : α} (x : TypedList β d m) (y : TypedList β m c) :
    (x ++ y).length = x.length + y.length := by
  induction x
  all_goals simp [HAppend.hAppend, TypedList.append] at *
  all_goals easy

@[simp]
lemma TypedList.append_nil_left :
    {x : TypedList β d c} → (TypedList.nil (β := β) d) ++ x = x := by
  intros x
  induction x
  all_goals simp [HAppend.hAppend, TypedList.append]

@[simp]
lemma TypedList.append_nil_right :
    {x : TypedList β d c} → x ++ (TypedList.nil (β := β) c) = x := by
  intros x
  induction x
  all_goals simp [HAppend.hAppend, TypedList.append]
  aesop

@[simp]
lemma TypedList.cons_append {x : TypedList β d m} {y : TypedList β m c} {head : β h d} :
    (TypedList.cons head x) ++ y = TypedList.cons head (x ++ y) := by
  induction x
  all_goals simp [HAppend.hAppend, TypedList.append]

-- HEq nightmare
-- #check List.append_inj
-- @[simp, grind]
-- lemma TypedList.append_inj {d m c : α} {x₁ x₂ : TypedList β d m} {y₁ y₂ : TypedList β m c} :
--     x₁ ++ y₁ = x₂ ++ y₂ → x₁.length = x₂.length → x₁ = x₂ ∧ y₁ = y₂ := by
--   intros heq hlen
--   induction x₁
--   case nil obj =>
--     cases x₂
--     all_goals try simp at hlen; omega
--     easy
--   case cons ih =>
--     cases x₂
--     all_goals simp at hlen
--     simp only [TypedList.cons_append] at heq
--     simp at heq ⊢

--     refine ⟨⟨heq.left, heq.right.left, ?tail⟩ , ?y⟩


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
def TypedList.map (fobj : α → δ) (f : {d c : α} → (β d c) → (γ (fobj d) (fobj c))) : TypedList β d c → TypedList γ (fobj d) (fobj c)
  | .nil obj => .nil (fobj obj)
  | .cons head tail => .cons (f head) (tail.map fobj f)

@[simp]
lemma TypedList.map_append {x : TypedList β d m} {y : TypedList β m c} : (x ++ y).map f' f = (x.map f' f) ++ (y.map f' f) := by
  induction x
  all_goals easy

@[simp]
lemma TypedList.map_id {x : TypedList β d c} : x.map id id = x := by
  induction x
  all_goals easy

@[simp, grind]
def TypedList.inv (g_inv : {c d : α} → (β d c) → (β c d)) : TypedList β d c → TypedList β c d
  | .nil obj => .nil obj
  | .cons head tail => (tail.inv g_inv) ++ (TypedList.cons (g_inv head) (TypedList.nil d))

@[simp, grind]
lemma TypedList.inv_append {g_inv} {x : TypedList β d m} {y : TypedList β m c} :
    (x ++ y).inv g_inv = (y.inv g_inv) ++ (x.inv g_inv) := by
  induction x
  all_goals aesop

@[simp]
lemma TypedList.inv_inv {β : α → α → Type} {inv₁ inv₂ : {c d : α} → (β d c) → (β c d)} {x : TypedList β d c} :
    (x.inv inv₁).inv inv₂ = x.map id (inv₂ ∘ inv₁) := by
  induction x
  all_goals easy

abbrev BraidWord α := TypedList (BraidGenerator α)

@[simp]
def BraidWord.id (X : List α) : BraidWord α X X :=
  TypedList.nil X

@[simp]
def BraidWord.inv (w : BraidWord α d c) : BraidWord α c d :=
  TypedList.inv BraidGenerator.inv w

@[simp, grind]
lemma BraidWord.inv_append {α : Type} {d m c : List α} {x : BraidWord α d m} {y : BraidWord α m c} : BraidWord.inv (x ++ y) = (y.inv ++ x.inv) := by
  simp

def BraidWord.inv_inv {α : Type} {d c : List α} (w : BraidWord α d c) : w.inv.inv = w := by
  induction w
  all_goals easy

-- inherited HEq nightmare
-- def BraidWord.inv_inj {α : Type} {d c : List α} (w₁ w₂ : BraidWord α d c) : w₁.inv = w₂.inv ↔ w₁ = w₂ := by
--   constructor
--   case mpr => easy
--   case mp =>
--     intros h
--     induction w₁
--     case nil =>
--       simp at h
--       cases w₂
--       all_goals simp
--       apply congrArg TypedList.length at h
--       simp at h
--     case cons head tail ih =>
--       simp at h
--       cases w₂
--       · all_goals simp
--         apply congrArg TypedList.length at h
--         simp at h
--       case cons head₂ tail₂ =>
--         simp at h
--         unfold BraidWord at ih
--         specialize ih (tail₂)
--         sorry
--         sorry

  -- rw [← BraidWord.inv_inv w₁, ← BraidWord.inv_inv w₂]
  -- congr
  -- exact h

@[simp]
def BraidWord.forget (x : BraidWord α d c) : BraidWord Unit (d.map (fun _ => ())) (c.map (fun _ => ())) :=
  (TypedList.map (fun x => x.map (fun _ => ())) BraidGenerator.forget) x

@[simp]
lemma BraidWord.forget_append (x : BraidWord α d m) (y : BraidWord α m c) : BraidWord.forget (x ++ y) = BraidWord.forget x ++ BraidWord.forget y := by
  simp

@[grind]
inductive BraidEquiv : BraidWord α d c → BraidWord α d c → Prop where
  | refl (x : BraidWord α d c) : BraidEquiv x x
  | symm {x y : BraidWord α d c} : BraidEquiv x y → BraidEquiv y x
  | trans {x y z : BraidWord α d c} : BraidEquiv x y → BraidEquiv y z → BraidEquiv x z
  | ignore_head {h : BraidWord α d m} {x y : BraidWord α m c} : BraidEquiv x y → BraidEquiv (h ++ x) (h ++ y)
  | ignore_tail {x y : BraidWord α d m} {t : BraidWord α m c} : BraidEquiv x y → BraidEquiv (x ++ t) (y ++ t)
  -- | inv (myend : List α) {hmyend : myend = (l ++ [a, b] ++ r)} : s₁ ≠ s₂ → BraidEquiv
  --   (TypedList.cons ⟨l, s₁, a, b, r, by easy, by easy⟩ (TypedList.cons ⟨l, s₂, b, a, r, by easy, by easy⟩ (TypedList.nil myend)))
  --   (TypedList.nil myend)
  | inv (g : BraidGenerator α d c) : BraidEquiv
    (TypedList.cons g (TypedList.cons g.inv (TypedList.nil d)))
    (BraidWord.id d)
  | comm : BraidEquiv
    (TypedList.cons (BraidGenerator.make l s₁ w x (m ++ y :: z :: r))
      (TypedList.cons (BraidGenerator.make (l ++ x :: w :: m) s₂ y z r)
        (TypedList.nil _)))
    (TypedList.cons ⟨l ++ w :: x :: m, s₂, y, z, r, by easy, by easy⟩
      (TypedList.cons ⟨l, s₁, w, x, m ++ z :: y :: r, by easy, by easy⟩
        (TypedList.nil _)))
  | yb : BraidEquiv
    (TypedList.cons ⟨l, s, x, y, z :: r, by easy, by easy⟩
      (TypedList.cons ⟨l ++ [y], s, x, z, r, by easy, by easy⟩
        (TypedList.cons ⟨l, s, y, z, x :: r, by easy, by easy⟩
          (TypedList.nil (l ++ z :: y :: x :: r)))))
    (TypedList.cons ⟨l ++ [x], s, y, z, r, by easy, by easy⟩
      (TypedList.cons ⟨l, s, x, z, y :: r, by easy, by easy⟩
        (TypedList.cons ⟨l ++ [z], s, x, y, r, by easy, by easy⟩
          (TypedList.nil (l ++ z :: y :: x :: r)))))

instance (d c : List α) : Trans (BraidEquiv (α := α) (d := d) (c := c)) (BraidEquiv (α := α) (d := d) (c := c)) (BraidEquiv (α := α) (d := d) (c := c)) where
  trans := BraidEquiv.trans

instance (d c : List α) : Equivalence (BraidEquiv (α := α) (d := d) (c := c)) where
  refl := BraidEquiv.refl
  symm := BraidEquiv.symm
  trans := BraidEquiv.trans

@[simp, grind]
lemma BraidWord.inv_comp {α : Type} {d c : List α} (w : BraidWord α d c) : BraidEquiv (w.inv ++ w) (TypedList.nil c) := by
  induction w
  case nil obj =>
    simp [HAppend.hAppend]
    grind
  case cons d m c head tail ih =>
    calc BraidEquiv _ ((BraidWord.inv tail) ++ (TypedList.cons head.inv (TypedList.cons head (TypedList.nil m))) ++ tail) := by
          simp
          apply BraidEquiv.refl
         BraidEquiv _ ((BraidWord.inv tail) ++ (TypedList.nil m) ++ tail) := by
          apply BraidEquiv.ignore_tail
          apply BraidEquiv.ignore_head
          cases head
          simp
          grind
         BraidEquiv _ (TypedList.nil c) := by
          rw [TypedList.append_nil_right]
          exact ih

@[simp, grind]
lemma BraidWord.comp_inv {α : Type} {d c : List α} (w : BraidWord α d c) : BraidEquiv (w ++ w.inv) (TypedList.nil d) := by
  induction w
  case nil obj =>
    simp [HAppend.hAppend]
    grind
  case cons d m c head tail ih =>
    calc BraidEquiv _ ((TypedList.cons head (TypedList.nil m)) ++ ((tail ++ BraidWord.inv tail) ++ TypedList.cons head.inv (TypedList.nil d))) := by
          simp
          apply BraidEquiv.refl
         BraidEquiv _ _ := BraidEquiv.ignore_head <| BraidEquiv.ignore_tail ih
         BraidEquiv _ (TypedList.nil d) := by
          -- cases head
          -- simp
          apply BraidEquiv.inv
          -- grind only [BraidEquiv.inv]

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

@[simp]
def Braid.id (X : List α) : Braid α X X := ⟦BraidWord.id X⟧

@[simp]
def Braid.forget {d c : List α} (f : Braid α d c) : Braid Unit (d.map (fun _ => ())) (c.map (fun _ => ())) :=
  Quotient.liftOn f
    (fun x => ⟦BraidWord.forget x⟧)
    (by
      intros a b hab
      clear f
      apply Quotient.sound ?_
      induction hab
      -- all_goals try simp
      -- all_goals try (first | grind | apply BraidEquiv.symm; grind)
      case refl x => exact BraidEquiv.refl (BraidWord.forget x)
      case symm ih =>
        exact BraidEquiv.symm ih
      case trans ih₁ ih₂ =>
        exact BraidEquiv.trans ih₁ ih₂
      case ignore_head ih =>
        simp
        exact BraidEquiv.ignore_head ih
      case ignore_tail ih =>
        simp
        exact BraidEquiv.ignore_tail ih
      case inv d c g =>
        simp
        apply BraidEquiv.inv
        -- have hrw : List.map (fun _ => ()) (l ++ a :: b :: r) = List.replicate l.length () ++ () :: () :: List.replicate r.length () := by
        --   simp
        -- have x := BraidEquiv.inv (s₁ := s₁) (s₂ := s₂) (l := List.replicate l.length ()) (a := ()) (b := ()) (r := List.replicate r.length ()) hs
        -- simp at x
        -- -- rw [hrw]
        -- -- rw [← hrw] at x
        -- -- grind
        -- exact x
      case comm =>
        simp
        apply BraidEquiv.comm
      case yb =>
        simp
        apply BraidEquiv.yb)

@[simp, grind]
lemma Braid.inv_inv (f : Braid α X Y) : f.inv.inv = f := by
  qind f
  apply Quotient.sound
  rw [BraidWord.inv_inv]
  easy

@[simp, grind]
lemma Braid.inv_comp {X Y : List α} (f : Braid α X Y) : Braid.comp (Braid.inv f) f = ⟦TypedList.nil Y⟧ := by
  qind f
  simp
  apply Quotient.sound
  apply BraidWord.inv_comp

@[simp, grind]
lemma Braid.comp_inv {X Y : List α} (f : Braid α X Y) : Braid.comp f (Braid.inv f) = ⟦TypedList.nil X⟧ := by
  qind f
  simp
  apply Quotient.sound
  apply BraidWord.comp_inv

def BraidGroupoid : CategoryTheory.Groupoid (List α) where
  Hom := Braid α
  id := Braid.id
  comp := Braid.comp
  inv := Braid.inv
  id_comp x := by qind x; easy
  comp_id x := by qind x; easy
  assoc x y z := by qind x; qind y; qind z; easy
  inv_comp x := by
    qind x
    apply Quotient.sound
    apply BraidWord.inv_comp
  comp_inv x := by
    qind x
    apply Quotient.sound
    apply BraidWord.comp_inv
