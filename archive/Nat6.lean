import Mathlib
import Mathlib.CategoryTheory.Category.Basic

-- fuck it. Types at parameter/index level.

-- what if we don't have types at the parameter/index level
-- having BraidWord be always typed caused problems in Nat4
-- Nat's idea: back to explicit composition. No more nils; instead,
-- identities.

-- TODO simp before grind; assumption
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

inductive CatWord {β : Type} (α : β → β → Type) : β → β → Type where
  | id (X : β) : CatWord α X X
  | gen {X Y : β} (head : α X Y) : CatWord α X Y
  | comp {X Y Z : β} (f : CatWord α X Y) (g : CatWord α Y Z) : CatWord α X Z

inductive CatWordEquiv {β : Type} {α : β → β → Type} (quiv : {X Y : β} → CatWord α X Y → CatWord α X Y → Prop) : (CatWord α X Y) → (CatWord α X Y) → Prop where
  | refl (w : CatWord α X Y) : CatWordEquiv quiv w w
  | symm {w₁ w₂ : CatWord α X Y} : CatWordEquiv quiv w₁ w₂ → CatWordEquiv quiv w₂ w₁
  | trans {w₁ w₂ w₃ : CatWord α X Y} : CatWordEquiv quiv w₁ w₂ → CatWordEquiv quiv w₂ w₃ → CatWordEquiv quiv w₁ w₃
  | id_comp {w : CatWord α X Y} : CatWordEquiv quiv ((CatWord.id X).comp w) w
  | comp_id {w : CatWord α X Y} : CatWordEquiv quiv (w.comp (CatWord.id Y)) w
  | assoc {w₁ : CatWord α W X} {w₂ : CatWord α X Y} {w₃ : CatWord α Y Z} : CatWordEquiv quiv ((w₁.comp w₂).comp w₃) (w₁.comp (w₂.comp w₃))
  | over_comp {a₁ a₂ : CatWord α X Y} {b₁ b₂ : CatWord α Y Z} : CatWordEquiv quiv a₁ a₂ → CatWordEquiv quiv b₁ b₂ → CatWordEquiv quiv (a₁.comp b₁) (a₂.comp b₂)
  | quiv {a b : CatWord α X Y} : quiv a b → CatWordEquiv quiv a b

def setoidWord (α : β → β → Type) (quiv : {X Y : β} → CatWord α X Y → CatWord α X Y → Prop) (X Y : β) : Setoid (CatWord α X Y) :=
  ⟨CatWordEquiv quiv, ⟨CatWordEquiv.refl, CatWordEquiv.symm, CatWordEquiv.trans⟩⟩

def CatMorphism (α : β → β → Type) (quiv : {X Y : β} → CatWord α X Y → CatWord α X Y → Prop) (X Y : β) := Quotient <| setoidWord α quiv X Y

def CatMorphism.comp (quiv : {X Y : β} → CatWord α X Y → CatWord α X Y → Prop) (w₁ : CatMorphism α quiv X Y) (w₂ : CatMorphism α quiv Y Z) : CatMorphism α quiv X Z :=
  Quotient.liftOn₂ w₁ w₂ (fun w₁ w₂ => ⟦w₁.comp w₂⟧) <| by
    intros a₁ b₁ a₂ b₂ ha hb
    simp
    apply Quotient.sound
    exact CatWordEquiv.over_comp ha hb

def CatMorphism.id (quiv : {X Y : β} → CatWord α X Y → CatWord α X Y → Prop) (X : β) : CatMorphism α quiv X X := ⟦CatWord.id X⟧

def CatMorphism.gen (quiv : {X Y : β} → CatWord α X Y → CatWord α X Y → Prop) {X Y : β} (head : α X Y) : CatMorphism α quiv X Y := ⟦CatWord.gen head⟧

open CategoryTheory

def MyCategory (α : β → β → Type) (quiv : {X Y : β} → CatWord α X Y → CatWord α X Y → Prop) : Category β where
  Hom X Y := CatMorphism α quiv X Y
  id X := CatMorphism.id quiv X
  comp f g := CatMorphism.comp quiv f g
  id_comp f := by
    qind f
    simp [CatMorphism.comp, CatMorphism.id]
    apply Quotient.sound
    exact CatWordEquiv.id_comp
  comp_id f := by
    qind f
    simp [CatMorphism.comp, CatMorphism.id]
    apply Quotient.sound
    exact CatWordEquiv.comp_id
  assoc f g h := by
    qind f
    qind g
    qind h
    simp [CatMorphism.comp]
    apply Quotient.sound
    exact CatWordEquiv.assoc

-- instantiate!
structure BraidGenerator (α : Type) (dom cod : List α) where
  left : List α
  sign : Bool -- true is left over right
  a : α
  b : α
  right : List α
  hdom : dom = left ++ a :: b :: right
  hcod : cod = left ++ b :: a :: right

@[simp]
def BraidGenerator.inv (g : BraidGenerator α X Y) : BraidGenerator α Y X:=
  ⟨g.left, !g.sign, g.b, g.a, g.right, by simp [g.hcod], by simp [g.hdom]⟩

@[simp]
lemma BraidGenerator.inv_inv (g : BraidGenerator α X Y) : g.inv.inv = g := by easy

macro "simprfl" : tactic => `(tactic| first | (simp; done) | ((try simp); rfl))

inductive BraidEquiv : CatWord (BraidGenerator α) X Y → CatWord (BraidGenerator α) X Y → Prop where
  | inv {g : BraidGenerator α X Y} :
      BraidEquiv ((CatWord.gen g).comp (CatWord.gen g.inv)) (CatWord.id X)
  | comm {left middle right : List α} {w x y z : α} : BraidEquiv
      ((CatWord.gen ⟨left, s₁, w, x, middle ++ [y, z] ++ right, by simprfl, by simprfl⟩).comp
        (CatWord.gen ⟨left ++ [x, w] ++ middle, s₂, y, z, right, by simprfl, by simprfl⟩))
      ((CatWord.gen ⟨left ++ [w, x] ++ middle, s₂, y, z, right, by simprfl, by simprfl⟩).comp
        (CatWord.gen ⟨left, s₂, w, x, middle ++ [z, y] ++ right, by simprfl, by simprfl⟩))
  | yangBaxter {left right : List α} {a b c : α} : BraidEquiv
      (((CatWord.gen ⟨left, s, a, b, c :: right, by simprfl, by simprfl⟩).comp
        (CatWord.gen ⟨left ++ [b], s, a, c, right, by simprfl, by simprfl⟩)).comp
        (CatWord.gen ⟨left, s, b, c, a :: right, by simprfl, by simprfl⟩))
      (((CatWord.gen ⟨left ++ [a], s, b, c, right, by simprfl, by simprfl⟩).comp
        (CatWord.gen ⟨left, s, a, c, b :: right, by simprfl, by simprfl⟩)).comp
        (CatWord.gen ⟨left ++ [c], s, a, b, right, by simprfl, by simprfl⟩))

def BraidGroupoid (α : Type) := MyCategory (BraidGenerator α) BraidEquiv

#check (BraidGroupoid ℕ).Hom

@[simp]
def List.forget {α : Type} (l : List α) : List Unit :=
  l.map (fun _ => ())

@[simp]
def BraidGenerator.forget (g : BraidGenerator α X Y) : BraidGenerator Unit X.forget Y.forget :=
  ⟨g.left.map (fun _ => ()), g.sign, (), (), g.right.map (fun _ => ()), by simp [g.hdom], by simp [g.hcod]⟩

@[simp]
lemma PreTypedList.inv_append [I : Isomorphism β α] {x y : PreTypedList β α} (h : I.list.agree x y) :
    (x ++ y).inv = y.inv ++ x.inv := by
  induction x
  all_goals simp [PreTypedList.inv]
  case nil =>
    calc y.inv = _ := by
          symm
          exact PreTypedList.append_nil
         _ = _ := by easy
  case cons head tail ih =>
    rw [ih]
    all_goals easy

@[simp]
lemma PreTypedList.inv_inv [I : Isomorphism β α] {x : PreTypedList β α} (h : x.Typed) :
    (x.inv).inv = x := by
  induction x
  all_goals easy

@[simp]
lemma PreTypedList.typed_append [M : Morphism β α] {x y : PreTypedList β α} (h : M.list.agree x y):
    (x ++ y).Typed ↔ (x.Typed ∧ y.Typed) := by
  induction x
  case nil obj =>
    easy
  case cons ih =>
    specialize ih (by easy)
    easy

@[simp]
lemma PreTypedList.inv_typed_typed [Isomorphism β α] {x : PreTypedList β α} :
    x.Typed → x.inv.Typed := by
  intros h
  induction x
  case nil => easy
  case cons head tail ih =>
    simp
    rw [PreTypedList.typed_append (by easy)]
    easy

abbrev TypedList (β : Type) (α : Type) [Morphism β α] := {x : PreTypedList β α // x.Typed}

instance Morphism.typedList [M : Morphism β α] : Morphism (TypedList β α) α where
  dom x := M.list.dom x.val
  cod x := M.list.cod x.val

instance Isomorphism.list [I : Isomorphism β α] : Isomorphism (TypedList β α) α where
  inv x := ⟨x.val.inv, by easy⟩
  inv_dom x := by
    simp only [Morphism.dom, Morphism.cod]
    rw [PreTypedList.inv_dom (by easy)]
  inv_cod x := by
    simp only [Morphism.dom, Morphism.cod]
    rw [PreTypedList.inv_cod]

@[simp]
def PreTypedList.length : PreTypedList β α → Nat
  | .nil _ => 0
  | .cons _ tail => 1 + tail.length

@[simp, grind =]
lemma PreTypedList.length_append (x : PreTypedList β α) (y : PreTypedList β α) [M : Morphism β α] (heq : M.list.agree x y) :
    (x.append y).length = x.length + y.length := by
  induction x
  all_goals simp [PreTypedList.append] at *
  case cons ih =>
    specialize ih (by easy)
    omega

@[simp]
lemma TypedList.append_inj {d m c : α} {x₁ x₂ : PreTypedList β α} {y₁ y₂ : PreTypedList β α} {M : Morphism β α} (h₁ : M.list.agree x₁ y₁) (h₂ : M.list.agree x₂ y₂) :
    x₁ ++ y₁ = x₂ ++ y₂ → x₁.length = x₂.length → x₁ = x₂ ∧ y₁ = y₂ := by
  intros heq hlen
  induction x₁ generalizing x₂ y₁ y₂
  case nil =>
    cases x₂
    case nil => easy
    case cons =>
      simp only [PreTypedList.length] at hlen
      omega
  case cons ih =>
    cases x₂
    case nil => simp only [PreTypedList.length, Nat.add_eq_zero_iff, one_ne_zero, false_and] at hlen
    case cons =>
      simp only [PreTypedList.cons_append, PreTypedList.cons.injEq] at heq ⊢
      specialize ih (by easy) (by easy) heq.right (by easy)
      easy

-- @[simp]
-- def PreTypedList.extendLeft {β : α → α → Type} [Append α] [Extend β] (a : α) : PreTypedList β d c → PreTypedList β (a ++ d) (a ++ c)
--   | .nil obj => .nil (a ++ obj)
--   | .cons head tail => .cons (Extend.extendLeft a head) (tail.extendLeft a)

-- @[simp]
-- def PreTypedList.extendRight {β : α → α → Type} [Append α] [Extend β] (a : α) : PreTypedList β d c → PreTypedList β (d ++ a) (c ++ a)
--   | .nil obj => .nil (obj ++ a)
--   | .cons head tail => .cons (Extend.extendRight a head) (tail.extendRight a)

-- @[simp]
-- def PreTypedList.prod {α : Type} {β : α → α → Type} [Append α] [Extend β] {d₁ c₁ d₂ c₂ : α} (left : PreTypedList β d₁ c₁) (right : PreTypedList β d₂ c₂) : PreTypedList β (d₁ ++ d₂) (c₁ ++ c₂) :=
--   (left.extendRight d₂) ++ (right.extendLeft c₁)

-- use ⊗ for prod
-- notation x " ⊗ " y => PreTypedList.prod x y

@[simp, grind]
def PreTypedList.map (fobj : α → δ) (f : β → γ) : PreTypedList β α → PreTypedList γ δ
  | .nil obj => .nil (fobj obj)
  | .cons head tail => .cons (f head) (tail.map fobj f)

@[simp]
lemma PreTypedList.dom_map {x : PreTypedList β α} {f' : α → δ} {f : β → γ} [Morphism β α] [Morphism γ δ]
    (hdom : ∀ b, Morphism.dom (f b) = f' (Morphism.dom b)) : (x.map f' f).dom = f' (x.dom) := by
  cases x
  case nil => easy
  case cons =>
    simp only [PreTypedList.map, PreTypedList.dom]
    rw [hdom]

@[simp]
lemma PreTypedList.cod_map {x : PreTypedList β α} {f' : α → δ} {f : β → γ} [Morphism β α] [Morphism γ δ]
    : (x.map f' f).cod = f' (x.cod) := by
  induction x
  case nil => easy
  case cons ih =>
    simp only [PreTypedList.map, PreTypedList.cod]
    apply ih

@[simp]
lemma PreTypedList.map_typed {x : PreTypedList β α} {f' : α → δ} {f : β → γ} [Morphism β α] [Morphism γ δ] (h : x.Typed)
    (hdom : ∀ b, Morphism.dom (f b) = f' (Morphism.dom b)) (hcod : ∀ b, Morphism.cod (f b) = f' (Morphism.cod b)) :
    (x.map f' f).Typed := by
  induction x
  case nil => easy
  case cons ih =>
    simp only [PreTypedList.map, PreTypedList.Typed, hcod] at h ⊢
    rw [PreTypedList.dom_map (by easy)]
    rw [h.left]
    exact ⟨rfl, ih (by easy)⟩

@[simp]
lemma PreTypedList.map_append {x y : PreTypedList β α} :
    (x ++ y).map f' f = (x.map f' f) ++ (y.map f' f) := by
  induction x
  case nil => easy
  case cons ih =>
    simp only [PreTypedList.cons_append, PreTypedList.map]
    rw [ih]

@[simp]
lemma PreTypedList.map_id {x : PreTypedList β α} : x.map id id = x := by
  induction x
  all_goals easy

@[simp]
lemma PreTypedList.map_agree {x y : PreTypedList β α} {f' : α → δ} {f : β → γ} [Morphism β α] [Morphism γ δ]
    (hdom : ∀ b, Morphism.dom (f b) = f' (Morphism.dom b)) :
    Morphism.list.agree x y → Morphism.list.agree (x.map f' f) (y.map f' f) := by
  simp only [Morphism.agree, Morphism.cod, Morphism.dom]
  rw [PreTypedList.cod_map]
  rw [PreTypedList.dom_map hdom]
  intros h; rw [h]

abbrev BraidWord α := { w : PreTypedList (BraidGenerator α) (List α) // w.Typed }

-- def BraidWord.mk (w : PreTypedList (BraidGenerator α) (List α)) (h : w.Typed) : BraidWord α :=
--   ⟨_, h⟩

-- @[simp]
-- def BraidWord.Typed (x : BraidWord α) : Prop :=
--   PreTypedList.Typed x

@[simp]
def BraidWord.id (X : List α) : BraidWord α :=
  ⟨PreTypedList.nil X, by easy⟩

instance : Coe (BraidWord α) (PreTypedList (BraidGenerator α) (List α)) where
  coe w := w.val

@[simp]
def BraidWord.inv (w : BraidWord α) : BraidWord α :=
  ⟨PreTypedList.inv w, by
    apply PreTypedList.inv_typed_typed
    exact w.prop⟩

instance : Isomorphism (BraidWord α) (List α) where
  dom w := w.val.dom
  cod w := w.val.cod
  inv w := w.inv
  inv_dom x := by
    apply PreTypedList.inv_dom
    exact x.prop
  inv_cod x := PreTypedList.inv_cod
  inv_inv x := by
    apply Subtype.ext
    apply PreTypedList.inv_inv
    exact x.prop

def BraidWord.append (x y : BraidWord α) (h : Morphism.agree x y) : BraidWord α :=
  ⟨x.val ++ y.val, by
    rw [PreTypedList.typed_append h]
    exact ⟨x.prop, y.prop⟩⟩

@[simp, grind]
lemma BraidWord.inv_append {x y : BraidWord α} {h : Morphism.agree x y} : BraidWord.inv (x.append y h) = (y.inv.append x.inv (Isomorphism.agree_inv h)) := by
  apply Subtype.ext
  apply PreTypedList.inv_append
  exact h

def BraidWord.inv_inv {w : BraidWord α} : w.inv.inv = w := by
  apply Subtype.ext
  apply PreTypedList.inv_inv
  exact w.prop

-- def BraidWord.inv_inj {α : Type} (w₁ w₂ : BraidWord α) : w₁.inv = w₂.inv ↔ w₁ = w₂ := by
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
def BraidWord.forget (x : BraidWord α) : BraidWord Unit :=
  ⟨(PreTypedList.map (fun (x : List α) => x.map (fun _ => ())) BraidGenerator.forget) x.val, by
    apply PreTypedList.map_typed x.prop
    all_goals easy⟩

@[simp]
lemma BraidWord.forget_append {x y : BraidWord α} {h : Morphism.agree x y} :
    (x.append y h).forget = (x.forget.append y.forget (PreTypedList.map_agree BraidGenerator.forget_dom h)) := by
  apply Subtype.ext
  simp only [BraidWord.forget, BraidWord.append]
  apply PreTypedList.map_append

@[simp]
def BraidEquiv.inv1 (g : BraidGenerator α) : BraidWord α :=
  ⟨(PreTypedList.cons g (PreTypedList.cons g.inv (PreTypedList.nil g.dom))), by easy⟩

@[simp]
def BraidEquiv.inv2 (_g : BraidGenerator α) : BraidWord α :=
  ⟨(PreTypedList.nil _g.dom), by easy⟩

@[simp]
lemma BraidEquiv.inv_dom : Morphism.dom (BraidEquiv.inv1 g) = Morphism.dom (BraidEquiv.inv2 g) := by
  easy

@[simp]
lemma BraidEquiv.inv_cod : Morphism.cod (BraidEquiv.inv1 g) = Morphism.cod (BraidEquiv.inv2 g) := by
  simp only [Morphism.cod, BraidEquiv.inv1, BraidEquiv.inv2, PreTypedList.cod]

@[simp]
def BraidEquiv.comm1 (s₁ s₂ : Bool) (l : List α) (w x : α) (m : List α) (y z : α) (r : List α) : BraidWord α :=
  ⟨(PreTypedList.cons ⟨l, s₁, w, x, m ++ y :: z :: r⟩
    (PreTypedList.cons ⟨l ++ x :: w :: m, s₂, y, z, r⟩
      (PreTypedList.nil _))), by easy⟩

@[simp]
def BraidEquiv.comm2 (s₁ s₂ : Bool) (l : List α) (w x : α) (m : List α) (y z : α) (r : List α) : BraidWord α :=
  ⟨(PreTypedList.cons ⟨l ++ w :: x :: m, s₂, y, z, r⟩
    (PreTypedList.cons ⟨l, s₁, w, x, m ++ z :: y :: r⟩
      (PreTypedList.nil _))), by easy⟩

@[simp]
lemma BraidEquiv.comm_dom : Morphism.dom (BraidEquiv.comm1 s₁ s₂ l w x m y z r)= Morphism.dom (BraidEquiv.comm2 s₁ s₂ l w x m y z r) := by
  simp only [Morphism.dom, BraidEquiv.comm1, BraidEquiv.comm2, PreTypedList.dom, BraidGenerator.dom]
  easy

@[simp]
lemma BraidEquiv.comm_cod : Morphism.cod (BraidEquiv.comm1 s₁ s₂ l w x m y z r) = Morphism.cod (BraidEquiv.comm2 s₁ s₂ l w x m y z r) := by
  simp only [Morphism.cod, BraidEquiv.comm1, BraidEquiv.comm2, PreTypedList.cod]

@[simp]
def BraidEquiv.yb1 (s : Bool) (l : List α) (x y z : α) (r : List α) : BraidWord α :=
  ⟨(PreTypedList.cons ⟨l, s, x, y, z :: r⟩
    (PreTypedList.cons ⟨l ++ [y], s, x, z, r⟩
      (PreTypedList.cons ⟨l, s, y, z, x :: r⟩
        (PreTypedList.nil _)))), by easy⟩

@[simp]
def BraidEquiv.yb2 (s : Bool) (l : List α) (x y z : α) (r : List α) : BraidWord α :=
  ⟨(PreTypedList.cons ⟨l ++ [x], s, y, z, r⟩
    (PreTypedList.cons ⟨l, s, x, z, y :: r⟩
      (PreTypedList.cons ⟨l ++ [z], s, x, y, r⟩
        (PreTypedList.nil _)))), by easy⟩

@[simp]
lemma BraidEquiv.yb_dom : Morphism.dom (BraidEquiv.yb1 s l x y z r) = Morphism.dom (BraidEquiv.yb2 s l x y z r) := by
  simp only [Morphism.dom, BraidEquiv.yb1, BraidEquiv.yb2, PreTypedList.dom, BraidGenerator.dom]
  easy

@[simp]
lemma BraidEquiv.yb_cod : Morphism.cod (BraidEquiv.yb1 s l x y z r) = Morphism.cod (BraidEquiv.yb2 s l x y z r) := by
  simp only [Morphism.cod, BraidEquiv.yb1, BraidEquiv.yb2, PreTypedList.cod]

@[simp, grind]
lemma List.cons_replicate : a :: (List.replicate n a) = List.replicate (n + 1) a := by
  symm
  apply List.replicate_succ

-- comm1.forget is another comm1
lemma BraidEquiv.forget_comm1 (s₁ s₂ : Bool) (l : List α) (w x : α) (m : List α) (y z : α) (r : List α) :
    BraidWord.forget (BraidEquiv.comm1 s₁ s₂ l w x m y z r) =
    (BraidEquiv.comm1 s₁ s₂ (l.map (fun _ => ())) () () (m.map (fun _ => ())) () () (r.map (fun _ => ()))) := by
  simp

@[grind]
inductive BraidEquiv : BraidWord α → BraidWord α → Prop where
  | refl (x : BraidWord α) : BraidEquiv x x
  | symm {x y : BraidWord α} : BraidEquiv x y → BraidEquiv y x
  | trans {x y z : BraidWord α} : BraidEquiv x y → BraidEquiv y z → BraidEquiv x z
  | ignore_head {head x y : BraidWord α} {h₁ : Morphism.agree head x} {h₂ : Morphism.agree head y} : BraidEquiv x y → BraidEquiv (head.append x h₁) (head.append y h₂)
  | ignore_tail {x y tail : BraidWord α} {h₁ : Morphism.agree x tail} {h₂ : Morphism.agree y tail} : BraidEquiv x y → BraidEquiv (x.append tail h₁) (y.append tail h₂)
  -- | ignore_head {x y : BraidWord α} : BraidEquiv x y → BraidEquiv (PreTypedList.cons g x) (PreTypedList.cons g y)
  -- | ignore_tail {x y : BraidWord α d m} {t : BraidWord α m c} : BraidEquiv x y → BraidEquiv (x ++ t) (y ++ t)
  -- | inv (g : BraidGenerator α d c) : x = (TypedList.cons g (TypedList.cons g.inv (TypedList.nil d))) → BraidEquiv x (BraidWord.id d)
  -- | comm {a b : BraidWord α _ _} : a = (BraidEquiv.comm1 s₁ s₂ l w x m y z r) → b = (BraidEquiv.comm2 s₁ s₂ l w x m y z r) → BraidEquiv a b
  -- | yb {a b : BraidWord α _ _} : a = (BraidEquiv.yb1 s l x y z r) → b = (BraidEquiv.yb2 s l x y z r) → BraidEquiv a b
  | inv (g : BraidGenerator α) : BraidEquiv (BraidEquiv.inv1 g) (BraidEquiv.inv2 g)
  | comm : BraidEquiv (BraidEquiv.comm1 s₁ s₂ l w x m y z r) (BraidEquiv.comm2 s₁ s₂ l w x m y z r)
  | yb : BraidEquiv (BraidEquiv.yb1 s l x y z r) (BraidEquiv.yb2 s l x y z r)

instance : Trans (BraidEquiv (α := α)) (BraidEquiv (α := α)) (BraidEquiv (α := α)) where
  trans := BraidEquiv.trans

instance : Equivalence (BraidEquiv (α := α)) where
  refl := BraidEquiv.refl
  symm := BraidEquiv.symm
  trans := BraidEquiv.trans

@[refl]
lemma BraidEquiv.refl' (x : BraidWord α) : BraidEquiv x x := by
  apply BraidEquiv.refl

@[simp, grind]
lemma BraidWord.inv_comp {α : Type} (w : BraidWord α) : BraidEquiv (w.inv.append w (Isomorphism.inv_agree)) (BraidWord.id (Morphism.cod w)) := by
  rcases w with ⟨w, hw⟩
  induction w
  case nil obj => rfl
  case cons head tail ih =>
    simp only [BraidWord.inv, PreTypedList.inv, BraidWord.append]
    have hrw : PreTypedList.cons head tail = (PreTypedList.cons head (PreTypedList.nil head.cod)) ++ tail := by sorry
    rw [hrw]
    -- sorry
    calc BraidEquiv _ ((BraidWord.inv tail) ++ (PreTypedList.cons head.inv (PreTypedList.cons head (PreTypedList.nil m))) ++ tail) := by
          simp
          apply BraidEquiv.refl
         BraidEquiv _ ((BraidWord.inv tail) ++ (PreTypedList.nil m) ++ tail) := by
          apply BraidEquiv.ignore_tail
          apply BraidEquiv.ignore_head
          apply BraidEquiv.symm
          calc BraidEquiv (PreTypedList.nil m) _ := by
                apply BraidEquiv.symm
                exact BraidEquiv.inv head.inv
               BraidEquiv _ _ := by
                simp
                apply BraidEquiv.refl
         BraidEquiv _ (PreTypedList.nil c) := by
          rw [PreTypedList.append_nil_right]
          exact ih

@[simp, grind]
lemma BraidWord.comp_inv {α : Type} (w : BraidWord α) : BraidEquiv (w.append w.inv (Isomorphism.inv_agree)) (BraidWord.id (Morphism.dom w)) := by
  induction w
  case nil obj =>
    simp [HAppend.hAppend]
    grind
  case cons d m c head tail ih =>
    calc BraidEquiv _ ((PreTypedList.cons head (PreTypedList.nil m)) ++ ((tail ++ BraidWord.inv tail) ++ PreTypedList.cons head.inv (PreTypedList.nil d))) := by
          simp
          apply BraidEquiv.refl
         BraidEquiv _ _ := BraidEquiv.ignore_head <| BraidEquiv.ignore_tail ih
         BraidEquiv _ (PreTypedList.nil d) := by
          -- cases head
          -- simp
          apply BraidEquiv.inv head
          simp
          -- grind only [BraidEquiv.inv]

abbrev TypedBraidWord α := { w : BraidWord α // BraidWord.Typed w }

inductive TypedBraidEquiv : TypedBraidWord α → TypedBraidWord α → Prop where
  | refl (a : TypedBraidWord α) : TypedBraidEquiv a a
  | symm {a b : TypedBraidWord α} : TypedBraidEquiv a b → TypedBraidEquiv b a
  | trans {a b c : TypedBraidWord α} : TypedBraidEquiv a b → TypedBraidEquiv b c → TypedBraidEquiv a c
  | ofBraidEquiv (a b : TypedBraidWord α) (h : BraidEquiv a.val b.val) : TypedBraidEquiv a b

instance : Trans (TypedBraidEquiv (α := α)) (TypedBraidEquiv (α := α)) (TypedBraidEquiv (α := α)) where
  trans := TypedBraidEquiv.trans

def TypedBraidEquiv.Equiv : Equivalence (TypedBraidEquiv (α := α)) := {
  refl := TypedBraidEquiv.refl
  symm := TypedBraidEquiv.symm
  trans := TypedBraidEquiv.trans
}

@[simp, grind]
def setoidBraid (α) : Setoid (TypedBraidWord α) :=
  ⟨TypedBraidEquiv, TypedBraidEquiv.Equiv⟩

def Braid (α) := Quotient (setoidBraid α)

def Braid.dom (x : Braid α) : List α :=
  Quotient.liftOn x (fun w => PreTypedList.dom w.val) (by
    intros a b hab
    induction hab
    case ofBraidEquiv a b hab =>
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      simp only
      simp at hab
      induction hab
      all_goals easy
    all_goals try easy
  )

def Braid.cod (x : Braid α) : List α :=
  Quotient.liftOn x (fun w => PreTypedList.cod w.val) (by
    intros a b hab
    induction hab
    case ofBraidEquiv a b hab =>
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      simp only
      simp at hab
      induction hab
      all_goals easy
    all_goals easy
  )

instance : Morphism (Braid α) (List α) where
  dom := Braid.dom
  cod := Braid.cod

@[simp]
def Braid.comp {X Y Z : List α} (f : Braid α) (g : Braid α) : Braid α :=
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
      case inv x g hx =>
        subst x
        simp
        apply BraidEquiv.inv g
        simp
      case comm =>
        simp
        -- apply BraidEquiv.symm
        apply BraidEquiv.comm

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
      case comm s₁ s₂ l w x m y z r =>
        simp
        ▹
        #check Eq.rec
        #check Eq.ndrec
        -- have h :
        --   List.map (fun _ => ())
        --     (l ++ x :: w :: (m ++ z :: y :: r)) =
        --     (List.map (fun _ => ()) l) ++ () :: () ::
        --     (List.map (fun _ => ()) m) ++ () :: () ::
        --     (List.map (fun _ => ()) r) := by
        --   simp [List.map_append, List.map_cons]
        -- simp [List.map_append, List.map_cons, List.map_const]
        #check List.map_const
        calc BraidEquiv _ _ := by
              apply BraidEquiv.refl
             BraidEquiv _ _ := by
              apply BraidEquiv.comm (s₁ := s₁) (s₂ := s₂) (l := List.replicate l.length ()) (w := ()) (x := ()) (m := List.replicate m.length ()) (y := ()) (z := ()) (r := List.replicate r.length ())
             BraidEquiv _ _ := by
              apply BraidEquiv.refl

        -- simp
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
lemma Braid.inv_comp {X Y : List α} (f : Braid α X Y) : Braid.comp (Braid.inv f) f = ⟦PreTypedList.nil Y⟧ := by
  qind f
  simp
  apply Quotient.sound
  apply BraidWord.inv_comp

@[simp, grind]
lemma Braid.comp_inv {X Y : List α} (f : Braid α X Y) : Braid.comp f (Braid.inv f) = ⟦PreTypedList.nil X⟧ := by
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

-- -/
-- -/
-- -/
-- -/
