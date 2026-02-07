-- import Mathlib.CategoryTheory.Category.Basic
import Mathlib

-- open CategoryTheory

inductive Dir where
| left : Dir
| right : Dir
deriving Repr, DecidableEq

inductive Bed where
| front : Bed
| back : Bed
deriving Repr, DecidableEq

@[grind]
inductive BoxInfo where
| tuck : Dir → BoxInfo
| split : (carriers : ℕ+) → (loops : ℕ+) → Dir → Bed → BoxInfo
deriving Repr, DecidableEq
-- no drop: that's been laddered out already. Let's just ignore that the drops need to
-- be glued on to the splits for now; TODO don't ignore that

@[simp, grind =]
def BoxInfo.dom : BoxInfo → ℕ
  | tuck _ => 1
  | split c l _ _ => c + l

@[simp, grind =]
def BoxInfo.cod : BoxInfo → ℕ
  | tuck _ => 2
  | split c l _ _ => c + 2 * l

-- A stitch with a record of the identity strands on its left/right
-- TODO: maybe make two layers -- one for two+ outs, one for one out
structure Layer (dom cod : ℕ) where
  left : ℕ
  box : BoxInfo
  right : ℕ
  hdom : dom = left + box.dom + right := by grind
  hcod :
  cod = left + box.cod + right := by grind

-- @[simp, grind =]
-- def Layer.dom (l : Layer) : ℕ :=
--   l.left + l.box.dom + l.right

-- @[simp, grind =]
-- def Layer.cod (l : Layer) : ℕ :=
--   l.left + l.box.cod + l.right

-- a single braid generator
-- inductive BraidGenerator (n : ℕ) where
  -- | id : BraidGenerator n
  -- | σ : Bool → Fin (n - 1) → BraidGenerator n

def ZFin (n : ℤ) := { i : ℕ // i < n }

instance : DecidableEq (ZFin n) := fun a b ↦
  if h : a.val = b.val then
    .isTrue <| Subtype.ext h
  else
    .isFalse <| by aesop

instance : LT (ZFin n) where
  lt := (·.val < ·.val)

@[grind]
def ZFin.succ : ZFin n → ZFin (n + 1)
  | ⟨i, h⟩ => ⟨i + 1, by omega⟩

@[grind]
lemma ZFin.succ_val : ∀ z : ZFin n, z.succ.val = z.val + 1 := by
  unfold ZFin.succ
  aesop

@[grind]
def ZFin.castSucc : ZFin n → ZFin (n + 1)
  | ⟨i, h⟩ => ⟨i, by omega⟩

@[grind]
lemma ZFin.castSucc_val : ∀ z : ZFin n, z.castSucc.val = z.val := by
  unfold ZFin.castSucc
  aesop

@[grind]
def ZFin.cast {a b : ℤ} (h : a = b := by omega) : ZFin a → ZFin b
  | ⟨i, h⟩ => ⟨i, by omega⟩

@[grind, simp]
lemma ZFin.cast_val : ∀ z : ZFin n, (z.cast h).val = z.val := by
  unfold ZFin.cast
  aesop

-- def ZFin.castNat {a : ℤ} {b : ℕ} (h : a = b := by omega) : ZFin a → Fin b
--   | ⟨i, h⟩ => ⟨i, by omega⟩

structure BraidGenerator (n : ℤ) where
  sign : Bool
  index : ZFin (n - 1)

@[grind]
inductive BraidWord (n : ℕ) where
  | id : BraidWord n
  -- | gen : BraidGenerator n → BraidWord n
  | cons : BraidGenerator n → BraidWord n → BraidWord n

-- def Fin.predSame : (i : Fin n) → i.val ≠ 0 → Fin n
--   | ⟨i + 1, h⟩, h0 => ⟨i, by omega⟩

-- def Fin.succSame : (i : Fin n) → i.val + 1 < n → Fin n
--   | ⟨i, h⟩, h0 => ⟨i + 1, by omega⟩

@[grind]
inductive BraidEquiv : BraidWord n → BraidWord n → Prop
  | refl : (x : BraidWord n) → BraidEquiv x x
  | symm : BraidEquiv x y → BraidEquiv y x
  | trans : BraidEquiv x y → BraidEquiv y z → BraidEquiv x z
  | ignore_head : BraidEquiv x y → BraidEquiv (.cons g x) (.cons g y)
  | inv : BraidEquiv (.cons ⟨s, i⟩ <| .cons ⟨s.not, i⟩ x) x
  | comm {x : BraidWord n} {i₁ i₂ : ZFin (n - 1)} : i₁.val - i₂.val > 1 →
    BraidEquiv (.cons ⟨s₁, i₁⟩ <| .cons ⟨s₂, i₂⟩ x) (.cons ⟨s₂, i₂⟩ <| .cons ⟨s₁, i₁⟩ x)
  | yb {x : BraidWord n} {i : ZFin (↑n - 2)} : BraidEquiv
    (.cons ⟨s, i.succ.cast⟩ <| .cons ⟨s, i.castSucc.cast⟩ <| .cons ⟨s, i.succ.cast⟩ x)
    (.cons ⟨s, i.castSucc.cast⟩ <| .cons ⟨s, i.succ.cast⟩ <| .cons ⟨s, (i.castSucc.cast)⟩ x)

@[simp]
def setoidBraid (n : ℕ) : Setoid (BraidWord n) :=
  ⟨BraidEquiv, ⟨BraidEquiv.refl, BraidEquiv.symm, BraidEquiv.trans⟩⟩

def Braid (n : ℕ) := Quotient (setoidBraid n)

-- GROUPOID TIME

-- def List.toVector (l : List α) : Vector α (l.length) := ⟨l, by rfl⟩

-- #check List.Vector

-- @[grind]
-- def List.Vector.swap (l : List.Vector α n) (i : ZFin (n - 1)) : List.Vector α n :=
--   let ileft := i.castSucc.castNat
--   let iright := i.succ.castNat
--   let left := l.get ileft
--   let right := l.get iright
--   l.set ileft right |>.set iright left

-- @[grind =, simp]
-- lemma get_set_of_ne {v : List.Vector α n} {i j : Fin n} (h : i ≠ j) (a : α) :
--     (v.set i a).get j = v.get j := by
--   grind only [List.Vector.get_set_eq_if]

-- @[grind =, simp]
-- lemma get_set {v : List.Vector α n} {i : Fin n} (a : α) :
--     (v.set i a).get i = a := by
--   simp

-- @[simp, grind]
-- lemma succ_ne_castSucc (i : Fin n) :
--   i.succ ≠ i.castSucc := by
--   grind only [Fin.coeSucc_eq_succ, Fin.succ_ne_zero]

-- @[grind .]
-- lemma ZFin.castNat_eq {i₁ i₂ : ZFin n} : i₁ = i₂ ↔ i₁.castNat h₁ = i₂.castNat h₂ := by
--   unfold castNat
--   aesop

-- TODO find better names for this stuff
-- @[simp, grind]
-- lemma mything {l₁ l₂ : List.Vector α n} {v : α} {i₁ : ZFin n} {i₂ : Fin n} :
--     ((i₁.castNat = i₂ ∧ v = l₂.get i₂) ∨ (i₁.castNat ≠ i₂ ∧ l₁.get i₂ = l₂.get i₂)) → ((l₁.set i₁.castNat v).get i₂ = l₂.get i₂) := by
--   grind

-- TODO find better names for this stuff
-- @[simp, grind]
-- lemma mythingFin {l₁ l₂ : List.Vector α n} {v : α} {i₁ i₂ : Fin n} :
--     ((i₁ = i₂ ∧ v = l₂.get i₂) ∨ (i₁ ≠ i₂ ∧ l₁.get i₂= l₂.get i₂)) → ((l₁.set i₁ v).get i₂ = l₂.get i₂) := by
--   grind

-- @[grind =]
-- lemma List.Vector.swap_involutive (l : List.Vector α n) (i : ZFin (n - 1)) :
--     (l.swap i).swap i = l := by
--   unfold List.Vector.swap
--   simp
--   rw [List.Vector.ext_iff]
--   grind

-- @[grind .]
-- lemma ZFin.sep {i₁ i₂ : ZFin n} : i₂.val - i₁.val > 1 →
--     i₁.succ ≠ i₂.castSucc ∧
--     i₁.castSucc ≠ i₂.castSucc ∧
--     i₁.succ ≠ i₂.succ ∧
--     i₁.castSucc ≠ i₂.succ := by
--   intros h
--   refine ⟨?_, ?_, ?_, ?_⟩
--   all_goals intro hfalse
--   all_goals have hfalse := congrArg (·.val) hfalse
--   all_goals try unfold ZFin.succ at hfalse
--   all_goals try unfold ZFin.castSucc at hfalse
--   all_goals simp_all
--   all_goals aesop

-- @[grind]
-- lemma List.Vector.swap_comm (l : List.Vector α n) (i₁ i₂ : ZFin (n - 1)) (hi : i₂.val - i₁.val > 1) :
--     (l.swap i₁).swap i₂ = (l.swap i₂).swap i₁ := by
--   unfold List.Vector.swap
--   simp
--   rw [List.Vector.ext_iff]
--   grind

-- @[grind]
-- lemma List.Vector.swap_yb (l : List.Vector α n) (i : ZFin (n - 2)) :
--     ((l.swap i.succ.cast).swap (i.castSucc.cast)).swap i.succ.cast =
--     ((l.swap i.castSucc.cast).swap (i.succ.cast)).swap i.castSucc.cast := by
--   unfold List.Vector.swap
--   simp
--   rw [List.Vector.ext_iff]
--   intros j
--   rw [mythingFin]
--   grind
--   sorry

-- @[grind, simp]
-- def BraidWord.cod (d : Fin n → α) : BraidWord n → Fin n → α
--   | .id, i => d i
--   | .cons ⟨_, j⟩ x, i => x.cod d <|
--     if i.val = j.val then
--       j.succ.castNat
--     else if i.val = j.val.succ then
--       j.castSucc.castNat
--     else
--       i

-- @[grind, simp]
-- def BraidWord.cod (d : List.Vector α n) : BraidWord n → List.Vector α n
--   | .id => d
--   | .cons ⟨_, i⟩ x =>
--     x.cod d |>.swap i

@[ext, grind .]
lemma ZFin.ext (a b : ZFin n) : a.val = b.val → a = b := Subtype.ext

@[grind, simp]
def BraidWord.perm {n : ℕ} : BraidWord n → Equiv.Perm (ZFin n)
  | .id => Equiv.refl _
  | .cons ⟨_, j⟩ x =>
    let myFun (i : ZFin n) : ZFin n := if i.val = j.val then
      j.succ.cast
    else if i.val = j.val + 1 then
      j.castSucc.cast
    else
      i
    let mySwap := {
      toFun := myFun
      invFun := myFun
      left_inv i := by
        unfold myFun
        apply Subtype.ext
        grind
      right_inv i := by
        unfold myFun
        apply Subtype.ext
        grind
    }
    x.perm.trans mySwap

  -- {
  --   toFun i := if i.val = j.val then
  --     j.succ.cast
  --   else if i.val = j.val + 1 then
  --     j.castSucc.cast
  --   else
  --     i
  -- }
    -- x.cod d <| if i.val = j.val then
    --   j.succ.cast
    -- else if i.val = j.val + 1 then
    --   j.castSucc.cast
    -- else
      -- i

@[grind]
lemma BraidWord.perm_same (x : BraidWord n) : i.val = j.val → x.perm i = x.perm j := by
  intros h
  have h : i = j := Subtype.ext h
  subst i
  rfl

set_option maxHeartbeats 2000000 in
-- yucky, but it goes thru
def BraidWord.permEq {n : ℕ} {x y : BraidWord n} (heq : BraidEquiv x y) : x.perm = y.perm := by
    induction heq
    all_goals try simp
    -- all_goals sorry
    case ignore_head => grind
    case symm => grind
    case trans => grind
    case inv =>
      apply Equiv.ext ?_
      intros i
      apply Subtype.ext
      grind
    case comm j₁ j₂ _ =>
      apply Equiv.ext ?_
      intros i
      apply Subtype.ext
      simp
      by_cases i.val = j₁.val
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      by_cases i.val = j₁.val + 1
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      by_cases i.val = j₂.val
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      by_cases i.val = j₂.val + 1
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      case neg => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
    case yb j =>
      apply Equiv.ext ?_
      intros i
      apply Subtype.ext
      simp
      by_cases i.val = j.val
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      by_cases i.val = j.val + 1
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      by_cases i.val = j.val + 2
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      case neg => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]

def Braid.perm {n : ℕ} (x : Braid n) : Equiv.Perm (ZFin n) :=
  Quotient.lift (·.perm) (by
    intros x y heq
    exact BraidWord.permEq heq
  ) x

-- @[grind]
-- inductive BraidWordJudgement {α : Type} (d : List α) : BraidWord n → List α →
--     Prop where
--   | id : BraidWordJudgement d (BraidWord.id) d
--   | gen {l : List α} {r : List α} {h : l.length < n - 1} :
--     (x : BraidWord n) → BraidWordJudgement d x (l ++ [s₁, s₂] ++ r) →
--     BraidWordJudgement d (BraidWord.cons ⟨s, ⟨l.length, h⟩⟩ x) (l ++ [s₂, s₁] ++ r)

-- inductive BraidWordJudgement {α : Type} : BraidWord n → List.Vector α n → List.Vector α n → Type where
--   | id (v : List.Vector α n) : BraidWordJudgement (BraidWord.id) v v
--   | gen {l : List.Vector α n₀} {m : List.Vector α m₂} {r : List.Vector α n₂} : BraidWordJudgement (BraidWord.gen ⟨s, i⟩) (l ++ m ++ r) (l ++ m.reverse ++ r)

-- def BraidJudgement (x : Braid n) (v₁ v₂ : List α) : Prop :=
--   Quotient.lift (BraidWordJudgement v₁ · v₂) (by
--     intros x y h
--     apply propext ?_
--     induction h generalizing v₁ v₂
--     case refl => simp
--     case symm => grind
--     case trans => grind
--     case ignore_head x y g a ih =>
--       simp at ih ⊢
--       constructor
--       all_goals intros h
--       all_goals cases h
--       all_goals apply BraidWordJudgement.gen
--       all_goals grind
--     case inv x s i b =>
--       simp
--       constructor
--       case mp =>
--         intros h
--         cases h
--         case gen s₁ s₂ l r hl h =>
--           cases h
--           -- match h with
--           -- | .gen _ =>
--           --   sorry
--           -- cases h
--           -- sorry

--         -- | .gen myx myh =>
--         --   sorry
--         -- match h with
--         -- | .gen _ h =>
--         -- cases h with
--         -- | gen myx h =>
--       sorry
--   ) x

-- instance {n : ℕ} : Coe (ZFin n → α) (List.Vector α n) where
--   coe f := ⟨List.ofFn (fun (i : Fin n) ↦ f ⟨i.val, by have h := i.prop; omega⟩), by simp⟩

-- instance {n : ℕ} : Coe (List.Vector α n) (ZFin n → α) where
--   coe l i := l.get ⟨i.val, by have h := i.prop; omega⟩

-- def List.Vector.toPerm (l : List.Vector α n) (i : ZFin n) : α :=
--   l.get ⟨i.val, by have h := i.prop; omega⟩

-- def List.Vector.ofPerm {n : ℕ} (f : ZFin n → α) : List.Vector α n :=
--   ⟨List.ofFn (fun (i : Fin n) ↦ f ⟨i.val, by have h := i.prop; omega⟩), by simp⟩

-- def TypedBraid {n : ℕ} (dom cod : Equiv.Perm (ZFin n)) : Type :=
--   { x : Braid n // x.cod dom = cod }

-- now we need some way of representing the subgroupoid for a layer
-- the above subgroupoid is a certainly sized braid × ℤ, and sim. for below...
-- and then we can define the generators as functions on the layer -- generators
-- output certainly sized braid × ℤ
-- Then define the functors to/from the subgroupoid and the main thing. From subgroupoid
-- to main is easy (we need layer context, but that's not too bad).
-- From main to subgroupoid, we'll need a typing judgement. So we'll need a judgement
-- of a List.Vector ℕ (n + 2) that it's compatible (aka, it's a permutation of the things
-- that keeps the first stuff the same)

def AscendingByOne : List ℕ → Prop
  | [] => True
  | [_] => True
  | n :: m :: rest => n + 1 = m ∧ (AscendingByOne <| m :: rest)

def Consecutive (l : List ℕ) : Prop :=
  AscendingByOne l ∨ AscendingByOne l.reverse

#check Layer
def Layer.MatchesAbove (l : Layer d c) (p : Equiv.Perm (ZFin c)) : Prop :=
  -- what are the indices of the box's strands?
  let indices := List.range l.box.cod |>.attach.map (fun ⟨i, h⟩ ↦ p.symm ⟨i, by
    have h₁ := l.hcod
    have h₂ : i < l.box.cod := by simp_all only [BoxInfo.cod, List.mem_range]
    omega
  ⟩) |>.map (·.val)
  Consecutive indices
  -- TODO also the left/right gotta match the current layer state, but is that a good idea?

def Layer.AboveSubgroupoid (l : Layer d c) := Braid (c - l.box.cod + 1) × ℤ

-- hmmm... what if we went HARD into the typed-braid definition? Braids always have
-- types associated with them. Nah, would get annoying to track who's next to each other.

#check Finset

#check Fintype

-- def Indices n := ZFin n → Bool

-- def MyFinset (α : Type) := α → Bool

-- def MyFinset.toFinset [Fintype α] (s : MyFinset α) : Finset α :=
--   (Finset.univ.filter (fun a => s a))

-- def MyFinset.card [Fintype α] (s : MyFinset α) : ℕ :=
--   s.toFinset.card

-- def KnownCardMyFinset α [Fintype α] n' := { s : MyFinset α // s.card = n' }
def KnownCardFinset α n' := { s : Finset α // s.card = n' }

def KnownCardFinset.perm (s : KnownCardFinset α n') (eq : Equiv α β) [DecidableEq β] : KnownCardFinset β n' :=
  ⟨s.val.image eq, by simp [Finset.card_image_of_injective _ eq.injective, s.property]⟩

-- the plan here:
-- change "Braid.cod" to instead output a perm, not take a perm as well (start with id perm)
-- projection takes a subset of the indices on the domain
-- in the cons case, it calculates the permutation of x, and then composes w/ the index subset
-- to find the new subset

def BraidWord.projectionHelper (x' : BraidWord n') (g : BraidGenerator n) (perm : Equiv.Perm (ZFin n)) (ind' : KnownCardFinset (ZFin n) n') : BraidWord n' :=
  let ⟨s, i⟩ := g
  match hmem : (decide (i.castSucc.cast ∈ ind'.val ∧ i.succ.cast ∈ ind'.val)) with
    | true =>
      let i' := n' - (ind'.val.filter (· > i.succ.cast)).card - 2
      .cons ⟨s, ⟨i', by
        have h : n' ≥ 2 := by
          repeat clear x'
          simp
          rw [← ind'.prop]
          let twoset : Finset (ZFin n) := {i.castSucc.cast, i.succ.cast}
          have htwo : twoset.card = 2 := by
            apply Finset.card_pair
            intros hfalse
            apply congrArg (·.val) at hfalse
            grind
          rw [← htwo]
          apply Finset.card_le_card ?_
          grind
        omega⟩⟩ x'
    | false => x'

def BraidWord.projection {n n' : ℕ} (x : BraidWord n) (ind : KnownCardFinset (ZFin n) n') : BraidWord n' :=
  match x with
  | .id => .id
  | .cons g x =>
    let x' := x.projection ind
    let perm := x.perm
    let ind' := ind.perm perm
    projectionHelper x' g perm ind'

def Braid.projection {n n' : ℕ} (x : Braid n) (ind : KnownCardFinset (ZFin n) n') : Braid n' :=
  Quotient.lift (⟦·.projection ind⟧) (by
    intros x y heq
    simp
    induction heq
    all_goals try simp
    case symm => grind
    case trans => grind
    case ignore_head x y g heq ih =>
      unfold BraidWord.projection
      rw [Quotient.eq]
      simp
      have hperm : x.perm = y.perm := BraidWord.permEq heq
      rw [hperm]
      -- now prove and use a lemma
    case inv =>
      unfold BraidWord.projection
      rw [Quotient.eq]
      simp
      apply Equiv.ext ?_
      intros i
      apply Subtype.ext
      grind
    case comm j₁ j₂ _ =>
      apply Equiv.ext ?_
      intros i
      apply Subtype.ext
      simp
      by_cases i.val = j₁.val
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      by_cases i.val = j₁.val + 1
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      by_cases i.val = j₂.val
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      by_cases i.val = j₂.val + 1
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      case neg => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
    case yb j =>
      apply Equiv.ext ?_
      intros i
      apply Subtype.ext
      simp
      by_cases i.val = j.val
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      by_cases i.val = j.val + 1
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      by_cases i.val = j.val + 2
      case pos => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
      case neg => grind only [= ZFin.cast_val, ZFin.ext, = ZFin.succ_val, = ZFin.castSucc_val,
        ZFin.cast]
  )
    x

def Layer.gamma (l : Layer d c) : BraidWord c → Braid (c - l.box.cod + 1) :=
  -- first, grab the map of indices: injective from ZFin (c - l.box.cod + 1) to ZFin c
  -- NO! modify l to do that. hmm... we need this anyways
  let myMap : ZFin (c - l.box.cod + 1) → ZFin c
    | ⟨0, _⟩ => ⟨0, by sorry⟩
    | ⟨n + 1, _⟩ => if n < l.left then
        ⟨n, by sorry⟩
      else
        ⟨n + l.box.cod + 1, by sorry⟩
  sorry

def Layer.phi (l : Layer d c) : l.AboveSubgroupoid → Braid c :=
  sorry

-- hmm... what if instead of a List.Vector, we used a function (Fin (n + 2) → α)?

inductive BraidGroupoidWord {α : Type} : List α → List α → Type where
  | id (obj : List α) : BraidGroupoidWord obj obj
  | rw {obj₀ obj₁ obj₂ : List α} : obj₁ = obj₂ → BraidGroupoidWord obj₀ obj₁ →
    BraidGroupoidWord obj₀ obj₂
  | swap (left right : List α): Bool →
    BraidGroupoidWord β (left ++ [a, b] ++ right) → BraidGroupoidWord β (left ++ [b, a] ++ right)

inductive BraidGroupoidEquiv : {l1 l2 : List α} → BraidGroupoidWord l1 l2 → BraidGroupoidWord l1 l2 → Prop
  | refl : (x : _) → BraidGroupoidEquiv x x
  | symm : BraidGroupoidEquiv x y → BraidGroupoidEquiv y x
  | trans : BraidGroupoidEquiv x y → BraidGroupoidEquiv y z → BraidGroupoidEquiv x z
  | inv : BraidGroupoidEquiv (.swap l r s <| .swap l r s.not x) x
  | comm : BraidGroupoidEquiv
    (.swap l (m ++ [c, d] ++ r) s₁ <| .swap (l ++ [a, b] ++ m) r s₂ x)
    (.swap l (m ++ [c, d] ++ r) s₁ <| .swap (l ++ [a, b] ++ m) r s₂ x)
    -- (.cons ⟨s₂, i₂⟩ <| .cons ⟨s₁, i₁⟩ x)
  | yb {i : Fin (n - 1)} {h : i.val + 1 < n - 1} : BraidGroupoidEquiv
    (.cons ⟨s, i⟩ <| .cons ⟨s, i.succSame h⟩ <| .cons ⟨s, i⟩ x)
    (.cons ⟨s, i.succSame h⟩ <| .cons ⟨s, i⟩ <| .cons ⟨s, i.succSame h⟩ x)
    -- TODO composition w/ identity!!!

def Fin.predSame : (i : Fin n) → i.val ≠ 0 → Fin n
  | ⟨i + 1, h⟩, h0 => ⟨i, by omega⟩

def Fin.succSame : (i : Fin n) → i.val + 1 < n → Fin n
  | ⟨i, h⟩, h0 => ⟨i + 1, by omega⟩

inductive BraidEquiv : BraidWord n → BraidWord n → Prop
  | refl : (x : BraidWord n) → BraidEquiv x x
  | symm : BraidEquiv x y → BraidEquiv y x
  | trans : BraidEquiv x y → BraidEquiv y z → BraidEquiv x z
  | ignore_head : BraidEquiv x y → BraidEquiv (.cons g x) (.cons g y)
  | inv : BraidEquiv (.cons ⟨s, i⟩ <| .cons ⟨s.not, i⟩ x) x
  | comm {i₁ i₂ : Fin (n - 1)} : i₁ - i₂ > (1 : ℕ) →
    BraidEquiv (.cons ⟨s₁, i₁⟩ <| .cons ⟨s₂, i₂⟩ x) (.cons ⟨s₂, i₂⟩ <| .cons ⟨s₁, i₁⟩ x)
  | yb {i : Fin (n - 1)} {h : i.val + 1 < n - 1} : BraidEquiv
    (.cons ⟨s, i⟩ <| .cons ⟨s, i.succSame h⟩ <| .cons ⟨s, i⟩ x)
    (.cons ⟨s, i.succSame h⟩ <| .cons ⟨s, i⟩ <| .cons ⟨s, i.succSame h⟩ x)

@[simp]
def setoidBraid (n : ℕ) : Setoid (BraidWord n) :=
  ⟨BraidEquiv, ⟨BraidEquiv.refl, BraidEquiv.symm, BraidEquiv.trans⟩⟩

def Braid (n : ℕ) := Quotient (setoidBraid n)


-- n counts how many free strands there are, plus 1 for S.
-- Objects are natural numbers less than n: indices of S
-- Maybe have objects be permutations instead?
inductive LayerSubgroupoid (n : ℕ) : (Fin n) → (Fin n) → Type where
| sigmaUnderlineLeft : Bool → LayerSubgroupoid n l (l.predSame sorry).castSucc
-- | sigmaUnderlineRight : Bool → LayerSubgroupoid n l (l.pred _).castSucc
| sigma {l : Fin n} : Bool → (i : Fin (n - 1)) → (hi : i.val ≠ l.val ∧ i.val.succ ≠ l.val) →
  LayerSubgroupoid n l l

#check Fin.cast


-- first argument BELOW the second
def Braid.append : Braid n → Braid n → Braid n := sorry

-- TODO decide braid equivalence :)
instance : DecidableEq (Braid n) := fun x y ↦ sorry

inductive Word : ℕ → ℕ → Type where
  | just_braid : Braid n → Word n n
  -- the cons things append at the top (near the codomain)
  | consLayer : (l : Layer m k) → Word n m → Word n k
  | consBraid : Braid m → Word n m → Word n m

-- The rewrite rules on those words we claim to canonicalize
inductive WordEquiv : Word n m → Word n m → Prop
  -- Boring old equiv relation stuff
  | refl : (x : Word n m) → WordEquiv x x
  | symm (x y : Word n m) : WordEquiv x y → WordEquiv y x
  | trans (x y z : Word n m) : WordEquiv x y → WordEquiv y z → WordEquiv x z

  -- Slightly less boring rules are only here b/c of Word's representation
  | restLayer : WordEquiv x y → WordEquiv (.consLayer l x) (.consLayer l y)
  | restBraid : WordEquiv x y → WordEquiv (.consBraid b x) (.consBraid b y)
  | mergeBraid : WordEquiv (Word.consBraid b1 (Word.consBraid b2 x))
    (Word.consBraid (b1.append b2) x)

  -- the ACTUAL rewrite rules the paper claims to canonicalize (fig 5)
  -- l1 : drag a strand on the right of the box above/below the box to the left side
  -- The drag-to-left case is handled by symmetry
  | l1 : (above : Bool) →
    WordEquiv (Word.consLayer l x)
      (Word.consBraid a (Word.consLayer l (Word.consBraid b x)))

    -- (l.belowRight hRight above) (Word.consLayer (l.shiftRight Right)
    --   (Word.consBraid (l.aboveRight hRight above) rest)))


-- shift a box to the right; strand to the left
-- If "above", strand goes up and over to the left
-- see fig 5a -- this details shiftToRight, above=True
def shiftToRight (Left Cod Right : Obj C) (x : C) (above : Bool) :
    Braid (Left ++ [x] ++ Cod ++ Right) (Left ++ Cod ++ [x] ++ Right) :=
    let top := Braid.underline ([x] ++ Cod) |>.pad Left Right
    let top := if above then top else top.invert_in_place
      by
        simp at top ⊢
        exact top

-- L1 move, box goes to right, this is the above braid
def Layer.aboveRight [Box α C] (l : Layer α C A B)
  {Right} (hRight : l.right = [x] ++ Right) (above : Bool) :
    Braid (l.left ++ [x] ++ Box.cod l.box ++ Right) B :=
  let b := shiftToRight l.left (Box.cod l.box) Right x above
  by
    rw (occs := [3]) [l.hcod]
    rw [hRight]
    simp at b ⊢
    exact b

-- L1 move, box goes to right, this is the below braid
def Layer.belowRight [Box α C] (l : Layer α C A B)
  {Right} (hRight : l.right = [x] ++ Right) (above : Bool) :
    Braid A (l.left ++ [x] ++ Box.dom l.box ++ Right) :=
  let b := shiftToRight l.left (Box.dom l.box) Right x above |>.inverse
  by
    rw (occs := [1]) [l.hdom]
    rw [hRight]
    simp at b ⊢
    exact b

-- L1 move, box goes to left, this is the above braid
def Layer.aboveLeft [Box α C] (l : Layer α C A B)
  {Left} (hLeft : l.left = Left ++ [x]) (above : Bool) :
    Braid (Left ++ Box.cod l.box ++ [x] ++ l.right) B :=
  let b := shiftToRight Left (Box.cod l.box) l.right x above |>.inverse
  by
    rw (occs := [3]) [l.hcod]
    rw [hLeft]
    simp at b ⊢
    exact b

-- L1 move, box goes to left, this is the below braid
def Layer.belowLeft [Box α C] (l : Layer α C A B)
  {Left} (hLeft : l.left = Left ++ [x]) (above : Bool) :
    Braid A (Left ++ Box.dom l.box ++ [x] ++ l.right) :=
  let b := shiftToRight Left (Box.dom l.box) l.right x above
  by
    rw (occs := [1]) [l.hdom]
    rw [hLeft]
    simp at b ⊢
    exact b

-- L1 move, box goes to right, change the layer. Right is the right strands except x
def Layer.shiftRight [Box α C] (l : Layer α C A B) (Right) :
    Layer α C (l.left ++ [x] ++ (Box.dom l.box) ++ Right)
    (l.left ++ [x] ++ Box.cod l.box ++ Right) :=
  { left := l.left ++ [x], box := l.box, right := Right,
    hdom := by simp, hcod := by simp }

-- L1 move, box goes to left, change the layer. Left is the left strands except x
def Layer.shiftLeft [Box α C] (l : Layer α C A B)
  (Left) : Layer α C (Left ++ Box.dom l.box ++ [x] ++ l.right)
    (Left ++ (Box.cod l.box) ++ [x] ++ l.right) :=
    { left := Left, box := l.box, right := [x] ++ l.right,
      hdom := by simp, hcod := by simp }
