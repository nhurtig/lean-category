import Mathlib.Data.List.Rotate

abbrev Obj C := List C -- used to be List (Bool × C),
-- but Nat realized that we don't need that for the paper's result;
-- it'd be nice to generalize, and it's certainly possible without too
-- much hard new math, but it'd be a little annoying (one would have to
-- make a step where all the twists are combed down)

-- Object map of the involutive flip; page 9
def Obj.flip : Obj C → Obj C := List.reverse

-- Page 10
class Box (α C : Type) where
  dom : α → Obj C
  cod : α → Obj C
  hDom : ∀ a : α, (dom a).length >= 1
  hCod : ∀ a : α, (cod a).length >= 2

-- A Box (stitch) with identity strands on its left/right
structure Layer (α C : Type) [Box α C] (dom cod : Obj C) where
  left : Obj C
  box : α
  right : Obj C
  hdom : dom = left ++ Box.dom box ++ right
  hcod : cod = left ++ Box.cod box ++ right

-- Swaps the given index and next one (for braid group stuff)
-- maybe make this a proposition?
inductive Obj.Swap : ℕ → Obj C → Obj C → Prop where
| base {fst snd : C} {rest : Obj C} : Obj.Swap 0 (fst :: snd :: rest) (snd :: fst :: rest)
| step : Obj.Swap -- ugh... we're just making proof burden to show this inductive defn is right.
@[grind, simp]
def Obj.swap : (A : Obj C) → Fin (A.length - 1) → Obj C
  | fst :: snd :: rest, ⟨0, _⟩ => snd :: fst :: rest
  | fst :: rest, ⟨i+1, _⟩ => fst :: Obj.swap rest ⟨i, by simp_all; omega⟩
  | [fst], ⟨0, _⟩ => by contradiction
  | [], ⟨0, _⟩ => by contradiction

def Obj.swap_preserve_length : ∀ A : Obj C, ∀ i : Fin (A.length - 1),
  A.length = (Obj.swap A i).length := by
  intros A i
  rcases i with ⟨i, hi⟩
  induction i generalizing A
  case zero =>
    unfold Obj.swap
    cases A with
    | nil => contradiction
    | cons fst rest =>
      cases rest with
      | nil => contradiction
      | cons snd rest => simp
  case succ ih =>
    unfold Obj.swap
    cases A with
    | nil => contradiction
    | cons fst rest =>
      simp
      apply ih

@[simp]
def Obj.swap_small : ∀ A B : Obj C, ∀ i : Fin (A.length - 1),
    (A ++ B).swap ⟨i.val, by grind⟩ = A.swap i ++ B := by
  intros A
  cases A
  all_goals simp
  case cons fst A =>
    cases A
    all_goals simp
    case cons snd A =>
      induction A
      case nil =>
        simp
        unfold Obj.swap
        simp
      sorry
  -- intros A B i
  -- rcases i with ⟨i, hi⟩
  -- induction i
  -- case zero =>

  sorry

-- padding to the right doesn't change swapping
def Obj.swap_padRight : ∀ A B Right : Obj C, ∀ i : Fin (A.length - 1),
    ∀ i' : Fin ((A ++ Right).length - 1),
    i.val = i'.val → Obj.swap A i = B → Obj.swap (A ++ Right) i' = B ++ Right := by
  intros A B Right i i' hii' hAiB
  rcases i with ⟨i, hi⟩
  rcases i' with ⟨i', hi'⟩
  simp at hii'
  subst i'
  induction i
  case zero =>
    simp

    sorry
  -- grind only [swap.eq_def, = List.length_append, = List.cons_append, = List.length_cons, swap,
  --   Fin.isLt, #43b9, #13c6, #d7ab, #e951]

-- a single braid generator; it knows the strands to its left and right as well
structure BraidGenerator (dom cod : Obj C) where
  sign : Bool
  index : Fin (dom.length - 1)
  h : Obj.swap dom index = cod

-- upside down, but not the inverse
def BraidGenerator.reverse : (BraidGenerator A B) → BraidGenerator B A := fun g =>
  { sign := g.sign, index := by
      rw [← g.h]
      rw [← Obj.swap_preserve_length]
      exact g.index,
    h := sorry }

-- invert the sign, but don't change the objects
def BraidGenerator.invert_in_place : (BraidGenerator A B) → BraidGenerator A B := fun g =>
  { sign := g.sign.not, index := g.index, h := g.h }

-- invert the sign AND make the objects upside down
def BraidGenerator.inverse : (BraidGenerator A B) → BraidGenerator B A :=
  BraidGenerator.reverse ∘ BraidGenerator.invert_in_place

-- Rotate 180 degrees
def BraidGenerator.flip : (BraidGenerator A B) →
  BraidGenerator (Obj.flip A) (Obj.flip B) := fun g =>
  { sign := g.sign, index := ⟨A.length - 2 - g.index, by unfold Obj.flip; simp; omega⟩,
    h := sorry}

-- A braid in a braid groupoid
inductive Braid : Obj C → Obj C → Type where
  | id : Braid A A
  | cons : BraidGenerator A B → Braid B D → Braid A D

-- braid concatenation/multiplication
def Braid.append : Braid A B → Braid B D → Braid A D
  | id, b2 => b2
  | cons x b1, b2 => cons x (b1.append b2)

-- reverses, doesn't invert generators
def Braid.reverse : (Braid A B) → Braid B A
  | id => id
  | cons g b => b.reverse.append (cons g.reverse id)

-- inverts generators, doesn't reverse
def Braid.invert_in_place : (Braid A B) → Braid A B
  | id => id
  | cons g b => (cons g.invert_in_place b.invert_in_place)

-- mathematical inverse
def Braid.inverse : (Braid A B) → Braid B A :=
  Braid.reverse ∘ Braid.invert_in_place

-- 180 degree rotation
def Braid.flip : (Braid A B) → Braid (Obj.flip A) (Obj.flip B)
  | id => id
  | cons g b => cons g.flip b.flip

-- Puts identities on the left and right
def BraidGenerator.pad (Left Right : Obj C) : BraidGenerator A B →
  BraidGenerator (Left ++ A ++ Right) (Left ++ B ++ Right) := fun g =>
  let index : Fin ((Left ++ A ++ Right).length - 1) := ⟨Left.length + g.index, by simp; omega⟩
  { sign := g.sign, index := index,
    h := by
      induction Left
      case nil =>
        simp_all
        apply Obj.swap_padRight (i := g.index) (i' := index)
        · unfold index
          simp
        · apply g.h
      case cons head tail ih =>
        sorry
  }

-- Puts identities on the left and right
def Braid.pad (Left Right : Obj C) : Braid A B →
  Braid (Left ++ A ++ Right) (Left ++ B ++ Right)
  | id => id
  | cons g b => cons (g.pad Left Right) (b.pad Left Right)

-- moves a strand on the left all the way to the right, positive crossings
def Braid.underline : (A : Obj C) → Braid A (A.rotate 1)
  | [] => id
  | [x] => by simpa [List.rotate] using id
  | x :: a :: A =>
    let g : BraidGenerator (x :: a :: A) (a :: x :: A) :=
      { sign := true, index := ⟨0, by simp⟩,
        h := by unfold Obj.swap; simp}
    let b := Braid.underline (x :: A) |>.pad [a] []
    by
      simp at b
      exact cons g b

-- horizontal (parallel) concatenation of braids
def Braid.tensor : Braid A B → Braid D E → Braid (A ++ D) (B ++ E) := fun b1 b2 => by
  have b1 := (b1.pad [] D)
  have b2 := (b2.pad B [])
  simp at b1 b2
  exact b1.append b2

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

-- Almost the form of what the algorithm in the paper canonicalizes. The algorithm
-- usually likes to have the braids and layers alternate, but that'd be annoying to deal
-- with in the proof (pretty easy to convert to alternating if needed)
inductive Word (α C : Type) [Box α C] : Obj C → Obj C → Type where
  | empty : Word α C A A
  | consLayer : Layer α C A B → Word α C B D → Word α C A D
  | consBraid : Braid A B → Word α C B D → Word α C A D

-- The rewrite rules on those words we claim to canonicalize
inductive WordEquiv (α C : Type) [Box α C] : ∀ {A B : Obj C}, Word α C A B →
  Word α C A B → Prop
  -- Boring old equiv relation stuff
  | refl (x : Word α C A B) : WordEquiv α C x x
  | symm (x y : Word α C A B) : WordEquiv α C x y → WordEquiv α C y x
  | trans (x y z : Word α C A B) : WordEquiv α C x y → WordEquiv α C y z → WordEquiv α C x z

  -- Slightly less boring rules are only here b/c of Word's representation
  | restLayer : WordEquiv α C x y → WordEquiv α C (Word.consLayer l x) (Word.consLayer l y)
  | restBraid : WordEquiv α C x y → WordEquiv α C (Word.consBraid l x) (Word.consBraid l y)
  | mergeBraid : WordEquiv α C (Word.consBraid b1 (Word.consBraid b2 x))
    (Word.consBraid (b1.append b2) x)

  -- the ACTUAL rewrite rules the paper claims to canonicalize (fig 5)
  -- fig. 5a shows L1 right and above
  | l1Right : {A B Right : Obj C} → {x : C} → {rest : Word α C B _} →
    (above : Bool) → (l : Layer α C A B) → {hRight : l.right = [x] ++ Right} →
    WordEquiv α C (Word.consLayer l rest)
    (Word.consBraid (l.belowRight hRight above) (Word.consLayer (l.shiftRight Right)
      (Word.consBraid (l.aboveRight hRight above) rest)))
  | l1Left : {A B Left : Obj C} → {x : C} → {rest : Word α C B _} →
    (above : Bool) → (l : Layer α C A B) → {hLeft : l.left = Left ++ [x]} →
    WordEquiv α C (Word.consLayer l rest)
    (Word.consBraid (l.belowLeft hLeft above) (Word.consLayer (l.shiftLeft Left)
      (Word.consBraid (l.aboveLeft hLeft above) rest)))
