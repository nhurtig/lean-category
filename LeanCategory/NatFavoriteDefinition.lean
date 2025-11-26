import Mathlib.Data.List.Rotate
universe u

variable {C : Type u}

-- e.g. knit vs. purl, carrier direction/number, loop direction/number
variable {BoxInfo : Type} [DecidableEq BoxInfo]

local notation "Obj" => List C -- used to be List (Bool × C),
-- but Nat realized that we don't need that for the paper's result;
-- it'd be nice to generalize, and it's certainly possible without too
-- much hard new math, but it'd be a little annoying (one would have to
-- make a step where all the twists are combed down)

-- Object map of the involutive flip; page 9
def Obj.flip : Obj → Obj := List.reverse

-- Page 10
structure Box where
  dom : Obj
  cod : Obj
  info : BoxInfo
  hDom : dom.length >= 1
  hCod : cod.length >= 2

-- A Box (stitch) with identity strands on its left/right
structure Layer (dom cod : Obj) where
  left : Obj
  box : Box (BoxInfo := BoxInfo)
  right : Obj
  hdom : dom = left ++ box.dom ++ right
  hcod : cod = left ++ box.cod ++ right

-- Swaps the given index and next one (for braid group stuff)
def Obj.swap : (A : Obj) → Fin (A.length - 1) → Obj
  | fst :: snd :: rest, ⟨0, _⟩ => snd :: fst :: rest
  | fst :: rest, ⟨i+1, h⟩ => fst :: Obj.swap rest ⟨i, by simp_all; omega⟩
  | [fst], ⟨0, _⟩ => by contradiction
  | [], ⟨0, _⟩ => by contradiction

def Obj.swap_preserve_length : ∀ A : Obj, ∀ i : Fin (A.length - 1),
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

-- padding to the right doesn't change swapping
def Obj.swap_padRight : ∀ A B Right : Obj, ∀ i : Fin (A.length - 1),
  ∀ i' : Fin ((A ++ Right).length - 1),
  i.val = i'.val → Obj.swap A i = B → Obj.swap (A ++ Right) i' = B ++ Right := by
  sorry

-- a single braid generator; it knows the strands to its left and right
structure BraidGenerator (dom cod : Obj) where
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
inductive Braid : Obj → Obj → Type u where
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
def BraidGenerator.pad (Left Right : Obj) : BraidGenerator A B →
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
def Braid.pad (Left Right : Obj) : Braid A B →
  Braid (Left ++ A ++ Right) (Left ++ B ++ Right)
  | id => id
  | cons g b => cons (g.pad Left Right) (b.pad Left Right)

-- moves a strand on the left all the way to the right, positive crossings
def Braid.underline : (A : Obj) → Braid A (A.rotate 1)
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
def shiftToRight (Left Cod Right : Obj) (x : C) (above : Bool) :
    Braid (Left ++ [x] ++ Cod ++ Right) (Left ++ Cod ++ [x] ++ Right) :=
    let top := Braid.underline ([x] ++ Cod) |>.pad Left Right
    let top := if above then top else top.invert_in_place
      by
        simp at top ⊢
        exact top

-- L1 move, box goes to right, this is the above braid
def Layer.aboveRight (l : Layer (BoxInfo := BoxInfo) A B)
  {Right} (hRight : l.right = [x] ++ Right) (above : Bool) :
    Braid (l.left ++ [x] ++ l.box.cod ++ Right) B :=
  let b := shiftToRight l.left l.box.cod Right x above
  by
    rw (occs := [3]) [l.hcod]
    rw [hRight]
    simp at b ⊢
    exact b

-- L1 move, box goes to right, this is the below braid
def Layer.belowRight (l : Layer (BoxInfo := BoxInfo) A B)
  {Right} (hRight : l.right = [x] ++ Right) (above : Bool) :
    Braid A (l.left ++ [x] ++ l.box.dom ++ Right) :=
  let b := shiftToRight l.left l.box.dom Right x above |>.inverse
  by
    rw (occs := [1]) [l.hdom]
    rw [hRight]
    simp at b ⊢
    exact b

-- L1 move, box goes to left, this is the above braid
def Layer.aboveLeft (l : Layer (BoxInfo := BoxInfo) A B)
  {Left} (hLeft : l.left = Left ++ [x]) (above : Bool) :
    Braid (Left ++ l.box.cod ++ [x] ++ l.right) B :=
  let b := shiftToRight Left l.box.cod l.right x above |>.inverse
  by
    rw (occs := [3]) [l.hcod]
    rw [hLeft]
    simp at b ⊢
    exact b

-- L1 move, box goes to left, this is the below braid
def Layer.belowLeft (l : Layer (BoxInfo := BoxInfo) A B)
  {Left} (hLeft : l.left = Left ++ [x]) (above : Bool) :
    Braid A (Left ++ l.box.dom ++ [x] ++ l.right) :=
  let b := shiftToRight Left l.box.dom l.right x above
  by
    rw (occs := [1]) [l.hdom]
    rw [hLeft]
    simp at b ⊢
    exact b

-- L1 move, box goes to right, change the layer. Right is the right strands except x
def Layer.shiftRight (l : Layer (BoxInfo := BoxInfo) A B)
  (Right) : Layer (BoxInfo := BoxInfo) (l.left ++ [x] ++ l.box.dom ++ Right)
    (l.left ++ [x] ++ l.box.cod ++ Right) :=
    { left := l.left ++ [x], box := l.box, right := Right,
      hdom := by simp, hcod := by simp }

-- L1 move, box goes to left, change the layer. Left is the left strands except x
def Layer.shiftLeft (l : Layer (BoxInfo := BoxInfo) A B)
  (Left) : Layer (BoxInfo := BoxInfo) (Left ++ l.box.dom ++ [x] ++ l.right)
    (Left ++ l.box.cod ++ [x] ++ l.right) :=
    { left := Left, box := l.box, right := [x] ++ l.right,
      hdom := by simp, hcod := by simp }

-- Almost the form of what the algorithm in the paper canonicalizes. The algorithm
-- usually likes to have the braids and layers alternate, but that'd be annoying to deal
-- with in the proof
inductive Word : Obj → Obj → Type u where
  | empty : Word A A
  | consLayer : Layer (BoxInfo := BoxInfo) A B →
    Word B D → Word A D -- C omitted b/c name conflict
  | consBraid : Braid A B →
    Word B D → Word A D -- C omitted b/c name conflict

-- The rewrite rules on those words we claim to canonicalize
inductive WordEquiv : ∀ {A B : Obj}, Word (BoxInfo := BoxInfo) A B →
  Word (BoxInfo := BoxInfo) A B → Prop
  -- Boring old equiv relation stuff
  | refl (x : Word A B) : WordEquiv x x
  | symm (x y : Word A B) : WordEquiv x y → WordEquiv y x
  | trans (x y z : Word A B) : WordEquiv x y → WordEquiv y z → WordEquiv x z

  -- Slightly less boring rules are only here b/c of Word's representation
  | restLayer : WordEquiv x y → WordEquiv (Word.consLayer l x) (Word.consLayer l y)
  | restBraid : WordEquiv x y → WordEquiv (Word.consBraid l x) (Word.consBraid l y)
  | mergeBraid : WordEquiv (Word.consBraid b1 (Word.consBraid b2 x))
    (Word.consBraid (b1.append b2) x)

  -- the ACTUAL rewrite rules the paper claims to canonicalize (fig 5)
  -- fig. 5a shows L1 right and above
  | l1Right : {A B Right : Obj} → {x : C} → {rest : Word B _} →
    (above : Bool) → (l : Layer A B) → {hRight : l.right = [x] ++ Right} →
    WordEquiv (Word.consLayer l rest)
    (Word.consBraid (l.belowRight hRight above) (Word.consLayer (l.shiftRight Right)
      (Word.consBraid (l.aboveRight hRight above) rest)))
  | l1Left : {A B Left : Obj} → {x : C} → {rest : Word B _} →
    (above : Bool) → (l : Layer A B) → {hLeft : l.left = Left ++ [x]} →
    WordEquiv (Word.consLayer l rest)
    (Word.consBraid (l.belowLeft hLeft above) (Word.consLayer (l.shiftLeft Left)
      (Word.consBraid (l.aboveLeft hLeft above) rest)))
