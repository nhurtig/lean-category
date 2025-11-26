/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The free monoidal category over a type

Given a type `C`, the free monoidal category over `C` has as objects formal expressions built from
(formal) tensor products of terms of `C` and a formal unit. Its morphisms are compositions and
tensor products of identities, unitors and associators.

In this file, we construct the free monoidal category and prove that it is a monoidal category. If
`D` is a monoidal category, we construct the functor `FreeMonoidalCategory C ⥤ D` associated to
a function `C → D`.

The free monoidal category has two important properties: it is a groupoid and it is thin. The former
is obvious from the construction, and the latter is what is commonly known as the monoidal coherence
theorem. Both of these properties are proved in the file `Coherence.lean`.

-/

@[expose] public section


universe v' u u'

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u}

-- e.g. knit vs. purl, carrier direction/number, loop direction/number
variable {BoxInfo : Type} [DecidableEq BoxInfo]

section

variable (C)

variable (BoxInfo)

-- Don't generate unnecessary `sizeOf_spec` or `injEq` lemmas
-- which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/--
Given a type `C`, the free monoidal category over `C` has as objects formal expressions built from
(formal) tensor products of terms of `C` and a formal unit. Its morphisms are compositions and
tensor products of identities, unitors and associators.
-/
inductive FreeMonoidalCategoryListItem : Type u
  | of : C → FreeMonoidalCategoryListItem
  | ofFlipped : C → FreeMonoidalCategoryListItem
  deriving Inhabited

-- inductive FreeMonoidalCategory : Type u
--   | unit : FreeMonoidalCategory
--   | tensor : (FreeMonoidalCategoryListItem C) → FreeMonoidalCategory → FreeMonoidalCategory
--   deriving Inhabited
end

local notation "F" => FreeMonoidalCategoryListItem

namespace FreeMonoidalCategory

-- -- Length of the tensor product (used to constrain box morphisms)
-- def length : F C → Nat
--   | of _ => 1
--   | ofFlipped _ => 1
--   | unit => 0
  -- | tensor A B => A.length + B.length

-- def FreeMonoidalCategoryListItem.flip : FreeMonoidalCategoryListItem C → FreeMonoidalCategoryListItem C
--   | of
--   | [] => []
--   | A :: rest => A.flip :: rest.flip
--   | ofFlipped A => of A
--   | unit => unit
--   | tensor A B => tensor B.flip A.flip

local notation "Obj" => List C -- used to be List (Bool × C),
-- but Nat realized that we don't need that for the paper's result;
-- it'd be nice to generalize though

-- Object map of the involutive flip; page 9
def Obj.flip : Obj → Obj := List.reverse

-- Page 10
structure Box where
  dom : Obj
  cod : Obj
  info : BoxInfo
  hDom : dom.length >= 1
  hCod : cod.length >= 2

-- A Box with identity strands on the left/right
structure Layer (dom cod : Obj) where
  left : Obj
  box : Box (BoxInfo := BoxInfo)
  right : Obj
  hdom : dom = left ++ box.dom ++ right
  hcod : cod = left ++ box.cod ++ right

-- Swaps the given index and next one
def Obj.swap : (A : Obj) → Fin (A.length - 1) → Obj
  | fst :: snd :: rest, ⟨0, _⟩ => snd :: fst :: rest
  | fst :: rest, ⟨i+1, h⟩ => fst :: Obj.swap rest ⟨i, by simp_all; omega⟩
  | [fst], ⟨0, _⟩ => by contradiction
  | [], ⟨0, _⟩ => by contradiction

lemma Obj.swap_preserve_length : ∀ A : Obj, ∀ i : Fin (A.length - 1),
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

lemma Obj.swap_padRight : ∀ A B Right : Obj, ∀ i : Fin (A.length - 1), ∀ i' : Fin ((A ++ Right).length - 1),
  i.val = i'.val → Obj.swap A i = B → Obj.swap (A ++ Right) i' = B ++ Right := by
  sorry

structure BraidGenerator (dom cod : Obj) where
  sign : Bool
  index : Fin (dom.length - 1)
  h : Obj.swap dom index = cod

def BraidGenerator.reverse : (BraidGenerator A B) → BraidGenerator B A := fun g =>
  { sign := g.sign, index := by
      rw [← g.h]
      rw [← Obj.swap_preserve_length]
      exact g.index,
    h := sorry }

def BraidGenerator.invert_in_place : (BraidGenerator A B) → BraidGenerator A B := fun g =>
  { sign := g.sign.not, index := g.index, h := g.h }

def BraidGenerator.inverse : (BraidGenerator A B) → BraidGenerator B A :=
  BraidGenerator.reverse ∘ BraidGenerator.invert_in_place

def BraidGenerator.flip : (BraidGenerator A B) → BraidGenerator (Obj.flip A) (Obj.flip B) := fun g =>
  { sign := g.sign, index := ⟨A.length - 2 - g.index, by unfold Obj.flip; simp; omega⟩,
    h := sorry}

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
      have hrw : (x :: A).rotate 1 = A ++ [x] := by
        cases A
        all_goals simp [List.rotate]
      rw [hrw] at b
      exact cons g b

def Braid.tensor : Braid A B → Braid D E → Braid (A ++ D) (B ++ E) := fun b1 b2 => by
  have b1 := (b1.pad [] D)
  have b2 := (b2.pad B [])
  simp at b1 b2
  exact b1.append b2

-- lLeft's box is shifted one to the left of lRight's (fig 5a)
-- structure Layer.leftOf {Left Right}
--   (lLeft : Layer (C := C) (BoxInfo := BoxInfo) Left ([x] ++ Right))
--   (lRight : Layer (C := C) (BoxInfo := BoxInfo) (Left ++ [x]) Right) where
--   hbox : lLeft.box = lRight.box

-- shift a box to the right; strand to the left (fig 5a).
-- If "above", strand goes up and over to the left (fig 5a)
def shiftToRight (Left Cod Right : Obj) (x : C) (above : Bool) :
  -- {Right} (hRight : l.right = [x] ++ Right) :
  -- Braid (Left ++ Dom ++ [x] ++ Right) (Left ++ [x] ++ Dom ++ Right)
    -- × Layer (BoxInfo := BoxInfo) (l.left ++ [x] ++ l.box.dom ++ Right)
    --   (l.left ++ [x] ++ l.box.cod ++ Right)
    Braid (Left ++ [x] ++ Cod ++ Right) (Left ++ Cod ++ [x] ++ Right) :=
    -- let bot := Braid.underline ([x] ++ Dom) |>.inverse |>.pad Left Right
    -- let layer : Layer (l.left ++ [x] ++ l.box.dom ++ Right) (l.left ++ [x] ++ l.box.cod ++ Right) :=
      -- { left := l.left ++ [x], box := l.box, right := Right,
        -- hdom := by simp, hcod := by simp }
    let top := Braid.underline ([x] ++ Cod) |>.pad Left Right
    -- let bot := if above then bot else bot.invert_in_place
    let top := if above then top else top.invert_in_place
    -- ⟨ by
    --     -- rw (occs := [1]) [l.hdom]
    --     -- rw [hRight]
    --     simp at bot
    --     have hrw : (x :: Dom).rotate 1 = Dom ++ [x] := by
    --       cases Dom
    --       all_goals rw [List.rotate]
    --       all_goals simp
    --     rw [hrw] at bot
    --     simp at bot ⊢
    --     exact bot,
    --   -- layer,
      by
        -- rw (occs := [3]) [l.hcod]
        -- rw [hRight]
        simp at top
        have hrw : (x :: Cod).rotate 1 = Cod ++ [x] := by
          cases Cod
          all_goals rw [List.rotate]
          all_goals simp
        rw [hrw] at top
        simp at top ⊢
        exact top
        -- ⟩

def Layer.aboveRight (l : Layer (BoxInfo := BoxInfo) A B)
  {Right} (hRight : l.right = [x] ++ Right) (above : Bool) :
    Braid (l.left ++ [x] ++ l.box.cod ++ Right) B :=
  let b := shiftToRight l.left l.box.cod Right x above
  by
    rw (occs := [3]) [l.hcod]
    rw [hRight]
    simp at b ⊢
    exact b

def Layer.belowRight (l : Layer (BoxInfo := BoxInfo) A B)
  {Right} (hRight : l.right = [x] ++ Right) (above : Bool) :
    Braid A (l.left ++ [x] ++ l.box.dom ++ Right) :=
  let b := shiftToRight l.left l.box.dom Right x above |>.inverse
  by
    rw (occs := [1]) [l.hdom]
    rw [hRight]
    simp at b ⊢
    exact b

def Layer.aboveLeft (l : Layer (BoxInfo := BoxInfo) A B)
  {Left} (hLeft : l.left = Left ++ [x]) (above : Bool) :
    Braid (Left ++ l.box.cod ++ [x] ++ l.right) B :=
  let b := shiftToRight Left l.box.cod l.right x above |>.inverse
  by
    rw (occs := [3]) [l.hcod]
    rw [hLeft]
    simp at b ⊢
    exact b

def Layer.belowLeft (l : Layer (BoxInfo := BoxInfo) A B)
  {Left} (hLeft : l.left = Left ++ [x]) (above : Bool) :
    Braid A (Left ++ l.box.dom ++ [x] ++ l.right) :=
  let b := shiftToRight Left l.box.dom l.right x above
  by
    rw (occs := [1]) [l.hdom]
    rw [hLeft]
    simp at b ⊢
    exact b

def Layer.shiftRight (l : Layer (BoxInfo := BoxInfo) A B)
  {Right} : Layer (BoxInfo := BoxInfo) (l.left ++ [x] ++ l.box.dom ++ Right)
    (l.left ++ [x] ++ l.box.cod ++ Right) :=
    { left := l.left ++ [x], box := l.box, right := Right,
      hdom := by simp, hcod := by simp }

def Layer.shiftLeft (l : Layer (BoxInfo := BoxInfo) A B)
  {Left} : Layer (BoxInfo := BoxInfo) (Left ++ l.box.dom ++ [x] ++ l.right)
    (Left ++ l.box.cod ++ [x] ++ l.right) :=
    { left := Left, box := l.box, right := [x] ++ l.right,
      hdom := by simp, hcod := by simp }

inductive Word : Obj → Obj → Type u where
  | empty : Word A A
  -- | braid : Braid A B → Word A B
  -- | layer : Layer (BoxInfo := BoxInfo) A B → Word A B
  | consLayer : Layer (BoxInfo := BoxInfo) A B →
    Word B D → Word A D -- C omitted b/c name conflict
  | consBraid : Braid A B →
    Word B D → Word A D -- C omitted b/c name conflict

inductive WordEquiv : ∀ {A B : Obj}, Word (BoxInfo := BoxInfo) A B →
  Word (BoxInfo := BoxInfo) A B → Prop
  | refl (x : Word A B) : WordEquiv x x
  | symm (x y : Word A B) : WordEquiv x y → WordEquiv y x
  | trans (x y z : Word A B) : WordEquiv x y → WordEquiv y z → WordEquiv x z

  | restLayer : WordEquiv x y → WordEquiv (Word.consLayer l x) (Word.consLayer l y)
  | restBraid : WordEquiv x y → WordEquiv (Word.consBraid l x) (Word.consBraid l y)
  | mergeBraid : WordEquiv (Word.consBraid b1 (Word.consBraid b2 x))
    (Word.consBraid (b1.append b2) x)

  -- fig. 5a shows L1 right and above
  | l1Right : {A B Right : Obj} → {x : C} → {rest : Word B _} →
    (above : Bool) → (l : Layer A B) → {hRight : l.right = [x] ++ Right} →
    WordEquiv (Word.consLayer l rest)
    (Word.consBraid (l.belowRight hRight above) (Word.consLayer l.shiftRight
      (Word.consBraid (l.aboveRight hRight above) rest)))
  | l1Left : {A B Left : Obj} → {x : C} → {rest : Word B _} →
    (above : Bool) → (l : Layer A B) → {hLeft : l.left = Left ++ [x]} →
    WordEquiv (Word.consLayer l rest)
    (Word.consBraid (l.belowLeft hLeft above) (Word.consLayer l.shiftLeft
      (Word.consBraid (l.aboveLeft hLeft above) rest)))

  -- | l1Right : (l.leftOf l') → WordEquiv (Word.consLayer l Word.empty)
  --   (Word.consBraid sorry (Word.consLayer l' (Word.consBraid sorry Word.empty)))

-- inductive Hom : Obj → Obj → Type u
--   | id (A) : Hom A A -- Page 7
--   | comp {A B C} (x : Hom A B) (y : Hom B C) : Hom A C -- Page 7
--   | tensor {A B C D} (x : Hom A B) (y : Hom C D) : Hom (A.tensor C) (B.tensor D) -- Page 8
--   -- σ is defined in terms of Δ
--   | Δ (A) : Hom A A.flip -- Page 9
--   | Δ_inv (A) : Hom A.flip A -- Page 9
--   | box (A B) : A.length >= 1 → B.length >= 2 → Hom A B -- Page 10

-- def σ {A B : F C} : Hom (A.tensor B) (B.tensor A) := by
--   simpa using (Hom.Δ (A.tensor B)).comp
--     ((Hom.Δ_inv B).tensor (Hom.Δ_inv A))

-- /-- Formal compositions and tensor products of identities, unitors and associators. The morphisms
-- of the free monoidal category are obtained as a quotient of these formal morphisms by the
-- relations defining a monoidal category. -/
-- inductive BoringHom : F C → F C → Type u
--   | id (X) : BoringHom X X
--   | blah (Y) : BoringHom Y Y
--   | α_BoringHom (X Y Z : F C) : BoringHom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
--   | α_inv (X Y Z : F C) : BoringHom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
--   | l_BoringHom (X) : BoringHom (unit.tensor X) X
--   | l_inv (X) : BoringHom X (unit.tensor X)
--   | ρ_BoringHom (X : F C) : BoringHom (X.tensor unit) X
--   | ρ_inv (X : F C) : BoringHom X (X.tensor unit)
--   | comp {X Y Z} (f : BoringHom X Y) (g : BoringHom Y Z) : BoringHom X Z
--   | whiskerLeft (X : F C) {Y₁ Y₂} (f : BoringHom Y₁ Y₂) : BoringHom (X.tensor Y₁) (X.tensor Y₂)
--   | whiskerRight {X₁ X₂} (f : BoringHom X₁ X₂) (Y : F C) : BoringHom (X₁.tensor Y) (X₂.tensor Y)
--   | tensor {W X Y Z} (f : BoringHom W Y) (g : BoringHom X Z) : BoringHom (W.tensor X) (Y.tensor Z)

-- local infixr:10 " ⟶ᵐ " => BoringHom

-- /-- The morphisms of the free monoidal category satisfy 21 relations ensuring that the resulting
-- category is in fact a category and that it is monoidal. -/
-- inductive BoringHomEquiv : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
--   | refl {X Y} (f : X ⟶ᵐ Y) : BoringHomEquiv f f
--   | symm {X Y} (f g : X ⟶ᵐ Y) : BoringHomEquiv f g → BoringHomEquiv g f
--   | trans {X Y} {f g h : X ⟶ᵐ Y} : BoringHomEquiv f g → BoringHomEquiv g h → BoringHomEquiv f h
--   | comp {X Y Z} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} :
--       BoringHomEquiv f f' → BoringHomEquiv g g' → BoringHomEquiv (f.comp g) (f'.comp g')
--   | whiskerLeft (X) {Y Z} (f f' : Y ⟶ᵐ Z) :
--       BoringHomEquiv f f' → BoringHomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
--   | whiskerRight {Y Z} (f f' : Y ⟶ᵐ Z) (X) :
--       BoringHomEquiv f f' → BoringHomEquiv (f.whiskerRight X) (f'.whiskerRight X)
--   | tensor {W X Y Z} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} :
--       BoringHomEquiv f f' → BoringHomEquiv g g' → BoringHomEquiv (f.tensor g) (f'.tensor g')
--   | tensorBoringHom_def {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
--       BoringHomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
--   | comp_id {X Y} (f : X ⟶ᵐ Y) : BoringHomEquiv (f.comp (BoringHom.id _)) f
--   | id_comp {X Y} (f : X ⟶ᵐ Y) : BoringHomEquiv ((BoringHom.id _).comp f) f
--   | assoc {X Y U V : F C} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) :
--       BoringHomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
--   | id_tensorBoringHom_id {X Y} : BoringHomEquiv ((BoringHom.id X).tensor (BoringHom.id Y)) (BoringHom.id _)
--   | tensorBoringHom_comp_tensorBoringHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂)
--       (g₁ : Y₁ ⟶ᵐ Z₁) (g₂ : Y₂ ⟶ᵐ Z₂) :
--     BoringHomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
--   | whiskerLeft_id (X Y) : BoringHomEquiv ((BoringHom.id Y).whiskerLeft X) (BoringHom.id (X.tensor Y))
--   | id_whiskerRight (X Y) : BoringHomEquiv ((BoringHom.id X).whiskerRight Y) (BoringHom.id (X.tensor Y))
--   | α_BoringHom_inv {X Y Z} : BoringHomEquiv ((BoringHom.α_BoringHom X Y Z).comp (BoringHom.α_inv X Y Z)) (BoringHom.id _)
--   | α_inv_BoringHom {X Y Z} : BoringHomEquiv ((BoringHom.α_inv X Y Z).comp (BoringHom.α_BoringHom X Y Z)) (BoringHom.id _)
--   | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) :
--       BoringHomEquiv (((f₁.tensor f₂).tensor f₃).comp (BoringHom.α_BoringHom Y₁ Y₂ Y₃))
--         ((BoringHom.α_BoringHom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
--   | ρ_BoringHom_inv {X} : BoringHomEquiv ((BoringHom.ρ_BoringHom X).comp (BoringHom.ρ_inv X)) (BoringHom.id _)
--   | ρ_inv_BoringHom {X} : BoringHomEquiv ((BoringHom.ρ_inv X).comp (BoringHom.ρ_BoringHom X)) (BoringHom.id _)
--   | ρ_naturality {X Y} (f : X ⟶ᵐ Y) :
--       BoringHomEquiv ((f.whiskerRight unit).comp (BoringHom.ρ_BoringHom Y)) ((BoringHom.ρ_BoringHom X).comp f)
--   | l_BoringHom_inv {X} : BoringHomEquiv ((BoringHom.l_BoringHom X).comp (BoringHom.l_inv X)) (BoringHom.id _)
--   | l_inv_BoringHom {X} : BoringHomEquiv ((BoringHom.l_inv X).comp (BoringHom.l_BoringHom X)) (BoringHom.id _)
--   | l_naturality {X Y} (f : X ⟶ᵐ Y) :
--       BoringHomEquiv ((f.whiskerLeft unit).comp (BoringHom.l_BoringHom Y)) ((BoringHom.l_BoringHom X).comp f)
--   | pentagon {W X Y Z} :
--       BoringHomEquiv
--         (((BoringHom.α_BoringHom W X Y).whiskerRight Z).comp
--           ((BoringHom.α_BoringHom W (X.tensor Y) Z).comp ((BoringHom.α_BoringHom X Y Z).whiskerLeft W)))
--         ((BoringHom.α_BoringHom (W.tensor X) Y Z).comp (BoringHom.α_BoringHom W X (Y.tensor Z)))
--   | triangle {X Y} :
--       BoringHomEquiv ((BoringHom.α_BoringHom X unit Y).comp ((BoringHom.l_BoringHom Y).whiskerLeft X))
--         ((BoringHom.ρ_BoringHom X).whiskerRight Y)

-- /-- We say that two formal morphisms in the free monoidal category are equivalent if they become
-- equal if we apply the relations that are true in a monoidal category. Note that we will prove
-- that there is only one equivalence class -- this is the monoidal coherence theorem. -/
-- def setoidBoringHom (X Y : F C) : Setoid (X ⟶ᵐ Y) :=
--   ⟨BoringHomEquiv, ⟨BoringHomEquiv.refl, BoringHomEquiv.symm _ _, BoringHomEquiv.trans⟩⟩

-- attribute [instance] setoidBoringHom

-- section

-- open FreeMonoidalCategory.BoringHomEquiv

-- instance categoryFreeMonoidalCategory : Category.{u} (F C) where
--   BoringHom X Y := Quotient (FreeMonoidalCategory.setoidBoringHom X Y)
--   id X := ⟦BoringHom.id X⟧
--   comp := Quotient.map₂ BoringHom.comp (fun _ _ hf _ _ hg ↦ BoringHomEquiv.comp hf hg)
--   id_comp := by
--     rintro X Y ⟨f⟩
--     exact Quotient.sound (id_comp f)
--   comp_id := by
--     rintro X Y ⟨f⟩
--     exact Quotient.sound (comp_id f)
--   assoc := by
--     rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
--     exact Quotient.sound (assoc f g h)

-- instance : MonoidalCategory (F C) where
--   tensorObj X Y := FreeMonoidalCategory.tensor X Y
--   tensorBoringHom := Quotient.map₂ BoringHom.tensor (fun _ _ hf _ _ hg ↦ BoringHomEquiv.tensor hf hg)
--   whiskerLeft X _ _ f := Quot.map (fun f ↦ BoringHom.whiskerLeft X f) (fun f f' ↦ .whiskerLeft X f f') f
--   whiskerRight f Y := Quot.map (fun f ↦ BoringHom.whiskerRight f Y) (fun f f' ↦ .whiskerRight f f' Y) f
--   tensorBoringHom_def {W X Y Z} := by
--     rintro ⟨f⟩ ⟨g⟩
--     exact Quotient.sound (tensorBoringHom_def _ _)
--   id_tensorBoringHom_id _ _ := Quot.sound id_tensorBoringHom_id
--   tensorBoringHom_comp_tensorBoringHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} := by
--     rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
--     exact Quotient.sound (tensorBoringHom_comp_tensorBoringHom _ _ _ _)
--   whiskerLeft_id X Y := Quot.sound (BoringHomEquiv.whiskerLeft_id X Y)
--   id_whiskerRight X Y := Quot.sound (BoringHomEquiv.id_whiskerRight X Y)
--   tensorUnit := FreeMonoidalCategory.unit
--   associator X Y Z :=
--     ⟨⟦BoringHom.α_BoringHom X Y Z⟧, ⟦BoringHom.α_inv X Y Z⟧, Quotient.sound α_BoringHom_inv, Quotient.sound α_inv_BoringHom⟩
--   associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} := by
--     rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
--     exact Quotient.sound (associator_naturality _ _ _)
--   leftUnitor X := ⟨⟦BoringHom.l_BoringHom X⟧, ⟦BoringHom.l_inv X⟧, Quotient.sound l_BoringHom_inv, Quotient.sound l_inv_BoringHom⟩
--   leftUnitor_naturality {X Y} := by
--     rintro ⟨f⟩
--     exact Quotient.sound (l_naturality _)
--   rightUnitor X :=
--     ⟨⟦BoringHom.ρ_BoringHom X⟧, ⟦BoringHom.ρ_inv X⟧, Quotient.sound ρ_BoringHom_inv, Quotient.sound ρ_inv_BoringHom⟩
--   rightUnitor_naturality {X Y} := by
--     rintro ⟨f⟩
--     exact Quotient.sound (ρ_naturality _)
--   pentagon _ _ _ _ := Quotient.sound pentagon
--   triangle _ _ := Quotient.sound triangle

-- @[simp]
-- theorem mk_comp {X Y Z : F C} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z) :
--     ⟦f.comp g⟧ = @CategoryStruct.comp (F C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
--   rfl

-- @[simp]
-- theorem mk_tensor {X₁ Y₁ X₂ Y₂ : F C} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
--     ⟦f.tensor g⟧ = @MonoidalCategory.tensorBoringHom (F C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
--   rfl

-- @[simp]
-- theorem mk_whiskerLeft (X : F C) {Y₁ Y₂ : F C} (f : Y₁ ⟶ᵐ Y₂) :
--     ⟦f.whiskerLeft X⟧ = MonoidalCategory.whiskerLeft (C := F C) (X := X) (f := ⟦f⟧) :=
--   rfl

-- @[simp]
-- theorem mk_whiskerRight {X₁ X₂ : F C} (f : X₁ ⟶ᵐ X₂) (Y : F C) :
--     ⟦f.whiskerRight Y⟧ = MonoidalCategory.whiskerRight (C := F C) (f := ⟦f⟧) (Y := Y) :=
--   rfl

-- @[simp]
-- theorem mk_id {X : F C} : ⟦BoringHom.id X⟧ = 𝟙 X :=
--   rfl

-- @[simp]
-- theorem mk_α_BoringHom {X Y Z : F C} : ⟦BoringHom.α_BoringHom X Y Z⟧ = (α_ X Y Z).BoringHom :=
--   rfl

-- @[simp]
-- theorem mk_α_inv {X Y Z : F C} : ⟦BoringHom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
--   rfl

-- @[simp]
-- theorem mk_ρ_BoringHom {X : F C} : ⟦BoringHom.ρ_BoringHom X⟧ = (ρ_ X).BoringHom :=
--   rfl

-- @[simp]
-- theorem mk_ρ_inv {X : F C} : ⟦BoringHom.ρ_inv X⟧ = (ρ_ X).inv :=
--   rfl

-- @[simp]
-- theorem mk_l_BoringHom {X : F C} : ⟦BoringHom.l_BoringHom X⟧ = (λ_ X).BoringHom :=
--   rfl

-- @[simp]
-- theorem mk_l_inv {X : F C} : ⟦BoringHom.l_inv X⟧ = (λ_ X).inv :=
--   rfl

-- @[simp]
-- theorem tensor_eq_tensor {X Y : F C} : X.tensor Y = X ⊗ Y :=
--   rfl

-- @[simp]
-- theorem unit_eq_unit : FreeMonoidalCategory.unit = 𝟙_ (F C) :=
--   rfl

-- /-- The abbreviation for `⟦f⟧`. -/
-- /- This is useful since the notation `⟦f⟧` often behaves like an element of the quotient set,
-- but not like a morphism. This is why we need weird `@CategoryStruct.comp (F C) ...` in the
-- statement in `mk_comp` above. -/
-- abbrev BoringHomMk {X Y : F C} (f : X ⟶ᵐ Y) : X ⟶ Y := ⟦f⟧

-- theorem BoringHom.inductionOn {motive : {X Y : F C} → (X ⟶ Y) → Prop} {X Y : F C} (t : X ⟶ Y)
--     (id : (X : F C) → motive (𝟙 X))
--     (α_BoringHom : (X Y Z : F C) → motive (α_ X Y Z).BoringHom)
--     (α_inv : (X Y Z : F C) → motive (α_ X Y Z).inv)
--     (l_BoringHom : (X : F C) → motive (λ_ X).BoringHom)
--     (l_inv : (X : F C) → motive (λ_ X).inv)
--     (ρ_BoringHom : (X : F C) → motive (ρ_ X).BoringHom)
--     (ρ_inv : (X : F C) → motive (ρ_ X).inv)
--     (comp : {X Y Z : F C} → (f : X ⟶ Y) → (g : Y ⟶ Z) → motive f → motive g → motive (f ≫ g))
--     (whiskerLeft : (X : F C) → {Y Z : F C} → (f : Y ⟶ Z) → motive f → motive (X ◁ f))
--     (whiskerRight : {X Y : F C} → (f : X ⟶ Y) → (Z : F C) → motive f → motive (f ▷ Z)) :
--     motive t := by
--   apply Quotient.inductionOn
--   intro f
--   induction f with
--   | id X => exact id X
--   | α_BoringHom X Y Z => exact α_BoringHom X Y Z
--   | α_inv X Y Z => exact α_inv X Y Z
--   | l_BoringHom X => exact l_BoringHom X
--   | l_inv X => exact l_inv X
--   | ρ_BoringHom X => exact ρ_BoringHom X
--   | ρ_inv X => exact ρ_inv X
--   | comp f g hf hg => exact comp _ _ (hf ⟦f⟧) (hg ⟦g⟧)
--   | whiskerLeft X f hf => exact whiskerLeft X _ (hf ⟦f⟧)
--   | whiskerRight f X hf => exact whiskerRight _ X (hf ⟦f⟧)
--   | @tensor W X Y Z f g hf hg =>
--       have : BoringHomMk f ⊗ₘ BoringHomMk g = BoringHomMk f ▷ X ≫ Y ◁ BoringHomMk g :=
--         Quotient.sound (BoringHomEquiv.tensorBoringHom_def f g)
--       change motive (BoringHomMk f ⊗ₘ BoringHomMk g)
--       rw [this]
--       exact comp _ _ (whiskerRight _ _ (hf ⟦f⟧)) (whiskerLeft _ _ (hg ⟦g⟧))

-- section Functor

-- variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (f : C → D)

-- /-- Auxiliary definition for `free_monoidal_category.project`. -/
-- def projectObj : F C → D
--   | FreeMonoidalCategory.of X => f X
--   | FreeMonoidalCategory.unit => 𝟙_ D
--   | FreeMonoidalCategory.tensor X Y => projectObj X ⊗ projectObj Y

-- section


-- open BoringHom

-- /-- Auxiliary definition for `FreeMonoidalCategory.project`. -/
-- @[simp]
-- def projectMapAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (projectObj f X ⟶ projectObj f Y)
--   | _, _, BoringHom.id _ => 𝟙 _
--   | _, _, α_BoringHom _ _ _ => (α_ _ _ _).BoringHom
--   | _, _, α_inv _ _ _ => (α_ _ _ _).inv
--   | _, _, l_BoringHom _ => (λ_ _).BoringHom
--   | _, _, l_inv _ => (λ_ _).inv
--   | _, _, ρ_BoringHom _ => (ρ_ _).BoringHom
--   | _, _, ρ_inv _ => (ρ_ _).inv
--   | _, _, BoringHom.comp f g => projectMapAux f ≫ projectMapAux g
--   | _, _, BoringHom.whiskerLeft X p => projectObj f X ◁ projectMapAux p
--   | _, _, BoringHom.whiskerRight p X => projectMapAux p ▷ projectObj f X
--   | _, _, BoringHom.tensor f g => projectMapAux f ⊗ₘ projectMapAux g

-- /-- Auxiliary definition for `FreeMonoidalCategory.project`. -/
-- @[simp]
-- def projectMap (X Y : F C) : (X ⟶ Y) → (projectObj f X ⟶ projectObj f Y) :=
--   Quotient.lift (projectMapAux f) <| by
--     intro f g h
--     induction h with
--     | refl => rfl
--     | symm _ _ _ hfg' => exact hfg'.symm
--     | trans _ _ hfg hgh => exact hfg.trans hgh
--     | comp _ _ hf hg => dsimp only [projectMapAux]; rw [hf, hg]
--     | whiskerLeft _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
--     | whiskerRight _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
--     | tensor _ _ hfg hfg' => dsimp only [projectMapAux]; rw [hfg, hfg']
--     | tensorBoringHom_def _ _ =>
--         dsimp only [projectMapAux, projectObj]; rw [MonoidalCategory.tensorBoringHom_def]
--     | comp_id => dsimp only [projectMapAux]; rw [Category.comp_id]
--     | id_comp => dsimp only [projectMapAux]; rw [Category.id_comp]
--     | assoc => dsimp only [projectMapAux]; rw [Category.assoc]
--     | id_tensorBoringHom_id => dsimp only [projectMapAux]; rw [MonoidalCategory.id_tensorBoringHom_id]; rfl
--     | tensorBoringHom_comp_tensorBoringHom =>
--       dsimp only [projectMapAux]; rw [MonoidalCategory.tensorBoringHom_comp_tensorBoringHom]
--     | whiskerLeft_id =>
--         dsimp only [projectMapAux, projectObj]
--         rw [MonoidalCategory.whiskerLeft_id]
--     | id_whiskerRight =>
--         dsimp only [projectMapAux, projectObj]
--         rw [MonoidalCategory.id_whiskerRight]
--     | α_BoringHom_inv => dsimp only [projectMapAux]; rw [Iso.BoringHom_inv_id]
--     | α_inv_BoringHom => dsimp only [projectMapAux]; rw [Iso.inv_BoringHom_id]
--     | associator_naturality =>
--         dsimp only [projectMapAux]; rw [MonoidalCategory.associator_naturality]
--     | ρ_BoringHom_inv => dsimp only [projectMapAux]; rw [Iso.BoringHom_inv_id]
--     | ρ_inv_BoringHom => dsimp only [projectMapAux]; rw [Iso.inv_BoringHom_id]
--     | ρ_naturality =>
--         dsimp only [projectMapAux, projectObj]
--         rw [MonoidalCategory.rightUnitor_naturality]
--     | l_BoringHom_inv => dsimp only [projectMapAux]; rw [Iso.BoringHom_inv_id]
--     | l_inv_BoringHom => dsimp only [projectMapAux]; rw [Iso.inv_BoringHom_id]
--     | l_naturality =>
--         dsimp only [projectMapAux, projectObj]
--         rw [MonoidalCategory.leftUnitor_naturality]
--     | pentagon =>
--         dsimp only [projectMapAux, projectObj]
--         rw [MonoidalCategory.pentagon]
--     | triangle =>
--         dsimp only [projectMapAux, projectObj]
--         rw [MonoidalCategory.triangle]

-- end

-- /-- If `D` is a monoidal category and we have a function `C → D`, then we have a
-- monoidal functor from the free monoidal category over `C` to the category `D`. -/
-- def project : F C ⥤ D where
--   obj := projectObj f
--   map := projectMap f _ _
--   map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

-- instance : (project f).Monoidal :=
--   Functor.CoreMonoidal.toMonoidal
--     { εIso := Iso.refl _
--       μIso := fun _ _ ↦ Iso.refl _
--   -- Porting note: `μIso_BoringHom_natural_left` was proved in mathlib3 by tidy, using induction.
--   -- We probably don't expect `cat_disch` to handle this yet, see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases
--       μIso_BoringHom_natural_left := fun f _ => by
--         induction f using Quotient.recOn
--         all_goals aesop
--       μIso_BoringHom_natural_right := fun _ f => by
--         induction f using Quotient.recOn
--         all_goals aesop }

-- end Functor

-- end

end FreeMonoidalCategory

end CategoryTheory
