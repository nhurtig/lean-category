import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

-- TODO generalize to have any Box to strengthen our result.
-- We're just gonna force it to use our myBoxInfo for now because
-- it's easier.

-- class Box (BoxInfo : Type) where
--   dom : BoxInfo → ℕ
--   cod : BoxInfo → ℕ
--   hdom : ∀ b, dom b > 0 := by grind
--   hcod : ∀ b, cod b > 1 := by grind

-- TODO figure out how to use dot notation on anything that derives Box
-- notation b ".mydom" => Box.dom b
-- notation b ".cod" => Box.cod b
-- abbrev BoxInfo.mydom {BoxInfo : Type} [Box BoxInfo] (b : BoxInfo) : ℕ := Box.dom b
-- abbrev BoxInfo.cod {BoxInfo : Type} [Box BoxInfo] (b : BoxInfo) : ℕ := Box.cod b

inductive Dir where
| left : Dir
| right : Dir
deriving Repr, DecidableEq

inductive Bed where
| front : Bed
| back : Bed
deriving Repr, DecidableEq

@[grind]
inductive myBoxInfo where
| tuck : Dir → myBoxInfo
| split : (num_carriers : ℕ) → (hc : num_carriers > 0) → (num_loops : ℕ) → (hl : num_loops > 0) →
  Dir → Bed → myBoxInfo
deriving Repr, DecidableEq
-- no drop: that's been laddered out already. Let's just ignore that the drops need to
-- be glued on to the splits for now; TODO don't ignore that

@[simp, grind =]
def myBoxInfo.dom : myBoxInfo → ℕ
  | tuck _ => 1
  | split c _ l _ _ _ => c + 2 * l

@[simp, grind =]
def myBoxInfo.cod : myBoxInfo → ℕ
  | tuck _ => 2
  | split c _ l _ _ _ => 3 * c + 2 * l

-- instance : Box myBoxInfo where
--   dom b := b.dom
--   cod b := b.cod

inductive myMorphism : ℕ → ℕ → Type where
| box : (b : myBoxInfo) → myMorphism b.dom b.cod
| id : (n : ℕ) → myMorphism n n
| comp : myMorphism a b → myMorphism b c → myMorphism a c
-- fun idea: make braid WORDS, up to isomorphism, morphisms.
-- then the slide-past rule... will be... hmmm... ah! Just introduce
-- stuff on either side, done! No need to inspect what's on the
-- top and bottom. Just like how it's presented in the paper; not like
-- how humans usually think about it. THEN we can have the monoidal product
-- not be explicitly represented, but instead be the grid A ⊗ B =
-- I ⊗ B
--   ∘
-- A ⊗ I



instance myCat : Category ℕ where
  Hom := myMorphism
  id := .id

-- Okay, here's what I've learned. We want to write a proof over ALL the twisted involutive monoidal
-- categories, not just our own. It's pretty useless to say that our formalism is a category; our formalism
-- is really just a quotient over the requirements of the category we're saying it is. Big nothing burger.
-- Next goal: define a decision procedure over a free Category ·.
