import Mathlib
import LeanCategory.FreeEgger

open CategoryTheory

def Carrier := ℕ
deriving Repr, DecidableEq
def Loop := ℕ
deriving Repr, DecidableEq

def Strand := Carrier ⊕ Loop
deriving Repr, DecidableEq

def V := List Strand
deriving Repr, DecidableEq

instance : Coe (List Carrier) V where
  coe X := X.map Sum.inl

instance : Coe (List Loop) V where
  coe X := X.map Sum.inr

def List.toLoops : List Carrier → V :=
  List.map Sum.inr

instance instV_StarMonoid : StarMonoid V where
  mul := List.append
  mul_assoc := List.append_assoc
  one := List.nil
  one_mul := List.nil_append
  mul_one := List.append_nil
  star := List.reverse
  star_involutive := List.reverse_reverse
  star_mul _ _ := List.reverse_append

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
-- all tucks are in the + (aka right) direction
| tuck : (carriers : List Carrier) → BoxInfo
-- all splits are in the + direction -- they're rotated by the twist
| split : (carriers : List Carrier) → (loops : List Loop) → Bed → BoxInfo
deriving Repr, DecidableEq
-- no drop: that's been laddered out already. Let's just ignore that the drops need to
-- be glued on to the splits for now; TODO don't ignore that

@[simp, grind =]
def BoxInfo.dom : BoxInfo → V
  | tuck c => c
  | split c l _ => ↑c * ↑l -- TODO might want to change this depending on the bed

@[simp, grind =]
def BoxInfo.cod : BoxInfo → V
  | tuck c => c.toLoops * ↑c -- new loops, carriers
  | split c l .front => ↑c * ↑l * ↑c -- new loops @ front, xfered loops @ back, carrier
  | split c l .back => ↑l * ↑c * ↑c -- xfered loops @ front, new loops @ back, carrier

instance stitches : Quiver V where
  Hom X Y := { b : BoxInfo // b.dom = X ∧ b.cod = Y }

-- this is our category!!! Well, the twist on carriers is the identity, but close enough
#synth TwistedCategory (S V)

-- A stitch with a record of the identity strands on its left/right
-- TODO: maybe make two layers -- one for two+ outs, one for one out
structure Layer (dom cod : V) where
  left : V
  box : BoxInfo
  right : V
  hdom : dom = left * box.dom * right := by grind
  hcod : cod = left * box.cod * right := by grind

-- another type synonym -- this one for free stuff
def F := V

-- it's also a star monoid
instance : StarMonoid F := instV_StarMonoid

instance empty : Quiver F where
  Hom _ _ := Empty

-- this is just the braids
#synth TwistedCategory (S F)

#synth Quiver (S F)

-- for "N"at's representation
def N := V

-- TODO universes are a hack
inductive MyHom : N → N → Type 1 where
  | layer {X Y : V} : Layer X Y → MyHom X Y
  | braid {X Y : S F} : (X ⟶ Y) → MyHom X Y
  | id X : MyHom X X
  | comp : MyHom X Y → MyHom Y Z → MyHom X Z

#synth Quiver (S F)
#synth Category (S F)
#synth CategoryStruct (S F)

instance : CategoryStruct N where
  Hom := MyHom
  id := .id
  comp := .comp

inductive MyHom.equiv : ∀ {X Y : N}, (X ⟶ Y) → (X ⟶ Y) → Prop where
  | refl : MyHom.equiv f f
  | comp {f f' : X ⟶ Y} : MyHom.equiv f f' → MyHom.equiv g g' → MyHom.equiv (f ≫ g) (f' ≫ g')
  | id_comp : MyHom.equiv (𝟙 X ≫ f) f
  | comp_id {f : X ⟶ Y} : MyHom.equiv (f ≫ 𝟙 Y) f
  | assoc : MyHom.equiv ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
  | merge_braid {b₁ : X ⟶ Y} {b₂ : Y ⟶ Z} : MyHom.equiv ((.braid b₁) ≫ (.braid b₂)) (.braid (b₁ ≫ b₂))
  | destroy_braid : MyHom.equiv (f ≫ (.braid (𝟙 _)) ≫ g) (f ≫ g)
  -- the paper's rules
  -- swap
  -- layer moves
  | symm : MyHom.equiv f g → MyHom.equiv g f
  | trans : MyHom.equiv f g → MyHom.equiv g h → MyHom.equiv f h

instance {X Y} : HasEquiv (MyHom X Y) where
  Equiv := sorry

-- then some sort of equivalence of categories between the one on N and the one on S V
