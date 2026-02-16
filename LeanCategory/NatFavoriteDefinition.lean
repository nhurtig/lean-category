import Mathlib
import LeanCategory.FreeEgger
import LeanCategory.StarMonoid

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

-- another type synonym -- this one for free stuff
@[grind]
structure F where
  val : V

instance : Coe V F where
  coe v := ⟨v⟩

instance : Coe F V where
  coe f := f.val

@[ext]
lemma F.ext {x y : F} : x.val = y.val → x = y := by
  grind

-- it's also a star monoid
instance : StarMonoid F where
  one := (1 : V)
  mul X Y := X.val * Y.val
  mul_assoc A B C := F.ext <| mul_assoc A.val B.val C.val
  one_mul A := F.ext <| one_mul A.val
  mul_one A := F.ext <| mul_one A.val
  star X := ↑X.val⋆
  star_involutive X := F.ext <| star_involutive X.val
  star_mul X Y := F.ext <| StarMonoid.star_mul X.val Y.val

instance empty : Quiver F where
  Hom _ _ := Empty

-- this is just the braids
#synth TwistedCategory (S F)
#synth CategoryStruct (S F)

-- for "N"at's representation. Note this is really silly
@[grind]
structure N where
  val : V

instance : Coe V N where
  coe v := ⟨v⟩

instance : Coe N V where
  coe n := n.val

@[ext]
lemma N.ext {x y : N} : x.val = y.val → x = y := by
  grind

-- it's also a star monoid TODO is this definition used?
instance : StarMonoid N where
  one := (1 : V)
  mul X Y := X.val * Y.val
  mul_assoc A B C := N.ext <| mul_assoc A.val B.val C.val
  one_mul A := N.ext <| one_mul A.val
  mul_one A := N.ext <| mul_one A.val
  star X := ↑X.val⋆
  star_involutive X := N.ext <| star_involutive X.val
  star_mul X Y := N.ext <| StarMonoid.star_mul X.val Y.val

instance {T} : Coe (S T) T where
  coe s := s.val

-- A stitch with a record of the identity strands on its left/right
-- TODO: maybe make two layers -- one for two+ outs, one for one out
structure Layer where
  left : V
  box : BoxInfo
  right : V
  -- hdom : dom = left * box.dom * right := by grind
  -- hcod : cod = left * box.cod * right := by grind

@[simp]
def Layer.dom : Layer → V
  | ⟨left, box, right⟩ => left * box.dom * right

@[simp]
def Layer.cod : Layer → V
  | ⟨left, box, right⟩ => left * box.cod * right

-- TODO universes are a hack
inductive MyHom : N → N → Type 1 where
  | layer : (l : Layer) → MyHom l.dom l.cod
  | braid {X Y : S F} : (X ⟶ Y) → MyHom X Y
  | id (X : N) : MyHom X X
  | comp {X Y Z : N} : MyHom X Y → MyHom Y Z → MyHom X Z

#check CategoryTheory.Cat.isoOfEquiv -- we want to use this

-- TODO try S N if this is a problem
instance : CategoryStruct N where
  Hom := MyHom
  id := .id
  comp := .comp

-- #synth Quiver (S (F V))

-- variable {X Y Z : S (F V)} {b₁ : X ⟶ Y} {b₂ : Y ⟶ Z}

-- TODO: get namespaces set up so we don't do this "my" business
@[grind]
inductive MyHom.equiv : ∀ {X Y : N}, (X ⟶ Y) → (X ⟶ Y) → Prop where
  | refl (f) : MyHom.equiv f f
  | comp {f f' : X ⟶ Y} : MyHom.equiv f f' → MyHom.equiv g g' → MyHom.equiv (f ≫ g) (f' ≫ g')
  | id_comp : MyHom.equiv (𝟙 X ≫ f) f
  | comp_id {f : X ⟶ Y} : MyHom.equiv (f ≫ 𝟙 Y) f
  | assoc : MyHom.equiv ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
  | merge_braid {b₁ : X ⟶ Y} {b₂ : Y ⟶ Z} : MyHom.equiv ((.braid b₁) ≫ (.braid b₂))
      (.braid (Category.toCategoryStruct.comp b₁ b₂))
  | destroy_braid {X} : MyHom.equiv (.braid (Category.toCategoryStruct.id X)) (𝟙 (N.mk X.val.val))
  -- the paper's rules
  | swap {left middle right : V} {b t : BoxInfo} : MyHom.equiv -- TODO: even out eqToHom? 1 ↦ 3 now
      ((.layer ⟨left, b, middle * t.dom * right⟩) ≫
        (eqToHom (by simp [mul_assoc])) ≫
        (.layer ⟨left * b.cod * middle, t, right⟩))
      ((eqToHom (by simp [mul_assoc])) ≫
        (.layer ⟨left * b.dom * middle, t, right⟩) ≫
        (eqToHom (by simp [mul_assoc])) ≫
        (.layer ⟨left, b, middle * t.cod * right⟩) ≫
        (eqToHom (by simp [mul_assoc])))
  -- layer moves
  | symm (f g) : MyHom.equiv f g → MyHom.equiv g f
  | trans {f g h : X ⟶ Y} : MyHom.equiv f g → MyHom.equiv g h → MyHom.equiv f h

instance {X Y} : HasEquiv (MyHom X Y) where
  Equiv := MyHom.equiv

-- -- Q for quotient -- the quotient of N
-- @[grind]
-- structure Q where
--   val : V

-- instance : Coe V Q where
--   coe v := ⟨v⟩

-- instance : Coe Q V where
--   coe n := n.val

-- @[ext]
-- lemma Q.ext {x y : N} : x.val = y.val → x = y := by
--   grind

instance mySetoidHom (X Y : N) : Setoid (X ⟶ Y) :=
⟨MyHom.equiv, ⟨MyHom.equiv.refl, MyHom.equiv.symm _ _, MyHom.equiv.trans⟩⟩

@[grind =_]
lemma MyHom.equiv_def {X Y : N} {f g : X ⟶ Y} : MyHom.equiv f g ↔ f ≈ g := by
  constructor
  all_goals intros h
  all_goals exact h


#synth Quiver N
-- TODO generalize eqToHom_comp
lemma eqToHom_comp' {X Y Z : N} {f : X ⟶ Y} {g : Y ⟶ Z} {p : X = Y} {q : Y = Z} :
    (f ≈ eqToHom p) → (g ≈ eqToHom q) → (f ≫ g) ≈ (eqToHom (p.trans q)) := by
  intros hf hg
  apply MyHom.equiv.trans
  · exact MyHom.equiv.comp hf hg
  · cases p
    cases q
    simp
    grind

#synth Category N

instance : Category N where
  Hom X Y := Quotient (mySetoidHom X Y)
  id X := ⟦𝟙 X⟧
  comp f g := Quotient.map₂ (· ≫ ·) (fun _ _ hf _ _ hg ↦ MyHom.equiv.comp hf hg) f g
  id_comp {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    grind
  comp_id {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    grind
  assoc {W X Y Z} := by
    rintro ⟨f⟩ ⟨g⟩ ⟨h⟩
    apply Quotient.sound
    grind

#synth Quiver N

-- not eqToIso! TODO generalize eqToIso'
def eqToIso'' {X Y : N} (h : X = Y) : X ≅ Y := {
  hom := ⟦eqToHom h⟧
  inv := ⟦eqToHom h.symm⟧
  hom_inv_id := by
    apply Quotient.sound
    exact eqToHom_comp' (by rfl) (by rfl)
  inv_hom_id := by
    apply Quotient.sound
    exact eqToHom_comp' (by rfl) (by rfl)
}

instance : MonoidalCategory N where
  tensorObj X Y := X * Y
  tensorHom f g := Quotient.map₂ (· ⊗ ·) (fun _ _ hf _ _ hg ↦ MyHom.equiv.tensor hf hg) f g
  tensorUnit := 1
  associator X Y Z := eqToIso' (mul_assoc X Y Z)
  leftUnitor X := eqToIso' (one_mul X)
  rightUnitor X := eqToIso' (mul_one X)
  whiskerLeft X {Y₁ Y₂} f := Quotient.map (X ◁ ·) (fun _ _ hf ↦ HomEquiv.whiskerLeft X hf) f
  whiskerRight {X₁ X₂} f Y := Quotient.map (· ▷ Y) (fun _ _ hf ↦ HomEquiv.whiskerRight Y hf) f
  tensorHom_def {X₁ Y₁ X₂ Y₂} := by
    rintro ⟨f⟩ ⟨g⟩
    apply Quotient.sound
    apply HomEquiv.tensorHom_def
  id_tensorHom_id _ _ := Quotient.sound id_tensor_id
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} := by -- TODO can this be sound?
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    apply Quotient.sound
    grind
  whiskerLeft_id X Y := Quotient.sound (HomEquiv.whiskerLeft_id X Y)
  id_whiskerRight X Y := Quotient.sound (HomEquiv.id_whiskerRight X Y)
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    apply Quotient.sound
    grind
  leftUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    grind
  rightUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    grind
  pentagon W X Y Z := by
    apply Quotient.sound
    eqToHom_eq_eqToHom
  triangle X Y := by
    apply Quotient.sound
    eqToHom_eq_eqToHom

-- then an isomorphism of categories between the one on N and the one on S V

#check Functor.Monoidal
