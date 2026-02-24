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

-- Canonical means we've quotiented up to rotation
@[grind]
inductive CanonicalStitch where
-- all tucks are in the + (aka right) direction
| tuck : (carriers : List Carrier) → CanonicalStitch
-- all splits are in the + direction -- they're rotated by the twist
| split : (carriers : List Carrier) → (loops : List Loop) → Bed → CanonicalStitch
deriving Repr, DecidableEq
-- no drop: that's been laddered out already. Let's just ignore that the drops need to
-- be glued on to the splits for now; TODO don't ignore that

@[grind =]
def CanonicalStitch.dom : CanonicalStitch → V
  | tuck c => c
  | split c l _ => ↑c * ↑l -- TODO might want to change this depending on the bed

@[grind =]
def CanonicalStitch.cod : CanonicalStitch → V
  | tuck c => c.toLoops * ↑c -- new loops, carriers
  | split c l .front => ↑c * ↑l * ↑c -- new loops @ front, xfered loops @ back, carrier
  | split c l .back => ↑l * ↑c * ↑c -- xfered loops @ front, new loops @ back, carrier

instance : Quiver V where
  Hom X Y := { b : CanonicalStitch // b.dom = X ∧ b.cod = Y }

-- this is our category!!! Well, the twist on carriers is the identity, but close enough
#synth TwistedCategory (S V)

-- bool records whether it's in its original rotation (False) or has been starred (True)
def Stitch := CanonicalStitch × Bool

instance : Star Stitch where
  star | (s, b) => (s, !b)

@[simp]
def Stitch.dom : Stitch → V
  | (s, false) => s.dom
  | (s, true) => s.dom⋆

@[simp]
def Stitch.cod : Stitch → V
  | (s, false) => s.cod
  | (s, true) => s.cod⋆

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

@[simp]
lemma N.mul_val {X Y : N} : (X * Y : N) = N.mk (X.val * Y.val) := rfl

-- attribute [simp] mul

instance {T} : Coe (S T) T where
  coe s := s.val

#check Monoid
-- A CanonicalStitch with a record of the identity strands on its left/right
-- TODO: maybe make two layers -- one for two+ outs, one for one out
structure Layer where
  left : V
  box : Stitch
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
  -- | id (X : N) : MyHom X X -- just use braid's id!
  | comp {X Y Z : N} : MyHom X Y → MyHom Y Z → MyHom X Z

#check CategoryTheory.Cat.isoOfEquiv -- we want to use this

#synth Category (S F)

instance : Coe N (S F) where
  coe n := ⟨⟨n.val⟩⟩

-- try S N if this is a problem
-- TODO make the CategoryStruct' typeclass with the ' notation
-- then monoidalstruct', involutivestruct', twistedstruct'...
instance (priority := 100) : CategoryStruct N where
  Hom := MyHom
  id (X : N) := .braid (𝟙 ↑X)
  comp := .comp

open MonoidalCategory
@[simp, grind]
def MyHom.whisker (X : N) {Y₁ Y₂ : N} : (Y₁ ⟶ Y₂) → (Z : N) → ((X * (Y₁ * Z)) ⟶ (X * (Y₂ * Z)))
  | .layer l, Z => (eqToHom (by simp [mul_assoc])) ≫
      (.layer ⟨X * l.left, l.box, l.right * Z⟩) ≫ (eqToHom (by simp [mul_assoc]))
  | .braid b, Z => .braid (↑X ◁ b ▷ ↑Z)
  -- | .id Y, Z => 𝟙 (X * Y * Z)
  | .comp f g, Z => (whisker X f Z) ≫ (whisker X g Z)

#synth Quiver N

@[simp, grind]
def MyHom.whiskerLeft (X : N) {Y₁ Y₂ : N} (f : Y₁ ⟶ Y₂) : ((X * Y₁) ⟶ (X * Y₂)) :=
  eqToHom (by simp) ≫ MyHom.whisker X f 1 ≫ eqToHom (by simp)

@[simp, grind]
def MyHom.whiskerRight {X₁ X₂ : N} (f : X₁ ⟶ X₂) (Y : N) : ((X₁ * Y) ⟶ (X₂ * Y)) :=
  -- eqToHom (by simp) ≫ MyHom.whisker 1 f Y ≫ eqToHom (by simp)
  MyHom.whisker 1 f Y

@[simp, grind]
def MyHom.tensor {X₁ X₂ Y₁ Y₂ : N} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (X₁ * X₂) ⟶ (Y₁ * Y₂) :=
  (whiskerRight f X₂) ≫ (whiskerLeft Y₁ g)

open CategoryTheory.InvolutiveCategory -- for the ⋆ notation

@[simp, grind]
def MyHom.star {X Y : N} : (X ⟶ Y) → (X⋆ ⟶ Y⋆)
  | .layer l => (eqToHom (by simp [HMul.hMul, Mul.mul, Star.star]; grind)) ≫
      .layer ⟨l.right⋆, l.box⋆, l.left⋆⟩ ≫
      (eqToHom (by simp [HMul.hMul, Mul.mul, Star.star]; grind))
  | .braid b => .braid b⋆
  | .comp f g => (star f) ≫ (star g)

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
      (.braid (b₁ ≫ b₂))
  | destroy_braid {X} : MyHom.equiv (.braid (𝟙 X)) (𝟙 (N.mk X.val.val))
  -- the paper's rules
  | swap {left middle right : V} {b t : Stitch} : MyHom.equiv -- TODO: even out eqToHom? 1 ↦ 3 now
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

instance {X Y : N} : HasEquiv (MyHom X Y) where
  Equiv := MyHom.equiv

instance {X Y : N} : HasEquiv (X ⟶ Y) where
  Equiv := MyHom.equiv

attribute [grind →] MyHom.equiv.comp

@[grind =_]
lemma MyHom.equiv_def {X Y : N} {f g : X ⟶ Y} : MyHom.equiv f g ↔ f ≈ g := by
  constructor
  all_goals intros h
  all_goals exact h

@[grind =_]
lemma MyHom.equiv_def' {X Y : N} {f g : MyHom X Y} : MyHom.equiv f g ↔ f ≈ g := by
  constructor
  all_goals intros h
  all_goals exact h

open CategoryTheory.MonoidalCategory
#check CategoryTheory.MonoidalCategory

lemma MyHom.equiv.braid {X Y : S F} {b b' : X ⟶ Y} :
    b = b' → (MyHom.braid b) ≈ (MyHom.braid b') := by
  grind

lemma MyHom.equiv.braid_eqToHom {X Y : S F} {Y' : N} {b : X ⟶ Y} {h : (N.mk (Y.val.val)) = Y'} :
    (MyHom.braid b) ≫ eqToHom h ≈
      (MyHom.braid (b ≫ eqToHom (by change Y = ↑Y'; aesop))) := by
  cases h
  constructor

lemma MyHom.equiv.eqToHom_braid {X Y : S F} (b : X ⟶ Y) (X' : N) (h : X' = _) :
    eqToHom h ≫ (MyHom.braid b) ≈
      (MyHom.braid (eqToHom (by change ↑X'.val = X; aesop) ≫ b)) := by
  cases h
  constructor

instance mySetoidHom (X Y : N) : Setoid (X ⟶ Y) :=
⟨MyHom.equiv, ⟨MyHom.equiv.refl, MyHom.equiv.symm _ _, MyHom.equiv.trans⟩⟩

@[simp, grind]
lemma MyHom.equiv.whisker_eqToHom (X : N) {Y₁ Y₂ : N} {h : Y₁ = Y₂} (Z : N) :
    MyHom.whisker X (eqToHom h) Z ≈ eqToHom (by simp [h]) := by
  aesop

-- hmmm... maybe it's easier to define this stuff on the quotient directly so we can work
-- with equality instead of ≈: congruence and rw/simp are automatic
@[grind]
lemma MyHom.equiv.whisker (X : N) {Y₁ Y₂ : N} {f f' : Y₁ ⟶ Y₂} (h : f ≈ f') (Z : N) : (MyHom.whisker X f Z) ≈ (MyHom.whisker X f' Z) := by
  induction h
  any_goals simp
  case swap =>
    -- reassociate
    -- merge the eqToHoms (whisker of eqToHom is an eqToHom)
    -- rewrite just the bit between the eqToHom with swap
    -- merge the eqToHoms again
    -- done!
    sorry
  any_goals constructor <;> done
  all_goals grind

@[grind]
lemma MyHom.equiv.whiskerLeft (X : N) {Y₁ Y₂ : N} {f f' : Y₁ ⟶ Y₂} (h : f ≈ f') :
    (MyHom.whiskerLeft X f) ≈ (MyHom.whiskerLeft X f') := by
  apply comp (refl _)
  apply comp ?_ (refl _)
  exact MyHom.equiv.whisker X h 1

@[grind]
lemma MyHom.equiv.whiskerRight {X₁ X₂ : N} (Y : N) {f f' : X₁ ⟶ X₂} (h : f ≈ f') :
    (MyHom.whiskerRight f Y) ≈ (MyHom.whiskerRight f' Y) :=
  MyHom.equiv.whisker 1 h Y

@[grind]
lemma MyHom.equiv.tensor {X₁ X₂ Y₁ Y₂ : N} {f f' : X₁ ⟶ Y₁} {g g' : X₂ ⟶ Y₂} : f ≈ f' → g ≈ g' →
    (MyHom.tensor f g) ≈ (MyHom.tensor f' g') := by
  intros hf hg
  constructor
  · exact MyHom.equiv.whiskerRight X₂ hf
  · exact MyHom.equiv.whiskerLeft Y₁ hg

@[grind]
lemma MyHom.equiv.star {X Y : N} {f f' : X ⟶ Y} (h : f ≈ f') :
    (MyHom.star f) ≈ (MyHom.star f') := by
  induction h
  any_goals simp
  any_goals constructor <;> done
  case swap =>
    -- probably similar to the swap case in whisker: merge eqToHom, swap, merge eqToHom
    sorry
  all_goals grind
  -- all_goals grind

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

#check MonoidalCategory.whiskerRight

-- after checking out the moonoidal category definition, this equality is backwards
-- also maybe we should balance out the eqToHoms on either side
-- also why do we need this? It follows from monoidal stuff; we shouldn't NEED it for
-- defining monoidal, right?
-- @[simp, grind]
-- lemma MyHom.equiv.whisker_whisker (X₁ X₂ : N) {Y₁ Y₂ : N} (f : MyHom Y₁ Y₂) (Z₁ Z₂ : N) :
--     MyHom.whisker X₁ (MyHom.whisker X₂ f Z₁) Z₂ ≈
--       eqToHom (by simp [mul_assoc]) ≫ MyHom.whisker (X₁ * X₂) f (Z₁ * Z₂) ≫ eqToHom (by simp [mul_assoc]) := by
--   induction f
--   all_goals simp
--   -- case id =>
--   --   -- TODO this calls for reduction tactic
--   --   apply MyHom.equiv.symm
--   --   apply eqToHom_comp'
--   --   · apply MyHom.equiv.refl
--   --   · apply eqToHom_comp'
--   --     · apply MyHom.equiv.refl
--   --     · apply MyHom.equiv.refl
--   --     · rfl
--   case comp f g =>
--     apply MyHom.equiv.trans
--     · exact MyHom.equiv.comp f g
--     · simp
--       -- reassociate to get the inner eqToHom on the LHS next to each other
--       -- cancel (together, they're id)
--       -- rfl
--       sorry
--   case layer =>
--     -- merge the eqToHom on either side of the RHS
--     -- extensionality on the layer
--     -- mul_assoc
--     sorry
--   case braid =>
--     symm
--     -- trans
--     -- · symm
--     --   apply assoc
--     -- · trans
--     --   · apply MyHom.equiv.comp
--     --     ·
--     --       rename_i X _ a
--     --       apply eqToHom_braid (X' := X₁.val * (X₂.val * (X.val.val * Z₁.val) * Z₂.val)) ({ val := { val := X₁.val * X₂.val } } ◁ a ▷ { val := { val := Z₁.val * Z₂.val } })
--     --     · apply refl
--     --   · sorry
--     trans
--     · apply MyHom.equiv.comp
--       · apply MyHom.equiv.refl
--       · apply braid_eqToHom
--     · trans
--       · rename_i X _ b
--         apply eqToHom_braid ({ val := { val := X₁.val * X₂.val } } ◁ b ▷ { val := { val := Z₁.val * Z₂.val } } ≫ eqToHom _) (X₁.val * (X₂.val * (X.val.val * Z₁.val) * Z₂.val))
--       ·
--         apply braid
--         -- LHS: eqToHoms around a whisker of a
--         -- RHS: a composition of three
--         -- first: left whisker of associator
--         -- second: double whisker of a
--         -- third: left whisker of associator inv
--         -- simp [MonoidalCategory.whiskerRight]


--         -- for RHS first/third: unfold associator; whisker of an eqToHom is an eqToHom
--         -- probs need a general monoidal category rule about double whiskering

--         simp
--         sorry
--     -- apply braid
--     -- sorry

--   all_goals simp [MyHom.whisker]
--   simp
--   sorry


-- #synth Category N

-- If S is a CategoryStruct on the quotient:
-- instance : Category obj :=
--   { S with
--     id_comp := -- your proof,
--     comp_id := -- your proof,
--     assoc := -- your proof
--   }

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

open TwistedCategory

instance : TwistedCategoryStruct N where
  tensorObj X Y := X * Y
  tensorHom f g := Quotient.map₂ MyHom.tensor (fun _ _ hf _ _ hg ↦ MyHom.equiv.tensor hf hg) f g
  tensorUnit := 1
  whiskerLeft X {Y₁ Y₂} f :=
    Quotient.map (MyHom.whiskerLeft X ·) (fun _ _ hf ↦ MyHom.equiv.whiskerLeft X hf) f
  whiskerRight {X₁ X₂} f Y :=
    Quotient.map (MyHom.whiskerRight · Y) (fun _ _ hf ↦ MyHom.equiv.whiskerRight Y hf) f
  associator X Y Z := eqToIso (mul_assoc X Y Z)
  leftUnitor X := eqToIso (one_mul X)
  rightUnitor X := eqToIso (mul_one X)
  starObj X := X⋆
  starHom {X Y} f := Quotient.map MyHom.star (fun _ _ hf ↦ MyHom.equiv.star hf) f
  skewator X Y := eqToIso (StarMonoid.star_mul Y X).symm
  involutor X := eqToIso (star_involutive X)
  twist X := { -- TODO it'd be nice to lift an isomorphism to another isomorphism
    hom := ⟦.braid (ς_ ⟨⟨X⟩⟩).hom⟧
    inv := ⟦.braid (ς_ ⟨⟨X⟩⟩).inv⟧
    hom_inv_id := by
      apply Quotient.sound
      simp
      trans
      · apply MyHom.equiv.merge_braid
      · simp
        rfl
    inv_hom_id := by
      apply Quotient.sound
      simp
      trans
      · apply MyHom.equiv.merge_braid
      · simp
        rfl
  }

-- TODO next step: prefunctor between S V and N words
-- TODO:

-- -- not eqToIso' or eqToIso, but morally eqToIso'! TODO generalize eqToIso'
-- def eqToIso'' {X Y : N} (h : X = Y) : X ≅ Y := {
--   hom := ⟦eqToHom h⟧
--   inv := ⟦eqToHom h.symm⟧
--   hom_inv_id := by
--     apply Quotient.sound
--     exact eqToHom_comp' (by rfl) (by rfl)
--   inv_hom_id := by
--     apply Quotient.sound
--     exact eqToHom_comp' (by rfl) (by rfl)
-- }

-- #check FreeMonoidalCategory
-- def mymk :

-- maybe defining a MonoidalCategory N isn't worth it.
-- The end goal is to define a isomorphism between the categories
-- on S V and N
-- the natural isomorphisms are what's giving us trouble here, and
-- truly we don't care about that -- just map objects to objects,
-- morphisms to morphisms
-- first, just define it on the precategories: Hom to MyHom

/-
-- TODO use ofTensorHom
#check ofTensorHom
instance : MonoidalCategory N where
  tensorObj X Y := X * Y
  tensorHom f g := Quotient.map₂ MyHom.tensor (fun _ _ hf _ _ hg ↦ MyHom.equiv.tensor hf hg) f g
  tensorUnit := 1
  associator X Y Z := eqToIso'' (mul_assoc X Y Z)
  leftUnitor X := eqToIso'' (one_mul X)
  rightUnitor X := eqToIso'' (mul_one X)
  whiskerLeft X {Y₁ Y₂} f := Quotient.map (MyHom.whiskerLeft X ·) (fun _ _ hf ↦ MyHom.equiv.whiskerLeft X hf) f
  whiskerRight {X₁ X₂} f Y := Quotient.map (MyHom.whiskerRight · Y) (fun _ _ hf ↦ MyHom.equiv.whiskerRight Y hf) f
  tensorHom_def {X₁ Y₁ X₂ Y₂} := by
    rintro ⟨f⟩ ⟨g⟩
    apply Quotient.sound
    simp
    -- -- rw [Quotient.map₂_mk]
    -- -- simp [Quotient]
    -- trans
    -- ·
    --   apply Quotient.sound
    --   simp
    --   rfl
    -- · trans Category.toCategoryStruct.comp (homMk (MyHom.whiskerRight f X₂)) (homMk (MyHom.whiskerLeft Y₁ g))
    --   · simp [CategoryStruct.comp]
    --   ·
    --     simp
    --     apply congrArg₂
    --     ·
    --       apply Quotient.sound
    --       sorry
    --     · sorry
        -- apply HomEquiv.tensorHom_def
  id_tensorHom_id _ _ := by
    apply Quotient.sound
    simp
    -- repeatedly merge eqToHom with (.braid 𝟙)
    sorry
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    apply Quotient.sound
    simp
    -- need to swap the f₂ and g₁ in the middle
    -- reassociate to get them next to each other
    -- casework on f₂ and g₁
    -- induction for the comp
    -- braids merge; use tensorHom_comp_tensorHom
    -- layers swap
    -- braid/layer is layer moves (HARD!!!)
    sorry
  whiskerLeft_id X Y := by
    apply Quotient.sound
    simp
    apply MyHom.equiv.trans
    · apply MyHom.equiv.comp
      · apply MyHom.equiv.refl
      · apply MyHom.equiv.id_comp
    · apply eqToHom_comp'
      · apply MyHom.equiv.refl
      · apply MyHom.equiv.refl
  id_whiskerRight X Y := by
    apply Quotient.sound
    simp
    rfl
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    apply Quotient.sound
    simp
    grind
  -- leftUnitor_naturality {X Y} := by
  --   rintro ⟨f⟩
  --   apply Quotient.sound
  --   grind
  -- rightUnitor_naturality {X Y} := by
  --   rintro ⟨f⟩
  --   apply Quotient.sound
  --   grind
  -- pentagon W X Y Z := by
  --   apply Quotient.sound
  --   eqToHom_eq_eqToHom
  -- triangle X Y := by
  --   apply Quotient.sound
  --   eqToHom_eq_eqToHom

-- then an isomorphism of categories between the one on N and the one on S V

#check Functor.Monoidal
-/
