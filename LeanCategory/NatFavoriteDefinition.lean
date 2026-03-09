import Mathlib
import LeanCategory.FreeEgger
import LeanCategory.FreeEggerFunctor

open CategoryTheory

/- def Carrier := ℕ -/
/- deriving Repr, DecidableEq -/
/- def Loop := ℕ -- TODO: loops have twists! -/
/- deriving Repr, DecidableEq -/

/- def Strand := Carrier ⊕ Loop -/
/- deriving Repr, DecidableEq -/

-- the generating objects (for us, strands)
variable {V : Type u}

/- instance instV_StarMonoid : StarMonoid V where -/
/-   mul := List.append -/
/-   mul_assoc := List.append_assoc -/
/-   one := List.nil -/
/-   one_mul := List.nil_append -/
/-   mul_one := List.append_nil -/
/-   star := List.reverse -/
/-   star_involutive := List.reverse_reverse -/
/-   star_mul _ _ := List.reverse_append -/

@[simp]
def inject (L : List (V × Bool)) : F V :=
  L.map (fun (v, b) ↦ (if b then (FreeTwistedCategory.of v).star else (FreeTwistedCategory.of v)))
    |>.foldl .tensor .unit

@[simp]
instance : MulOne (List <| V × Bool) where
  one := []
  mul := List.append

@[simp]
instance : Star (List <| V × Bool) where
  star L := (L.map (fun (v, b) ↦ (v, !b))).reverse

/- #check  -/
postfix:max "⋆" => @Star.star (List <| _ × Bool) _

-- are the lists ever used? I don't think so...
@[simp]
def project : F V → List (V × Bool)
  | .unit => []
  | .star X => (project X)⋆
  | .tensor X Y => (project X) * (project Y)
  | .of X => [(X, false)]

variable (v : V)

-- TODO inject-project is ID; project-inject is involutive (adjoint stuff)

/- section -/
/- local instance : Quiver.{v} (F V) where -/
/-   Hom X Y := { f : ((Z : (List (V × Bool) × List (V × Bool))) × (Z.1 ⟶ Z.2)) // (inject f.1.1 = X ∧ inject f.1.2 = Y) } -/

/- -- this is our category!!! -/
/- #synth TwistedCategory (F V) -/
/- end -/

-- this is just the braids
#check (F V)
#synth TwistedCategory (F V)
#synth Category (F V)
#synth Quiver (F V)
/- #check CategoryTheory.FreeTwistedCategory.twistedFromQuiver -/

#check (F V)
#check Bool


  -- hdom : dom = left * box.dom * right := by grind
  -- hcod : cod = left * box.cod * right := by grind

-- β is the free category without a quiver
-- set up notation b/c we'll be introducing
-- a higher-priority category on F V later
#check MonoidalCategory
def βcat : Category.{u} (F V) := FreeTwistedCategory.categoryFreeTwistedCategory
infixr:10 " ⟶β " => βcat.Hom
notation "𝟙β" => βcat.id
infixr:80 " ≫β " => βcat.comp
infixr:10 " ≅β " => @Iso _ βcat
def βtwist : TwistedCategory.{u} (F V) := FreeTwistedCategory.freeTwistedCategory
infixr:70 " ⊗β " => βtwist.tensorObj
infixr:81 " ◁β " => βtwist.whiskerLeft
infixl:81 " ▷β " => βtwist.whiskerRight
infixr:70 " ⊗ₘβ " => βtwist.tensorHom
notation "𝟙_β " C:arg => βtwist.tensorUnit C
postfix:max "⋆β" => βtwist.starObj
postfix:max "⋆β" => βtwist.starHom

#synth Category (F V)


-- the stitches (lacking restriction on dom/cod size from paper)
variable [stitches : Quiver.{v} (F V)] {stitchStar : {X Y : F V} → (X ⟶ Y) → (X.star ⟶ Y.star)}

/- #synth (Quiver (List <| V × Bool)) -/
-- A CanonicalStitch with a record of the identity strands on its left/right
-- TODO: maybe make two layers -- one for two+ outs, one for one out
structure Layer (X Y : F V) where
  L : F V
  box : X ⟶ Y
  R : F V


-- if two F V's have the same project, there's a morphism between them in braid land
-- (w/o twist, but that's not important right now)
-- TO PROVE THIS: define a "canonical form" for (F V) up to natural isomorphisms.
-- Show that every F V is ⟶β equivalent to some canonical form.
-- Show that canonical forms and F V's have the same projection... ugh we'll need to drop the twist
-- now
-- wait... if p X = p Y and Y is canonical, that might work
-- List (V × Bool) IS our canonical representation!

open MonoidalCategory
#check Iso


#check CategoryStruct

inductive MyHom : F V → F V → Type (max u v 2) where
  | layer : (l : Layer X Y) →
      MyHom (l.L * X * l.R) (l.L * Y * l.R)
  | braid {X Y : F V} : (X ⟶β Y) → MyHom X Y
  /- -- | id (X : N) : MyHom X X -- just use braid's id! -/
  | comp {X Y Z : F V} : MyHom X Y → MyHom Y Z → MyHom X Z

infixr:10 " ⟶ⁿ " => MyHom

instance (priority := low) preHom : CategoryStruct (F V) where
  Hom := MyHom
  id := (MyHom.braid <| 𝟙β ·)
  comp := MyHom.comp

inductive TopBottom where
  | Top
  | Bottom

@[simp]
def Layer.boundary {X Y : F V} (l : Layer X Y) : TopBottom → F V
  | .Top => l.L * Y * l.R
  | .Bottom => l.L * X * l.R

/- @[simp] -/
/- def Layer.cod : Layer → V -/
/-   | ⟨left, box, right⟩ => left * box.cod * right -/

-- start of subgroupoid stuff

inductive LayerSubgroupoidGen {X Y : F V} (l : Layer X Y) where
  | kappa : LayerSubgroupoidGen l -- the primary strand
  | left : Fin l.L.length → LayerSubgroupoidGen l -- named strands to the left of the stitch
  | right : Fin l.R.length → LayerSubgroupoidGen l -- named strands to the right of the stitch

notation "S" => LayerSubgroupoidGen

def Lcat {X Y : F V} {l : Layer X Y} : Category.{0} (F (S l)) := inferInstance
infixr:10 " ⟶L " => Lcat.Hom
notation "𝟙L" => Lcat.id
infixr:80 " ≫L " => Lcat.comp
infixr:10 " ≅L " => @Iso _ Lcat
def Ltwist {X Y : F V} {l : Layer X Y} : TwistedCategory.{0} (F (S l)) := inferInstance
infixr:70 " ⊗L " => Ltwist.tensorObj
infixr:81 " ◁L " => Ltwist.whiskerLeft
infixl:81 " ▷L " => Ltwist.whiskerRight
infixr:70 " ⊗ₘL " => Ltwist.tensorHom
notation "𝟙_L " C:arg => Ltwist.tensorUnit C
postfix:max "⋆L" => Ltwist.starObj
postfix:max "⋆L" => Ltwist.starHom


def Layer.layerTypeLeft {X Y : F V} (l : Layer X Y) : F (S l) :=
  l.L.toFin.map .left

def Layer.layerTypeRight {X Y : F V} (l : Layer X Y) : F (S l) :=
  l.R.toFin.map .right

@[simp]
def Layer.layerTypeStitch {X Y : F V} (l : Layer X Y) : F (S l) :=
  .of .kappa -- TODO do we need to track flippedness in Layer? Nah, I don't think so...

@[simp]
def Layer.layerType {X Y : F V} (l : Layer X Y) : F (S l) :=
  l.layerTypeLeft * l.layerTypeStitch * l.layerTypeRight

-- boxHandler was used for above/below
@[simp]
def Layer.phiGen {X Y : F V} (l : Layer X Y) (above : TopBottom) : (S l) → F V
  | .kappa => match above with
    | .Top => Y
    | .Bottom => X
  | .left i => .of <| l.L.getElem i
  | .right i => .of <| l.R.getElem i

def Layer.phi {X Y : F V} (l : Layer X Y) (above : TopBottom) (Z : F (S l)) : F V :=
  (Z.map <| l.phiGen above).flatten

/- @[simp] -/
/- lemma List.map_range_succ : List.map f (List.range (n + 1)) = -/
/-     (List.map f (List.range n)) ++ [f n] := by -/
/-   rw [List.range_succ] -/
/-   simp -/

/- @[simp] -/
/- lemma List.getElem?_prefix {l l' : List α} : l' ++ [a] <+: l → l[l'.length]? = .some a := by -/
/-   rintro ⟨s, h⟩ -/
/-   subst l -/
/-   simp -/

@[simp]
lemma Layer.phi_involutive_helper {X : F V} : (X.toFin).map (X.getElem ·) = X := by
  induction X
  case of =>
    simp_all
  case unit =>
    simp
  case star X ih =>
    simp_all
    apply Eq.trans _ ih
    clear ih
    cases X <;> simp_all
    case star X =>
      apply congrArg (X.toFin.map ·)
      ext i
      apply congrArg (X.getElem ·)
      ext
      simp
      omega
    case tensor X Y =>
      constructor
      any_goals apply congrArg (X.toFin.map ·)
      any_goals apply congrArg (Y.toFin.map ·)
      all_goals ext i ; simp
      all_goals split
      any_goals omega
      any_goals apply congrArg (X.getElem ·)
      any_goals apply congrArg (Y.getElem ·)
      all_goals ext ; simp ; omega
  case tensor X Y ih₁ ih₂ =>
    simp
    constructor
    any_goals apply Eq.trans _ ih₁
    any_goals apply Eq.trans _ ih₂
    any_goals apply congrArg (X.toFin.map ·)
    any_goals apply congrArg (Y.toFin.map ·)
    all_goals ext i ; simp

/-
@[simp]
lemma Layer.phi_left {X Y : F V} {l : Layer X Y} : l.phi b l.layerTypeLeft = l.L := by
  simp [phi, layerTypeLeft]
  induction l.L

  generalize hx : l.L = x at *
  have hpre : x ⊆ l.L := by subst hx; exact FreeTwistedCategory.Subset.rfl
  clear hx
  induction x <;> simp_all
  case of x =>
    unfold Subset at hpre
    unfold FreeTwistedCategory.instHasSubset at hpre
    simp at hpre
    cases hpre
    case inl h =>
      rw [← h]
      simp
    case inr h =>
      rw [h.choose_spec]
      simp
  case star X ih =>
    cases hpre
    case inl h =>
      simp
      rw [← h]
      simp

@[simp]
lemma Layer.phi_right {l : Layer} : l.phi f l.layerTypeRight = l.right := by
  simp [phi, layerTypeRight]
  generalize hx : l.right = x at *
  have hpre : x <+: l.right := by aesop
  clear hx
  induction x using List.reverseRecOn
  all_goals simp
  case append_singleton l' a ih =>
    apply congrArg₂
    · apply ih
      refine trans ?_ hpre
      aesop
    · rw [List.getElem?_prefix hpre]
-/

@[simp]
lemma Layer.phi_mul {X Y : F V} {l : Layer X Y} {A B : F (S l)} : l.phi b (A * B) =
    (l.phi b A) * (l.phi b B) := by
  simp [HMul.hMul, phi]

lemma Layer.phi_involutive {X Y : F V} {l : Layer X Y} : l.phi b l.layerType = l.boundary b := by
  cases b <;> simp
  all_goals
    unfold Layer.phi ;
    unfold Layer.phiGen ;
    try unfold Layer.layerTypeLeft ;
    try unfold Layer.layerTypeRight ;
    simp ;
    unfold Function.comp ;
    simp

-- TODO a way to map F (S l) words (Y) with domain l.layerType into MyHom
-- words (aka F V) from l's bottom boundary (Y's domain) to Y's codomain in the
-- bottom projection to a modified l to Y's codomain in the top projection to to l's top boundary
-- (Y's domain)
--
-- extra condition that Y's domain is well-behaved? Not necessary! It MUST be well-behaved!!!
-- this is why the theory is nice
--
-- notably, our no-quiver representations are groupoids... gotta show that real quick TODO

#synth Category (F (S _))

-- end of subgroupoid stuff


#check CategoryTheory.Cat.isoOfEquiv -- we want to use this
open CategoryTheory.InvolutiveCategory -- for the ⋆ notation

macro "pure_iso_step_forwards" : tactic =>
  `(tactic|
    first
      | exact 𝟙β _
      | refine ?_ ▷β _
      | refine _ ◁β ?_
      | refine (α_ _ _ _).inv ≫β ?_
      | refine ?_ ≫β (α_ _ _ _).hom
      | refine (λ_ _).hom ≫β ?_
      | refine ?_ ≫β (λ_ _).inv
      | refine (ρ_ _).hom ≫β ?_
      | refine ?_ ≫β (ρ_ _).inv
      | refine (χ_ _ _).inv ≫β ?_
      | refine ?_ ≫β (χ_ _ _).hom
      | fail "IDK what to do"
  )

-- associator is reversed here
macro "pure_iso_step_backwards" : tactic =>
  `(tactic|
    first
      | exact 𝟙β _
      | refine ?_ ▷β _
      | refine _ ◁β ?_
      | refine (α_ _ _ _).hom ≫β ?_
      | refine ?_ ≫β (α_ _ _ _).inv
      | refine (λ_ _).hom ≫β ?_
      | refine ?_ ≫β (λ_ _).inv
      | refine (ρ_ _).hom ≫β ?_
      | refine ?_ ≫β (ρ_ _).inv
      | refine (χ_ _ _).inv ≫β ?_
      | refine ?_ ≫β (χ_ _ _).hom
      | fail "IDK what to do"
  )

-- the tactic equivalent of smacking a TV to see if that fixes it
macro "pure_iso" : tactic =>
  `(tactic|
      ((repeat pure_iso_step_forwards) ; (repeat pure_iso_step_backwards))
  )

open MonoidalCategory
@[simp, grind]
def MyHom.whisker (X : F V) {Y₁ Y₂ : F V} : (Y₁ ⟶ⁿ Y₂) → (Z : F V) →
    ((X * (Y₁ * Z)) ⟶ⁿ (X * (Y₂ * Z)))
  | .layer l, Z =>
    (MyHom.braid <| by pure_iso).comp <|
    (MyHom.layer ⟨X * l.L, l.box, l.R * Z⟩).comp
    (.braid <| by pure_iso)
  | .braid b, Z => MyHom.braid (↑X ◁ b ▷ ↑Z)
  -- | .id Y, Z => 𝟙 (X * Y * Z)
  | .comp f g, Z => (whisker X f Z).comp (whisker X g Z)

/- #synth Quiver N -/

@[simp, grind]
def MyHom.whiskerLeft (X : F V) {Y₁ Y₂ : F V} (f : Y₁ ⟶ⁿ Y₂) : ((X * Y₁) ⟶ⁿ (X * Y₂)) :=
  (MyHom.braid (by pure_iso)).comp <|
    (MyHom.whisker X f 1).comp <|
    MyHom.braid (by pure_iso)

@[simp, grind]
def MyHom.whiskerRight {X₁ X₂ : F V} (f : X₁ ⟶ⁿ X₂) (Y : F V) : ((X₁ * Y) ⟶ⁿ (X₂ * Y)) :=
  -- eqToHom (by simp) ≫ MyHom.whisker 1 f Y ≫ eqToHom (by simp)
  (MyHom.braid (by pure_iso)).comp <|
    (MyHom.whisker 1 f Y).comp <|
    MyHom.braid (by pure_iso)

@[simp, grind]
def MyHom.tensor {X₁ X₂ Y₁ Y₂ : F V} (f : X₁ ⟶ⁿ Y₁) (g : X₂ ⟶ⁿ Y₂) : (X₁ * X₂) ⟶ⁿ (Y₁ * Y₂) :=
  (whiskerRight f X₂).comp (whiskerLeft Y₁ g)

@[simp, grind]
def MyHom.star {X Y : F V} : (X ⟶ⁿ Y) → (X⋆ ⟶ⁿ Y⋆)
  | .layer ⟨L, s, R⟩ =>
      (MyHom.braid <| by pure_iso).comp <|
        (MyHom.layer ⟨R⋆, stitchStar s, L⋆⟩).comp <|
        MyHom.braid (by pure_iso)
  | .braid b => .braid b⋆
  | .comp f g => (f.star).comp g.star

-- #synth Quiver (S (F V))

-- variable {X Y Z : S (F V)} {b₁ : X ⟶ Y} {b₂ : Y ⟶ Z}

-- TODO: get namespaces set up so we don't do this "my" business
@[grind]
inductive MyHom.equiv : ∀ {X Y : (F V)}, (X ⟶ⁿ Y) → (X ⟶ⁿ Y) → Prop where
  | refl (f) : MyHom.equiv f f
  | comp {f f' : X ⟶ⁿ Y} : MyHom.equiv f f' → MyHom.equiv g g' → MyHom.equiv (f.comp g) (f'.comp g')
  | id_comp : MyHom.equiv ((MyHom.braid (𝟙β X)).comp f) f
  | comp_id {f : X ⟶ⁿ Y} : MyHom.equiv (f.comp (.braid (𝟙β Y))) f
  | assoc {f : _ ⟶ⁿ _} {g : _ ⟶ⁿ _} {h : _ ⟶ⁿ _} :
      MyHom.equiv ((f.comp g).comp h) (f.comp (g.comp h))
  | merge_braid {b₁ : X ⟶β Y} {b₂ : Y ⟶β Z} :
      MyHom.equiv ((MyHom.braid b₁).comp (.braid b₂)) (.braid (b₁ ≫β b₂))
  -- the paper's rules
/- ⊢ L * Y₁ * (M * X₂ * R) ⟶ L * Y₁ * M * X₂ * R -/
  | swap {s₁ : X₁ ⟶ Y₁} {s₂ : X₂ ⟶ Y₂} : MyHom.equiv
      ((MyHom.layer ⟨L, s₁, M * X₂ * R⟩).comp
        ((MyHom.braid (by pure_iso)).comp
        ((MyHom.layer ⟨L * Y₁ * M, s₂, R⟩).comp
        (MyHom.braid (by pure_iso)))))
      ((MyHom.braid <| by pure_iso).comp
        ((MyHom.layer ⟨L * X₁ * M, s₂, R⟩).comp
        ((MyHom.braid <| by pure_iso).comp
        (MyHom.layer ⟨L, s₁, M * Y₂ * R⟩))))
  -- TODO layer moves
  | symm (f g) : MyHom.equiv f g → MyHom.equiv g f
  | trans {f g h : X ⟶ⁿ Y} : MyHom.equiv f g → MyHom.equiv g h → MyHom.equiv f h

instance {X Y : F V} : HasEquiv (MyHom X Y) where
  Equiv := MyHom.equiv

instance {X Y : F V} : HasEquiv (X ⟶ⁿ Y) where
  Equiv := MyHom.equiv

attribute [grind →] MyHom.equiv.comp

@[grind =_]
lemma MyHom.equiv_def {X Y : F V} {f g : X ⟶ⁿ Y} : MyHom.equiv f g ↔ f ≈ g := by
  constructor
  all_goals intros h
  all_goals exact h

@[grind =_]
lemma MyHom.equiv_def' {X Y : F V} {f g : MyHom X Y} : MyHom.equiv f g ↔ f ≈ g := by
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

-- next step: prefunctor between S V and N words that'll eventually be our isomorphism

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
