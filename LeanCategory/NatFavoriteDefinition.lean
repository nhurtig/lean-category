import Mathlib
import LeanCategory.Layer

variable {V : Type u} [stitches : StarQuiver.{v} V]

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

namespace Layer

inductive TopBottom where
  | Top
  | Bottom

def boundary {X Y : F V} (l : Layer X Y) : TopBottom → F V
  | .Top => l.L * Y * l.R
  | .Bottom => l.L * X * l.R

@[simp]
lemma boundary_top {X Y : F V} (l : Layer X Y) : boundary l .Top = l.L * Y * l.R := rfl

@[simp]
lemma boundary_bottom {X Y : F V} (l : Layer X Y) : boundary l .Bottom = l.L * X * l.R := rfl

inductive SubgroupoidGen {X Y : F V} (l : Layer X Y) where
  | kappa : SubgroupoidGen l -- the primary strand
  | left : Fin l.L.length → SubgroupoidGen l -- named strands to the left of the stitch
  | right : Fin l.R.length → SubgroupoidGen l -- named strands to the right of the stitch

scoped notation "S" => SubgroupoidGen

def layerTypeLeft {X Y : F V} (l : Layer X Y) : F (S l) :=
  l.L.toFin.map .left

def layerTypeRight {X Y : F V} (l : Layer X Y) : F (S l) :=
  l.R.toFin.map .right

@[simp]
def layerTypeStitch {X Y : F V} (l : Layer X Y) : F (S l) :=
  .of .kappa -- TODO do we need to track flippedness in Layer? Nah, I don't think so...

@[simp]
def layerType {X Y : F V} (l : Layer X Y) : F (S l) :=
  l.layerTypeLeft * l.layerTypeStitch * l.layerTypeRight

@[simp]
def phiGen {X Y : F V} (l : Layer X Y) (b : TopBottom) : (S l) → F V
  | .kappa => match b with
    | .Top => Y
    | .Bottom => X
  | .left i => .of <| l.L.getElem i
  | .right i => .of <| l.R.getElem i

/-
def phi {X Y : F V} (l : Layer X Y) (b : TopBottom) (Z : F (S l)) : F V :=
  (Z.map <| l.phiGen b).flatten
-/

open CategoryTheory.InvolutiveCategory
open CategoryTheory.FreeTwistedCategory

omit stitches in
@[simp]
lemma phi_involutive_helper {X : F V} : (X.toFin).map (X.getElem ·) = X := by
  induction X
  case of =>
    simp_all
  case unit =>
    simp
  case star X ih =>
    simp_all
    apply congrArg
    apply Eq.trans _ ih
    clear ih
    cases X <;> simp_all
    case star X =>
      apply congrArg
      apply congrArg (map · X.toFin)
      ext i
      apply congrArg (X.getElem ·)
      ext
      simp
      omega
    case tensor X Y =>
      apply congrArg₂
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
    apply congrArg₂
    any_goals apply Eq.trans _ ih₁
    any_goals apply Eq.trans _ ih₂
    any_goals apply congrArg (X.toFin.map ·)
    any_goals apply congrArg (Y.toFin.map ·)
    all_goals ext i ; simp

/-
@[simp]
lemma phi_mul {X Y : F V} {l : Layer X Y} {A B : F (S l)} : l.phi b (A * B) =
    (l.phi b A) * (l.phi b B) := by
  simp [HMul.hMul, phi]

lemma phi_involutive {X Y : F V} {l : Layer X Y} : l.phi b l.layerType = l.boundary b := by
  cases b <;> simp
  all_goals
    unfold Layer.phi ;
    unfold Layer.phiGen ;
    try unfold Layer.layerTypeLeft ;
    try unfold Layer.layerTypeRight ;
    simp ;
    unfold Function.comp ;
    simp
-/

end Layer

open CategoryTheory

-- this is just the braids
#check (F V)
#synth TwistedCategory (F V)
#synth Category (F V)
#synth Quiver (F V)
/- #check CategoryTheory.FreeTwistedCategory.twistedFromQuiver -/

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
/- variable {stitchStar : {X Y : F V} → (X ⟶ Y) → (X.star ⟶ Y.star)} -/

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

namespace Layer

-- the subgroupoid
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


-- TODO a way to map F (S l) words (Y) with domain l.layerType into MyHom
-- words (aka F V) from l's bottom boundary (Y's domain) to Y's codomain in the
-- bottom projection to a modified l to Y's codomain in the top projection to to l's top boundary
-- (Y's domain)

-- well, there already should be a functor from F (S l) to F V in projectFree, given (S l) → V
open FreeTwistedCategory
#check projectFree
-- okay... what's our function (S l) → V? DNE... we need to map κ to F V
#check project
-- ok. So we want to have D := F V, and then we can use a function S l → F V
-- what's our function S l → F V? That's phiGen
#check phiGen

-- every layer begets a functor from its subgroupoid to its above/below space:
-- TODO call this phi, rename the others
instance φ {X Y : F V} (l : Layer X Y) (b : TopBottom) : F (S l) ⥤ F V := project (phiGen l b)

open MonoidalCategory

/- lemma phi_involutive {X Y : F V} {l : Layer X Y} : l.phi b l.layerType = l.boundary b := by -/
-- TODO logic for this lemma is scattered everywhere
@[simp]
lemma phi_obj_layerType {X Y : F V} (l : Layer X Y) :
    (l.φ b).obj l.layerType = l.boundary b := by
  unfold φ
  unfold project
  cases b <;> simp
  all_goals apply congrArg₂
  any_goals apply congrArg₂
  any_goals rfl
  any_goals unfold layerTypeLeft
  any_goals unfold layerTypeRight
  all_goals unfold phiGen
  all_goals simp
  all_goals unfold Function.comp
  all_goals simp

#check Functor
/- variable {X Y : F V} {l : Layer X Y} {b : TopBottom} {d : F (S l)} {f : l.layerType ⟶ d} -/
/- #check (l.φ b).obj l.layerType -/
/- #check (l.φ b).obj 1 -/
/- #check (l.φ b).map f -/
/- #check inv <| (l.φ b).map f -/

@[simp]
def layerMoveBraid {X Y : F V} (l : Layer X Y) {Z : F (S l)} (s : l.layerType ⟶ Z) (b : TopBottom) :
    (l.boundary b) ⟶β (l.φ b).obj Z :=
   (l.phi_obj_layerType) ▸ (l.φ b).map s -- TODO consider using eqToHom if something goes south

-- sorta like a functor for F (S l) into the category of layers...
-- yeah! Layer X Y (fixed box) forms a category, where morphisms
-- are movements between the left/right and reassociations

-- we should probably just map to a Layer X Y, and then later prove
-- that the boundaries are good
@[simp]
def preLayerMoveLayer {X Y : F V} (l : Layer X Y) {Z : F (S l)} : (l.layerType ⟶ᵐ Z) → Layer X Y
  | .id _ => l
  | .comp f g => (l.preLayerMoveLayer f).preLayerMoveLayer g
  | _ => sorry

-- AAHHHHH! Make each Layer contain its own subgroupoid type, and define a layer's
-- MyHom type using the injection φ! Now Layers can contain multiple, duplicated, boxes (who cares,
-- this is easy to reconfigure, right?). Actually, that could technically break the isomorphism.
-- Maybe we need a Layer split/merge rule if we do this... a Layer can split over tensor...
-- but this messes with the indices and the left/right-ness. Maybe a Layer doesn't necessarily
-- have unique strand IDs, but the generators are of a different type? Yeah, each Layer
-- has its own type for strand IDs, and its own strand projection into the real world. This
-- way, when they merge they just do an ⊕ of their types. The ⊕ has some nasty commutative
-- conversion junk, but the nice thing is that it's lost on the functor into the quivered
-- category, which is what we want to canonicalize anyways. Very annoying that all the index
-- work seems to have been for naught, though.

-- So a Layer is indexed by some type; we'll call it α. It has an object (F α), and a projection
-- α → TopBottom → F V. In the F V category of MyHom, we run map then flatten to get the
-- domain and codomain. We could even have EVERYTHING be a stitch! The identity strands are
-- just really tiny ones.

-- No, this doesn't work. If we use ⊕ to merge/split, then something that isn't using ⊕ can't split.
-- It's also unclear how we'd represent the boxes themselves within the layer. Okay, do we
-- need to use ⊕? Yeah, I think we do...

-- Okay, forget about that. What about the "category of layers"? Objects would be Layer X Y.
-- Morphisms can mess with the left, mess with the right, star the box, and exchange
-- the box with something to move between the left and right. So it's on a triple?
-- Objects would be (F V) × Bool × (F V). This feels an awful like the F (S l) category...
-- Or, the objects could just be Layer X Y!. This IS the subgroupoid, just a silly
-- representation of it!!! Do we even need the Bool in the middle? I don't really think
-- so... we only need to track the objects when they change how morphisms might be able
-- to be applied. So then the morphisms are a twist on the box, morphisms on either side,
-- and exchanges between either side: ((A ⊗ B), C) → (A, B ⊗ C). Ugh, there's gonna be
-- all this junk about naturality and stuff. But do we care? We just need to say that
-- it's a category, right? Yeah, the injection φ gives it semantics, this is just
-- typed syntax.

-- So say s is a morphism ℓ₁ ⟶ ℓ₂, each Layer X Y. Then we can use φ, parameterized by
-- some b : TopBottom, to turn s into morphisms in F V: ℓ₁.boundary b ⟶β ℓ₂.boundary b.
-- Invert the top one, we have on the bottom ℓ₁.dom →β ℓ₂.dom, compose with ℓ₂, then
-- ℓ₂.cod →β ℓ₁.cod!!!! DONE!

-- we'll need Quotient.liftOn, right?
def layerMoveLayer {X Y : F V} (l : Layer X Y) {Z : F (S l)} (s : l.layerType ⟶ Z) :
    (l.φ .Bottom).obj Z ⟶ⁿ (l.φ .Top).obj Z := by
  #check Quotient.liftOn
  apply Quotient.liftOn s

  sorry


--
-- extra condition that Y's domain is well-behaved? Not necessary! It MUST be well-behaved!!!
-- this is why the theory is nice
--
-- notably, our no-quiver representations are groupoids

end Layer


open MonoidalCategory
open InvolutiveCategory -- for the ⋆ notation
open TwistedCategory -- why not

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
