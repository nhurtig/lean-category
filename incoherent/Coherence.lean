import Mathlib
import LeanCategory.FreeEgger

/-!
# A `coherence` tactic for monoidal categories, and `⊗≫` (composition up to associators)

We provide a `coherence` tactic,
which proves equations where the two sides differ by replacing
strings of monoidal structural morphisms with other such strings.
(The replacements are always equalities by the monoidal coherence theorem.)

A simpler version of this tactic is `pure_coherence`,
which proves that any two morphisms (with the same source and target)
in a monoidal category which are built out of associators and unitors
are equal.

We also provide `f ⊗≫ g`, the `monoidal_comp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.
-/


-- Porting note: restore when ported
-- import Mathlib.CategoryTheory.Bicategory.CoherenceTactic

universe v u

open CategoryTheory FreeMonoidalCategory
open InvolutiveCategory

-- As the lemmas and typeclasses in this file are not intended for use outside of the tactic,
-- we put everything inside a namespace.
namespace Mathlib.Tactic.Coherence

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
open scoped MonoidalCategory

noncomputable section lifting

/-- A typeclass carrying a choice of lift of an object from `C` to `FreeMonoidalCategory C`.
It must be the case that `projectObj id (LiftObj.lift x) = x` by defeq. -/
class LiftObj (X : C) where
  protected lift : FreeMonoidalCategory C

instance LiftObj_unit : LiftObj (𝟙_ C) := ⟨Unit⟩

instance LiftObj_tensor (X Y : C) [LiftObj X] [LiftObj Y] : LiftObj (X ⊗ Y) where
  lift := LiftObj.lift X ⊗ LiftObj.lift Y

instance (priority := 100) LiftObj_of (X : C) : LiftObj X := ⟨of X⟩

/-- A typeclass carrying a choice of lift of a morphism from `C` to `FreeMonoidalCategory C`.
It must be the case that `projectMap id _ _ (LiftHom.lift f) = f` by defeq. -/
class LiftHom {X Y : C} [LiftObj X] [LiftObj Y] (f : X ⟶ Y) where
  protected lift : LiftObj.lift X ⟶ LiftObj.lift Y

instance LiftHom_id (X : C) [LiftObj X] : LiftHom (𝟙 X) := ⟨𝟙 _⟩

instance LiftHom_left_unitor_hom (X : C) [LiftObj X] : LiftHom (λ_ X).hom where
  lift := (λ_ (LiftObj.lift X)).hom

instance LiftHom_left_unitor_inv (X : C) [LiftObj X] : LiftHom (λ_ X).inv where
  lift := (λ_ (LiftObj.lift X)).inv

instance LiftHom_right_unitor_hom (X : C) [LiftObj X] : LiftHom (ρ_ X).hom where
  lift := (ρ_ (LiftObj.lift X)).hom

instance LiftHom_right_unitor_inv (X : C) [LiftObj X] : LiftHom (ρ_ X).inv where
  lift := (ρ_ (LiftObj.lift X)).inv

instance LiftHom_associator_hom (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).hom where
  lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).hom

instance LiftHom_associator_inv (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).inv where
  lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).inv

instance LiftHom_comp {X Y Z : C} [LiftObj X] [LiftObj Y] [LiftObj Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [LiftHom f] [LiftHom g] : LiftHom (f ≫ g) where
  lift := LiftHom.lift f ≫ LiftHom.lift g

instance LiftHom_tensor {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z]
    (f : W ⟶ X) (g : Y ⟶ Z) [LiftHom f] [LiftHom g] : LiftHom (f ⊗ g) where
  lift := LiftHom.lift f ⊗ LiftHom.lift g

/--
A typeclass carrying a choice of monoidal structural isomorphism between two objects.
Used by the `⊗≫` monoidal composition operator, and the `coherence` tactic.
-/
-- We could likely turn this into a `Prop` valued existential if that proves useful.
class MonoidalCoherence (X Y : C) [LiftObj X] [LiftObj Y] where
  hom : X ⟶ Y
  [isIso : IsIso hom]

attribute [instance] MonoidalCoherence.isIso

namespace MonoidalCoherence

@[simps]
instance refl (X : C) [LiftObj X] : MonoidalCoherence X X := ⟨𝟙 _⟩

@[simps]
instance tensor (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] [MonoidalCoherence Y Z] :
    MonoidalCoherence (X ⊗ Y) (X ⊗ Z) :=
  ⟨𝟙 X ⊗ MonoidalCoherence.hom⟩

@[simps]
instance tensor_right (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence (𝟙_ C) Y] :
    MonoidalCoherence X (X ⊗ Y) :=
  ⟨(ρ_ X).inv ≫ (𝟙 X ⊗ MonoidalCoherence.hom)⟩

@[simps]
instance tensor_right' (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence Y (𝟙_ C)] :
    MonoidalCoherence (X ⊗ Y) X :=
  ⟨(𝟙 X ⊗ MonoidalCoherence.hom) ≫ (ρ_ X).hom⟩

@[simps]
instance left (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] :
    MonoidalCoherence (𝟙_ C ⊗ X) Y :=
  ⟨(λ_ X).hom ≫ MonoidalCoherence.hom⟩

@[simps]
instance left' (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] :
    MonoidalCoherence X (𝟙_ C ⊗ Y) :=
  ⟨MonoidalCoherence.hom ≫ (λ_ Y).inv⟩

@[simps]
instance right (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] :
    MonoidalCoherence (X ⊗ 𝟙_ C) Y :=
  ⟨(ρ_ X).hom ≫ MonoidalCoherence.hom⟩

@[simps]
instance right' (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] :
    MonoidalCoherence X (Y ⊗ 𝟙_ C) :=
  ⟨MonoidalCoherence.hom ≫ (ρ_ Y).inv⟩

@[simps]
instance assoc (X Y Z W : C) [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z]
    [MonoidalCoherence (X ⊗ (Y ⊗ Z)) W] : MonoidalCoherence ((X ⊗ Y) ⊗ Z) W :=
  ⟨(α_ X Y Z).hom ≫ MonoidalCoherence.hom⟩

@[simps]
instance assoc' (W X Y Z : C) [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z]
    [MonoidalCoherence W (X ⊗ (Y ⊗ Z))] : MonoidalCoherence W ((X ⊗ Y) ⊗ Z) :=
  ⟨MonoidalCoherence.hom ≫ (α_ X Y Z).inv⟩

end MonoidalCoherence

/-- Construct an isomorphism between two objects in a monoidal category
out of unitors and associators. -/
def monoidalIso (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] : X ≅ Y :=
  asIso MonoidalCoherence.hom

example (X : C) : X ≅ (X ⊗ (𝟙_ C ⊗ 𝟙_ C)) := monoidalIso _ _

example (X1 X2 X3 X4 X5 X6 X7 X8 X9 : C) :
    (𝟙_ C ⊗ (X1 ⊗ X2 ⊗ ((X3 ⊗ X4) ⊗ X5)) ⊗ X6 ⊗ (X7 ⊗ X8 ⊗ X9)) ≅
    (X1 ⊗ (X2 ⊗ X3) ⊗ X4 ⊗ (X5 ⊗ (𝟙_ C ⊗ X6) ⊗ X7) ⊗ X8 ⊗ X9) :=
  monoidalIso _ _

/-- Compose two morphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
def monoidalComp {W X Y Z : C} [LiftObj X] [LiftObj Y]
    [MonoidalCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
  f ≫ MonoidalCoherence.hom ≫ g

@[inherit_doc Mathlib.Tactic.Coherence.monoidalComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ⊗≫ " =>
  Mathlib.Tactic.Coherence.monoidalComp -- type as \ot \gg

/-- Compose two isomorphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
noncomputable def monoidalIsoComp {W X Y Z : C} [LiftObj X] [LiftObj Y]
    [MonoidalCoherence X Y] (f : W ≅ X) (g : Y ≅ Z) : W ≅ Z :=
  f ≪≫ asIso MonoidalCoherence.hom ≪≫ g

@[inherit_doc Mathlib.Tactic.Coherence.monoidalIsoComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ≪⊗≫ " =>
  Mathlib.Tactic.Coherence.monoidalIsoComp -- type as \ll \ot \gg

example {U V W X Y : C} (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) : U ⟶ Y := f ⊗≫ g

-- To automatically insert unitors/associators at the beginning or end,
-- you can use `f ⊗≫ 𝟙 _`
example {W X Y Z : C} (f : W ⟶ (X ⊗ Y) ⊗ Z) : W ⟶ X ⊗ (Y ⊗ Z) := f ⊗≫ 𝟙 _

@[simp] lemma monoidalComp_refl {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ⊗≫ g = f ≫ g := by
  simp [monoidalComp]

example {U V W X Y : C} (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) :
    f ⊗≫ g = f ≫ (α_ _ _ _).inv ≫ g := by
  simp [monoidalComp]

end lifting

open Lean Meta Elab Tactic

/-- Helper function for throwing exceptions. -/
def exception (g : MVarId) (msg : MessageData) : MetaM α := throwTacticEx `monoidal_coherence g msg

/-- Helper function for throwing exceptions with respect to the main goal. -/
def exception' (msg : MessageData) : TacticM Unit := do
  try
    liftMetaTactic (exception (msg := msg))
  catch _ =>
    -- There might not be any goals
    throwError msg

/-- Auxiliary definition for `monoidal_coherence`. -/
-- We could construct this expression directly without using `elabTerm`,
-- but it would require preparing many implicit arguments by hand.
def mkProjectMapExpr (e : Expr) : TermElabM Expr := do
  Term.elabTerm
    (← ``(FreeMonoidalCategory.projectMap _root_.id _ _ (LiftHom.lift $(← Term.exprToSyntax e))))
    none

/-- Coherence tactic for monoidal categories. -/
def monoidal_coherence (g : MVarId) : TermElabM Unit := g.withContext do
  withOptions (fun opts => synthInstance.maxSize.set opts
    (max 256 (synthInstance.maxSize.get opts))) do
  -- TODO: is this `dsimp only` step necessary? It doesn't appear to be in the tests below.
  let (ty, _) ← dsimp (← g.getType) (← Simp.Context.ofNames [] true)
  let some (_, lhs, rhs) := (← whnfR ty).eq? | exception g "Not an equation of morphisms."
  let projectMap_lhs ← mkProjectMapExpr lhs
  let projectMap_rhs ← mkProjectMapExpr rhs
  -- This new equation is defeq to the original by assumption
  -- on the `LiftObj` and `LiftHom` instances.
  let g₁ ← g.change (← mkEq projectMap_lhs projectMap_rhs)
  let [g₂] ← g₁.applyConst ``congrArg
    | exception g "congrArg failed in coherence"
  let [] ← g₂.applyConst ``Subsingleton.elim
    | exception g "This shouldn't happen; Subsingleton.elim does not create goals."

/-- Coherence tactic for monoidal categories.
Use `pure_coherence` instead, which is a frontend to this one. -/
elab "monoidal_coherence" : tactic => do monoidal_coherence (← getMainGoal)

open Mathlib.Tactic.BicategoryCoherence

/--
`pure_coherence` uses the coherence theorem for monoidal categories to prove the goal.
It can prove any equality made up only of associators, unitors, and identities.
```lean
example {C : Type} [Category C] [MonoidalCategory C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
by pure_coherence
```

Users will typically just use the `coherence` tactic,
which can also cope with identities of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`
-/
elab (name := pure_coherence) "pure_coherence" : tactic => do
  let g ← getMainGoal
  monoidal_coherence g <|> bicategory_coherence g

/--
Auxiliary simp lemma for the `coherence` tactic:
this moves brackets to the left in order to expose a maximal prefix
built out of unitors and associators.
-/
-- We have unused typeclass arguments here.
-- They are intentional, to ensure that `simp only [assoc_LiftHom]` only left associates
-- monoidal structural morphisms.
@[nolint unusedArguments]
lemma assoc_liftHom {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y]
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) [LiftHom f] [LiftHom g] :
    f ≫ (g ≫ h) = (f ≫ g) ≫ h :=
  (Category.assoc _ _ _).symm

/--
Internal tactic used in `coherence`.

Rewrites an equation `f = g` as `f₀ ≫ f₁ = g₀ ≫ g₁`,
where `f₀` and `g₀` are maximal prefixes of `f` and `g` (possibly after reassociating)
which are "liftable" (i.e. expressible as compositions of unitors and associators).
-/
elab (name := liftable_prefixes) "liftable_prefixes" : tactic => do
  withOptions (fun opts => synthInstance.maxSize.set opts
    (max 256 (synthInstance.maxSize.get opts))) do
  evalTactic (← `(tactic|
    (simp (config := {failIfUnchanged := false}) only
      [monoidalComp, Category.assoc, MonoidalCoherence.hom]) <;>
    (apply (cancel_epi (𝟙 _)).1 <;> try infer_instance) <;>
    (simp (config := {failIfUnchanged := false}) only
      [assoc_liftHom, Mathlib.Tactic.BicategoryCoherence.assoc_liftHom₂])))

lemma insert_id_lhs {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y) (w : f ≫ 𝟙 _ = g) :
    f = g := by
  simpa using w

lemma insert_id_rhs {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y) (w : f = g ≫ 𝟙 _) :
    f = g := by
  simpa using w

/-- If either the lhs or rhs is not a composition, compose it on the right with an identity. -/
def insertTrailingIds (g : MVarId) : MetaM MVarId := do
  let some (_, lhs, rhs) := (← withReducible g.getType').eq? | exception g "Not an equality."
  let mut g := g
  if !(lhs.isAppOf ``CategoryStruct.comp) then
    let [g'] ← g.applyConst ``insert_id_lhs | exception g "failed to apply insert_id_lhs"
    g := g'
  if !(rhs.isAppOf ``CategoryStruct.comp) then
    let [g'] ← g.applyConst ``insert_id_rhs | exception g "failed to apply insert_id_rhs"
    g := g'
  return g

/-- The main part of `coherence` tactic. -/
-- Porting note: this is an ugly port, using too many `evalTactic`s.
-- We can refactor later into either a `macro` (but the flow control is awkward)
-- or a `MetaM` tactic.
def coherence_loop (maxSteps := 37) : TacticM Unit :=
  match maxSteps with
  | 0 => exception' "`coherence` tactic reached iteration limit"
  | maxSteps' + 1 => do
    -- To prove an equality `f = g` in a monoidal category,
    -- first try the `pure_coherence` tactic on the entire equation:
    evalTactic (← `(tactic| pure_coherence)) <|> do
    -- Otherwise, rearrange so we have a maximal prefix of each side
    -- that is built out of unitors and associators:
    evalTactic (← `(tactic| liftable_prefixes)) <|>
      exception' ("Something went wrong in the `coherence` tactic: " ++
        "is the target an equation in a monoidal category?")
    -- The goal should now look like `f₀ ≫ f₁ = g₀ ≫ g₁`,
    liftMetaTactic MVarId.congrCore
    -- and now we have two goals `f₀ = g₀` and `f₁ = g₁`.
    -- Discharge the first using `coherence`,
    evalTactic (← `(tactic| { pure_coherence })) <|>
      exception' "`coherence` tactic failed, subgoal not true in the free monoidal category"
    -- Then check that either `g₀` is identically `g₁`,
    evalTactic (← `(tactic| rfl)) <|> do
      -- or that both are compositions,
      liftMetaTactic' insertTrailingIds
      liftMetaTactic MVarId.congrCore
      -- with identical first terms,
      evalTactic (← `(tactic| rfl)) <|>
        exception' "`coherence` tactic failed, non-structural morphisms don't match"
      -- and whose second terms can be identified by recursively called `coherence`.
      coherence_loop maxSteps'

/--
Use the coherence theorem for monoidal categories to solve equations in a monoidal equation,
where the two sides only differ by replacing strings of monoidal structural morphisms
(that is, associators, unitors, and identities)
with different strings of structural morphisms with the same source and target.

That is, `coherence` can handle goals of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`.

(If you have very large equations on which `coherence` is unexpectedly failing,
you may need to increase the typeclass search depth,
using e.g. `set_option synthInstance.maxSize 500`.)
-/
syntax (name := coherence) "coherence" : tactic

@[inherit_doc coherence]
elab_rules : tactic
| `(tactic| coherence) => do
  evalTactic (← `(tactic|
    (simp (config := {failIfUnchanged := false}) only [bicategoricalComp,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom',
      monoidalComp]);
    whisker_simps (config := {failIfUnchanged := false})
    ))
  coherence_loop
