import Mathlib
import LeanCategory.Egger
import LeanCategory.FreeInvolutiveCategory

namespace CategoryTheory

variable {C : Type u}

section

variable (C : Type u)

open FreeInvolutiveCategory

structure FreeTwistedCategory where
  as : I C

end

namespace FreeTwistedCategory

scoped notation "T" => FreeTwistedCategory

def unit : T C :=
  ⟨.unit⟩

def tensor (X Y : T C) : T C :=
  ⟨X.as.tensor Y.as⟩

def star (X : T C) : T C :=
  ⟨X.as.star⟩

-- in case we run into termination_by problems
def sizeOf : T C → ℕ
  | ⟨X⟩ => X.sizeOf

inductive Hom : T C → T C → Type max u v
  | id (X) : Hom X X
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : T C) {Y₁ Y₂} (f : Hom Y₁ Y₂) :
      Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : T C) :
      Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)
  | α_hom (X Y Z : T C) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : T C) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : Hom (FreeTwistedCategory.unit.tensor X) X
  | l_inv (X) : Hom X (FreeTwistedCategory.unit.tensor X)
  | ρ_hom (X : T C) : Hom (X.tensor .unit) X
  | ρ_inv (X : T C) : Hom X (X.tensor .unit)
  | star {X Y} (f : Hom X Y) : Hom X.star Y.star
  | χ_hom (X Y : T C) : Hom (X.star.tensor  Y.star) (Y.tensor X).star
  | χ_inv (X Y : T C) : Hom (Y.tensor X).star (X.star.tensor Y.star)
  | ε_hom (X : T C) : Hom X.star.star X
  | ε_inv (X : T C) : Hom X X.star.star
  | twist_hom (X : T C) : Hom X.star X
  | twist_inv (X : T C) : Hom X X.star

scoped infixr:10 " ⟶t " => Hom -- t for "twisted"

@[simp]
def Hom.inv {X Y : T C} : (X ⟶t Y) → (Y ⟶t X)
  | id X => id X
  | comp f g => comp (g.inv) (f.inv)
  | whiskerLeft X f => whiskerLeft X (f.inv)
  | whiskerRight f Y => whiskerRight (f.inv) Y
  | tensor f g => tensor (f.inv) (g.inv)
  | α_hom X Y Z => α_inv X Y Z
  | α_inv X Y Z => α_hom X Y Z
  | l_hom X => l_inv X
  | l_inv X => l_hom X
  | ρ_hom X => ρ_inv X
  | ρ_inv X => ρ_hom X
  | star f => star (f.inv)
  | χ_hom X Y => χ_inv X Y
  | χ_inv X Y => χ_hom X Y
  | ε_hom X => ε_inv X
  | ε_inv X => ε_hom X
  | twist_hom X => twist_inv X
  | twist_inv X => twist_hom X

-- whether a morphism is coherent (aka, doesn't contain twists)
def Hom.pure {X Y : T C} : (X ⟶t Y) → Prop
  | id _ => True
  | comp f g => f.pure ∧ g.pure
  | whiskerLeft _ f => f.pure
  | whiskerRight f _ => f.pure
  | tensor f g => f.pure ∧ g.pure
  | α_hom _ _ _ => True
  | α_inv _ _ _ => True
  | l_hom _ => True
  | l_inv _ => True
  | ρ_hom _ => True
  | ρ_inv _ => True
  | star f => True
  | χ_hom _ _ => True
  | χ_inv _ _ => True
  | ε_hom _ => True
  | ε_inv _ => True
  | twist_hom _ => False
  | twist_inv _ => False

inductive HomEquiv : ∀ {X Y : T C}, (X ⟶t Y) → (X ⟶t Y) → Prop
  | refl {X Y} (f : X ⟶t Y) : HomEquiv f f
  | comp {X Y Z} {f f' : X ⟶t Y} {g g' : Y ⟶t Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
  | whiskerLeft (X) {Y Z} (f f' : Y ⟶t Z) :
      HomEquiv f f' → HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
  | whiskerRight {Y Z} (f f' : Y ⟶t Z) (X) :
      HomEquiv f f' → HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
  | tensor {W X Y Z} {f f' : W ⟶t X} {g g' : Y ⟶t Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.tensor g) (f'.tensor g')
  | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶t Y₁) (g : X₂ ⟶t Y₂) :
      HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
  | comp_id {X Y} (f : X ⟶t Y) : HomEquiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : X ⟶t Y) : HomEquiv ((Hom.id _).comp f) f
  | assoc {X Y U V : T C} (f : X ⟶t U) (g : U ⟶t V) (h : V ⟶t Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  /- | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _) -/
  | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : T C} (f₁ : X₁ ⟶t Y₁) (f₂ : X₂ ⟶t Y₂)
      (g₁ : Y₁ ⟶t Z₁) (g₂ : Y₂ ⟶t Z₂) :
    HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
  | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  /- | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _) -/
  /- | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _) -/
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶t Y₁) (f₂ : X₂ ⟶t Y₂) (f₃ : X₃ ⟶t Y₃) :
      HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
        ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  /- | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _) -/
  /- | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _) -/
  | ρ_naturality {X Y} (f : X ⟶t Y) :
      HomEquiv ((f.whiskerRight unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  /- | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _) -/
  /- | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _) -/
  | l_naturality {X Y} (f : X ⟶t Y) :
      HomEquiv ((f.whiskerLeft unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  /- | pentagon {W X Y Z} : -/
  /-     HomEquiv -/
  /-       (((Hom.α_hom W X Y).whiskerRight Z).comp -/
  /-         ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W))) -/
  /-       ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z))) -/
  /- | triangle {X Y} : -/
  /-     HomEquiv ((Hom.α_hom X unit Y).comp ((Hom.l_hom Y).whiskerLeft X)) -/
  /-       ((Hom.ρ_hom X).whiskerRight Y) -/
  -- START OF NAT'S STUFF
  | star {X Y} {f f' : X ⟶t Y} : HomEquiv f f' → HomEquiv f.star f'.star
  /- | starHom_id {X} : HomEquiv (Hom.id X).star (Hom.id X.star) -/
  | starHom_comp_starHom {X Y Z : T C} (f : X ⟶t Y) (g : Y ⟶t Z) :
    HomEquiv (f.comp g).star (f.star.comp g.star)
  /- | χ_hom_inv {X Y} : HomEquiv ((Hom.χ_hom X Y).comp (Hom.χ_inv X Y)) (Hom.id _) -/
  /- | χ_inv_hom {X Y} : HomEquiv ((Hom.χ_inv X Y).comp (Hom.χ_hom X Y)) (Hom.id _) -/
  | χ_naturality {X₁ X₂ Y₁ Y₂} (f : X₁ ⟶t Y₁) (g : X₂ ⟶t Y₂) :
    HomEquiv ((f.star.tensor g.star).comp (Hom.χ_hom Y₁ Y₂))
      ((Hom.χ_hom X₁ X₂).comp (g.tensor f).star)
  /- | ε_hom_inv {X} : HomEquiv ((Hom.ε_hom X).comp (Hom.ε_inv X)) (Hom.id _) -/
  /- | ε_inv_hom {X} : HomEquiv ((Hom.ε_inv X).comp (Hom.ε_hom X)) (Hom.id _) -/
  | ε_naturality {X Y : T C} (f : X ⟶t Y) :
    HomEquiv (f.star.star.comp (Hom.ε_hom Y)) ((Hom.ε_hom X).comp f)
  /- | f3 {P Q R : T C} : HomEquiv ((Hom.α_hom P.star Q.star R.star).comp <| -/
  /-   ((Hom.χ_hom Q R).whiskerLeft P.star).comp <| -/
  /-   (Hom.χ_hom P (R.tensor Q)).comp (Hom.α_hom R Q P).star) -/
  /-   (((Hom.χ_hom P Q).whiskerRight R.star).comp (Hom.χ_hom (Q.tensor P) R)) -/
  /- | n2 {P Q : T C} : HomEquiv ((Hom.χ_hom P.star Q.star).comp <| -/
  /-   (Hom.χ_hom Q P).star.comp (Hom.ε_hom (P.tensor Q))) -/
  /-   ((Hom.ε_hom P).tensor (Hom.ε_hom Q)) -/
  /- | a {R : T C} : HomEquiv (Hom.ε_hom R).star (Hom.ε_hom R.star) -/
  | twist_hom_inv {X} : HomEquiv ((Hom.twist_hom X).comp (Hom.twist_inv X)) (Hom.id _)
  | twist_inv_hom {X} : HomEquiv ((Hom.twist_inv X).comp (Hom.twist_hom X)) (Hom.id _)
  | twist_naturality {X Y : T C} (f : X ⟶t Y) :
    HomEquiv (f.star.comp (Hom.twist_hom Y)) ((Hom.twist_hom X).comp f)
  | tℓ {P Q R : T C} : HomEquiv
    (((Hom.χ_hom P.star Q.star).whiskerRight R.star.star).comp <|
      ((Hom.twist_hom (Q.star.tensor P.star)).whiskerRight R.star.star).comp <|
      (Hom.α_hom Q.star P.star R.star.star).comp <|
      ((Hom.χ_hom P R.star).whiskerLeft Q.star).comp <|
      ((Hom.twist_hom (R.star.tensor P)).whiskerLeft Q.star).comp <|
      (Hom.α_inv Q.star R.star P).comp <|
      ((Hom.χ_hom Q R).whiskerRight P).comp <|
      ((Hom.twist_hom (R.tensor Q)).whiskerRight P).comp <|
      (Hom.α_hom R Q P))
    ((((Hom.twist_hom P.star).tensor (Hom.twist_hom Q.star)).tensor (Hom.twist_hom R.star)).comp <|
      ((Hom.χ_hom P Q).whiskerRight R.star).comp <|
      (Hom.χ_hom (Q.tensor P) R).comp
      (Hom.twist_hom (R.tensor (Q.tensor P))))
  | coherence (X Y : T C) (f g : X ⟶t Y) : f.pure → g.pure → HomEquiv f g
  | symm {X Y} (f g : X ⟶t Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : X ⟶t Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h

instance setoidHom (X Y : T C) : Setoid (X ⟶t Y) :=
  ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

macro "coherence" : tactic =>
  `(tactic|
    (intros; apply _root_.Quotient.sound; apply HomEquiv.coherence <;> repeat' constructor)
  )

instance : Category (T C) where
  Hom := fun X Y ↦ _root_.Quotient (setoidHom X Y)
  id X := ⟦Hom.id X⟧
  comp := Quotient.map₂ Hom.comp <| fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg
  id_comp := by
    rintro X Y ⟨f⟩
    apply _root_.Quotient.sound
    constructor
  comp_id := by
    rintro X Y ⟨f⟩
    apply _root_.Quotient.sound
    constructor
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    apply _root_.Quotient.sound
    constructor

instance : MonoidalCategory (T C) where
  tensorUnit := .unit
  tensorObj := .tensor
  whiskerLeft X := Quotient.map (Hom.whiskerLeft X) <| fun _ _ h ↦ HomEquiv.whiskerLeft X _ _ h
  whiskerRight f X := Quotient.map (Hom.whiskerRight · X)
    (fun _ _ h ↦ HomEquiv.whiskerRight _ _ X h) f
  tensorHom := Quotient.map₂ Hom.tensor <| fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg
  associator := fun X Y Z ↦ {
    hom := ⟦Hom.α_hom X Y Z⟧
    inv := ⟦Hom.α_inv X Y Z⟧
    hom_inv_id := by coherence
    inv_hom_id := by coherence
  }
  leftUnitor := fun X ↦ {
    hom := ⟦Hom.l_hom X⟧
    inv := ⟦Hom.l_inv X⟧
    hom_inv_id := by coherence
    inv_hom_id := by coherence
  }
  rightUnitor := fun X ↦ {
    hom := ⟦Hom.ρ_hom X⟧
    inv := ⟦Hom.ρ_inv X⟧
    hom_inv_id := by coherence
    inv_hom_id := by coherence
  }
  whiskerLeft_id := by intros; apply _root_.Quotient.sound; constructor
  id_whiskerRight := by intros; apply _root_.Quotient.sound; constructor
  tensorHom_def := by
    rintro X₁ Y₁ X₂ Y₂ ⟨f⟩ ⟨g⟩
    apply _root_.Quotient.sound; constructor
  id_tensorHom_id := by coherence
  tensorHom_comp_tensorHom := by
    rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩; apply _root_.Quotient.sound; constructor
  associator_naturality := by
    rintro _ _ _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩; apply _root_.Quotient.sound; constructor
  leftUnitor_naturality := by rintro _ _ ⟨f⟩; apply _root_.Quotient.sound; constructor
  rightUnitor_naturality := by rintro _ _ ⟨f⟩; apply _root_.Quotient.sound; constructor
  pentagon := by coherence
  triangle := by coherence

instance : InvolutiveCategoryStruct (T C) where
  starObj := .star
  starHom := Quotient.map Hom.star <| fun _ _ h ↦ HomEquiv.star h
  skewator := fun X Y ↦ {
    hom := ⟦Hom.χ_hom X Y⟧
    inv := ⟦Hom.χ_inv X Y⟧
    hom_inv_id := by coherence
    inv_hom_id := by coherence
  }
  involutor := fun X ↦ {
    hom := ⟦Hom.ε_hom X⟧
    inv := ⟦Hom.ε_inv X⟧
    hom_inv_id := by coherence
    inv_hom_id := by coherence
  }

open InvolutiveCategory

@[simp]
def homMk {X Y : T C} (f : X ⟶t Y) : X ⟶ Y := ⟦f⟧

lemma coherence_pure {X Y : T C} : ∀ f : X ⟶t Y, InvolutiveCoherence (homMk f) → f.pure := by
  intros f hf
  induction hf
  repeat' constructor

instance : InvolutiveCategory (T C) where
  starHom_id := by coherence
  starHom_comp_starHom := by rintro _ _ _ ⟨f⟩ ⟨g⟩; apply _root_.Quotient.sound; constructor
  skewator_naturality := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩; apply _root_.Quotient.sound; constructor
  involutor_naturality := by rintro _ _ ⟨f⟩; apply _root_.Quotient.sound; constructor
  coherence := by coherence

instance : Groupoid (T C) where
  inv := Quotient.map Hom.inv (by intros; trivial)
  inv_comp := by intros; exact coherence
  comp_inv := by intros; exact coherence

end CategoryTheory.T

