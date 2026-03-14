import Mathlib
import LeanCategory.Egger

namespace CategoryTheory

variable {C : Type u}

section

variable (C : Type u)

-- we will NOT be defining notation for
-- this type, as it conflicts with the later
-- monoidal/involutive category notations
inductive FreeInvolutiveCategory : Type u
  | of : C → FreeInvolutiveCategory
  | unit : FreeInvolutiveCategory
  | tensor : FreeInvolutiveCategory → FreeInvolutiveCategory → FreeInvolutiveCategory
  | star : FreeInvolutiveCategory → FreeInvolutiveCategory
  deriving Inhabited

end

namespace FreeInvolutiveCategory

scoped notation "I" => FreeInvolutiveCategory

-- in case we run into termination_by problems
def sizeOf : FreeInvolutiveCategory C → ℕ
  | of _ => 0
  | unit => 0
  | tensor A B => A.sizeOf + B.sizeOf + 1
  | star A => A.sizeOf + 1

inductive Hom : FreeInvolutiveCategory C → FreeInvolutiveCategory C → Type max u v
  | id (X) : Hom X X
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : FreeInvolutiveCategory C) {Y₁ Y₂} (f : Hom Y₁ Y₂) :
      Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : FreeInvolutiveCategory C) :
      Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)
  | α_hom (X Y Z : FreeInvolutiveCategory C) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : FreeInvolutiveCategory C) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : Hom (FreeInvolutiveCategory.unit.tensor X) X
  | l_inv (X) : Hom X (FreeInvolutiveCategory.unit.tensor X)
  | ρ_hom (X : FreeInvolutiveCategory C) : Hom (X.tensor .unit) X
  | ρ_inv (X : FreeInvolutiveCategory C) : Hom X (X.tensor .unit)
  | star {X Y} (f : Hom X Y) : Hom X.star Y.star
  | χ_hom (X Y : FreeInvolutiveCategory C) : Hom (X.star.tensor  Y.star) (Y.tensor X).star
  | χ_inv (X Y : FreeInvolutiveCategory C) : Hom (Y.tensor X).star (X.star.tensor Y.star)
  | ε_hom (X : FreeInvolutiveCategory C) : Hom X.star.star X
  | ε_inv (X : FreeInvolutiveCategory C) : Hom X X.star.star

scoped infixr:10 " ⟶i " => Hom -- i for "involutive"

@[simp]
def Hom.inv {X Y : FreeInvolutiveCategory C} : (X ⟶i Y) → (Y ⟶i X)
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

-- assuming coherence really blasts through everything... disappointing
def HomEquiv : ∀ {X Y : FreeInvolutiveCategory C}, (X ⟶i Y) → (X ⟶i Y) → Prop := fun _ _ ↦ True
  /- | refl {X Y} (f : X ⟶i Y) : HomEquiv f f -/
  /- | symm {X Y} (f g : X ⟶i Y) : HomEquiv f g → HomEquiv g f -/
  /- | trans {X Y} {f g h : X ⟶i Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h -/
  /- | comp {X Y Z} {f f' : X ⟶i Y} {g g' : Y ⟶i Z} : -/
  /-     HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g') -/
  /- | whiskerLeft (X) {Y Z} (f f' : Y ⟶i Z) : -/
  /-     HomEquiv f f' → HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X) -/
  /- | whiskerRight {Y Z} (f f' : Y ⟶i Z) (X) : -/
  /-     HomEquiv f f' → HomEquiv (f.whiskerRight X) (f'.whiskerRight X) -/
  /- | tensor {W X Y Z} {f f' : W ⟶i X} {g g' : Y ⟶i Z} : -/
  /-     HomEquiv f f' → HomEquiv g g' → HomEquiv (f.tensor g) (f'.tensor g') -/
  /- | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶i Y₁) (g : X₂ ⟶i Y₂) : -/
  /-     HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁)) -/
  /- | comp_id {X Y} (f : X ⟶i Y) : HomEquiv (f.comp (Hom.id _)) f -/
  /- | id_comp {X Y} (f : X ⟶i Y) : HomEquiv ((Hom.id _).comp f) f -/
  /- | assoc {X Y U V : FreeInvolutiveCategory C} (f : X ⟶i U) (g : U ⟶i V) (h : V ⟶i Y) : -/
  /-     HomEquiv ((f.comp g).comp h) (f.comp (g.comp h)) -/
  /- | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _) -/
  /- | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : FreeInvolutiveCategory C} (f₁ : X₁ ⟶i Y₁) (f₂ : X₂ ⟶i Y₂) -/
  /-     (g₁ : Y₁ ⟶i Z₁) (g₂ : Y₂ ⟶i Z₂) : -/
  /-   HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂)) -/
  /- | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y)) -/
  /- | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y)) -/
  /- | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _) -/
  /- | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _) -/
  /- | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶i Y₁) (f₂ : X₂ ⟶i Y₂) (f₃ : X₃ ⟶i Y₃) : -/
  /-     HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃)) -/
  /-       ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃))) -/
  /- | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _) -/
  /- | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _) -/
  /- | ρ_naturality {X Y} (f : X ⟶i Y) : -/
  /-     HomEquiv ((f.whiskerRight unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f) -/
  /- | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _) -/
  /- | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _) -/
  /- | l_naturality {X Y} (f : X ⟶i Y) : -/
  /-     HomEquiv ((f.whiskerLeft unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f) -/
  /- | pentagon {W X Y Z} : -/
  /-     HomEquiv -/
  /-       (((Hom.α_hom W X Y).whiskerRight Z).comp -/
  /-         ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W))) -/
  /-       ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z))) -/
  /- | triangle {X Y} : -/
  /-     HomEquiv ((Hom.α_hom X unit Y).comp ((Hom.l_hom Y).whiskerLeft X)) -/
  /-       ((Hom.ρ_hom X).whiskerRight Y) -/
  /- -- START OF NAT'S STUFF -/
  /- | star {X Y} {f f' : X ⟶i Y} : HomEquiv f f' → HomEquiv f.star f'.star -/
  /- | starHom_id {X} : HomEquiv (Hom.id X).star (Hom.id X.star) -/
  /- | starHom_comp_starHom {X Y Z : FreeInvolutiveCategory C} (f : X ⟶i Y) (g : Y ⟶i Z) : -/
  /-   HomEquiv (f.comp g).star (f.star.comp g.star) -/
  /- | χ_hom_inv {X Y} : HomEquiv ((Hom.χ_hom X Y).comp (Hom.χ_inv X Y)) (Hom.id _) -/
  /- | χ_inv_hom {X Y} : HomEquiv ((Hom.χ_inv X Y).comp (Hom.χ_hom X Y)) (Hom.id _) -/
  /- | χ_naturality {X₁ X₂ Y₁ Y₂} (f : X₁ ⟶i Y₁) (g : X₂ ⟶i Y₂) : -/
  /-   HomEquiv ((f.star.tensor g.star).comp (Hom.χ_hom Y₁ Y₂)) -/
  /-     ((Hom.χ_hom X₁ X₂).comp (g.tensor f).star) -/
  /- | ε_hom_inv {X} : HomEquiv ((Hom.ε_hom X).comp (Hom.ε_inv X)) (Hom.id _) -/
  /- | ε_inv_hom {X} : HomEquiv ((Hom.ε_inv X).comp (Hom.ε_hom X)) (Hom.id _) -/
  /- | ε_naturality {X Y : FreeInvolutiveCategory C} (f : X ⟶i Y) : -/
  /-   HomEquiv (f.star.star.comp (Hom.ε_hom Y)) ((Hom.ε_hom X).comp f) -/
  /- | f3 {P Q R : FreeInvolutiveCategory C} : HomEquiv ((Hom.α_hom P.star Q.star R.star).comp <| -/
  /-   ((Hom.χ_hom Q R).whiskerLeft P.star).comp <| -/
  /-   (Hom.χ_hom P (R.tensor Q)).comp (Hom.α_hom R Q P).star) -/
  /-   (((Hom.χ_hom P Q).whiskerRight R.star).comp (Hom.χ_hom (Q.tensor P) R)) -/
  /- | n2 {P Q : FreeInvolutiveCategory C} : HomEquiv ((Hom.χ_hom P.star Q.star).comp <| -/
  /-   (Hom.χ_hom Q P).star.comp (Hom.ε_hom (P.tensor Q))) -/
  /-   ((Hom.ε_hom P).tensor (Hom.ε_hom Q)) -/
  /- | a {R : FreeInvolutiveCategory C} : HomEquiv (Hom.ε_hom R).star (Hom.ε_hom R.star) -/
  /- | twist_hom_inv {X} : HomEquiv ((Hom.twist_hom X).comp (Hom.twist_inv X)) (Hom.id _) -/
  /- | twist_inv_hom {X} : HomEquiv ((Hom.twist_inv X).comp (Hom.twist_hom X)) (Hom.id _) -/
  /- | twist_naturality {X Y : FreeInvolutiveCategory C} (f : X ⟶ᵐ Y) : -/
  /-   HomEquiv (f.star.comp (Hom.twist_hom Y)) ((Hom.twist_hom X).comp f) -/
  /- | tℓ {P Q R : FreeInvolutiveCategory C} : HomEquiv -/
  /-   (((Hom.χ_hom P.star Q.star).whiskerRight R.star.star).comp <| -/
  /-     ((Hom.twist_hom (Q.star * P.star)).whiskerRight R.star.star).comp <| -/
  /-     (Hom.α_hom Q.star P.star R.star.star).comp <| -/
  /-     ((Hom.χ_hom P R.star).whiskerLeft Q.star).comp <| -/
  /-     ((Hom.twist_hom (R.star * P)).whiskerLeft Q.star).comp <| -/
  /-     (Hom.α_inv Q.star R.star P).comp <| -/
  /-     ((Hom.χ_hom Q R).whiskerRight P).comp <| -/
  /-     ((Hom.twist_hom (R * Q)).whiskerRight P).comp <| -/
  /-     (Hom.α_hom R Q P)) -/
  /-   ((((Hom.twist_hom P.star).tensor (Hom.twist_hom Q.star)).tensor (Hom.twist_hom R.star)).comp <| -/
  /-     ((Hom.χ_hom P Q).whiskerRight R.star).comp <| -/
  /-     (Hom.χ_hom (Q * P) R).comp -/
  /-     (Hom.twist_hom (R * (Q * P)))) -/

instance setoidHom (X Y : FreeInvolutiveCategory C) : Setoid (X ⟶i Y) :=
  ⟨HomEquiv, ⟨fun _ ↦ True.intro, fun _ ↦ True.intro, fun _ _ ↦ True.intro⟩⟩

@[simp, aesop safe]
lemma coherence {X Y : FreeInvolutiveCategory C} {f g : _root_.Quotient (setoidHom X Y)} :
    f = g := by
      rcases f with ⟨f⟩
      rcases g with ⟨g⟩
      exact _root_.Quotient.sound True.intro

instance : Category (FreeInvolutiveCategory C) where
  Hom := fun X Y ↦ _root_.Quotient (setoidHom X Y)
  id X := ⟦Hom.id X⟧
  comp := Quotient.map₂ Hom.comp <| by intros; trivial

instance : MonoidalCategory (FreeInvolutiveCategory C) where
  tensorUnit := FreeInvolutiveCategory.unit
  tensorObj := FreeInvolutiveCategory.tensor
  whiskerLeft X := Quotient.map (Hom.whiskerLeft X) <| by intros; trivial
  whiskerRight f Y := Quotient.map (Hom.whiskerRight · Y) (by intros; trivial) f
  tensorHom := Quotient.map₂ Hom.tensor <| by intros; trivial
  associator := fun X Y Z ↦ {
    hom := ⟦Hom.α_hom X Y Z⟧
    inv := ⟦Hom.α_inv X Y Z⟧
    hom_inv_id := coherence
    inv_hom_id := coherence
  }
  leftUnitor := fun X ↦ {
    hom := ⟦Hom.l_hom X⟧
    inv := ⟦Hom.l_inv X⟧
    hom_inv_id := coherence
    inv_hom_id := coherence
  }
  rightUnitor := fun X ↦ {
    hom := ⟦Hom.ρ_hom X⟧
    inv := ⟦Hom.ρ_inv X⟧
    hom_inv_id := coherence
    inv_hom_id := coherence
  }
  whiskerLeft_id := by intros; exact coherence
  id_whiskerRight := by intros; exact coherence
  tensorHom_def := by intros; exact coherence
  id_tensorHom_id := by intros; exact coherence
  tensorHom_comp_tensorHom := by intros; exact coherence
  associator_naturality := by intros; exact coherence
  leftUnitor_naturality := by intros; exact coherence
  rightUnitor_naturality := by intros; exact coherence
  pentagon := by intros; exact coherence
  triangle := by intros; exact coherence

instance : InvolutiveCategory (FreeInvolutiveCategory C) where
  starObj := FreeInvolutiveCategory.star
  starHom := Quotient.map Hom.star (by intros; trivial)
  skewator := fun X Y ↦ {
    hom := ⟦Hom.χ_hom X Y⟧
    inv := ⟦Hom.χ_inv X Y⟧
    hom_inv_id := coherence
    inv_hom_id := coherence
  }
  involutor := fun X ↦ {
    hom := ⟦Hom.ε_hom X⟧
    inv := ⟦Hom.ε_inv X⟧
    hom_inv_id := coherence
    inv_hom_id := coherence
  }
  starHom_id := by intros; exact coherence
  starHom_comp_starHom := by intros; exact coherence
  skewator_naturality := by intros; exact coherence
  involutor_naturality := by intros; exact coherence
  coherence := by intros; exact coherence

instance : Groupoid (FreeInvolutiveCategory C) where
  inv := Quotient.map Hom.inv (by intros; trivial)
  inv_comp := by intros; exact coherence
  comp_inv := by intros; exact coherence

end CategoryTheory.FreeInvolutiveCategory

