import Mathlib
import LeanCategory.Egger
import LeanCategory.FreeTwistedCategoryQuiverBase

namespace CategoryTheory.FreeTwistedCategoryQuiver

open CategoryTheory.FreeTwistedCategory

variable {C : Type u} [Quiver.{v} (T C)]

inductive HomEquiv : ∀ {X Y : TQ C}, (X ⟶tq Y) → (X ⟶tq Y) → Prop
  | refl {X Y} (f : X ⟶tq Y) : HomEquiv f f
  | comp {X Y Z} {f f' : X ⟶tq Y} {g g' : Y ⟶tq Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
  | whiskerLeft (X) {Y Z} (f f' : Y ⟶tq Z) :
      HomEquiv f f' → HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
  | whiskerRight {Y Z} (f f' : Y ⟶tq Z) (X) :
      HomEquiv f f' → HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
  | tensor {W X Y Z} {f f' : W ⟶tq X} {g g' : Y ⟶tq Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.tensor g) (f'.tensor g')
  | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶tq Y₁) (g : X₂ ⟶tq Y₂) :
      HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
  | comp_id {X Y} (f : X ⟶tq Y) : HomEquiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : X ⟶tq Y) : HomEquiv ((Hom.id _).comp f) f
  | assoc {X Y U V : TQ C} (f : X ⟶tq U) (g : U ⟶tq V) (h : V ⟶tq Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : TQ C} (f₁ : X₁ ⟶tq Y₁) (f₂ : X₂ ⟶tq Y₂)
      (g₁ : Y₁ ⟶tq Z₁) (g₂ : Y₂ ⟶tq Z₂) :
    HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
  | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶tq Y₁) (f₂ : X₂ ⟶tq Y₂) (f₃ : X₃ ⟶tq Y₃) :
      HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
        ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  | ρ_naturality {X Y} (f : X ⟶tq Y) :
      HomEquiv ((f.whiskerRight .unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  | l_naturality {X Y} (f : X ⟶tq Y) :
      HomEquiv ((f.whiskerLeft .unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  -- START OF NAT'S STUFF
  | star {X Y} {f f' : X ⟶tq Y} : HomEquiv f f' → HomEquiv f.star f'.star
  | starHom_comp_starHom {X Y Z : TQ C} (f : X ⟶tq Y) (g : Y ⟶tq Z) :
    HomEquiv (f.comp g).star (f.star.comp g.star)
  | χ_naturality {X₁ X₂ Y₁ Y₂} (f : X₁ ⟶tq Y₁) (g : X₂ ⟶tq Y₂) :
    HomEquiv ((f.star.tensor g.star).comp (Hom.χ_hom Y₁ Y₂))
      ((Hom.χ_hom X₁ X₂).comp (g.tensor f).star)
  | ε_naturality {X Y : TQ C} (f : X ⟶tq Y) :
    HomEquiv (f.star.star.comp (Hom.ε_hom Y)) ((Hom.ε_hom X).comp f)
  | twist_hom_inv {X} : HomEquiv ((Hom.twist_hom X).comp (Hom.twist_inv X)) (Hom.id _)
  | twist_inv_hom {X} : HomEquiv ((Hom.twist_inv X).comp (Hom.twist_hom X)) (Hom.id _)
  | twist_naturality {X Y : TQ C} (f : X ⟶tq Y) :
    HomEquiv (f.star.comp (Hom.twist_hom Y)) ((Hom.twist_hom X).comp f)
  | tℓ {P Q R : TQ C} : HomEquiv
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
  | coherence (X Y : TQ C) (f g : X ⟶tq Y) : f.Pure → g.Pure → HomEquiv f g
  | symm {X Y} (f g : X ⟶tq Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : X ⟶tq Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h

instance setoidHom (X Y : TQ C) : Setoid (X ⟶tq Y) :=
  ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

macro "coherence" : tactic =>
  `(tactic|
    (intros; apply _root_.Quotient.sound; apply HomEquiv.coherence <;> repeat' constructor)
  )

instance : Category.{max u v, u} (TQ C) where
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

instance : MonoidalCategory (TQ C) where
  tensorUnit := .unit
  tensorObj X Y := .tensor X Y
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

instance : InvolutiveCategoryStruct (TQ C) where
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

lemma coherence_Pure {X Y : TQ C} : ∀ f : X ⟶ Y, InvolutiveCoherence f →
    ∃ f', f'.Pure ∧ f = ⟦f'⟧ := by
  intros f hf
  induction hf
  case id =>
    exists .id _
  case comp f g _ _ hf hg =>
    rcases hf with ⟨f', ⟨hf', hf⟩⟩
    subst f
    rcases hg with ⟨g', ⟨hg', hg⟩⟩
    subst g
    exists f'.comp g'
  case tensor f _ _ g _ _ hf hg =>
    rcases hf with ⟨f', ⟨hf', hf⟩⟩
    subst f
    rcases hg with ⟨g', ⟨hg', hg⟩⟩
    subst g
    exists f'.tensor g'
  case whiskerLeft f X _ hf =>
    rcases hf with ⟨f', ⟨hf', hf⟩⟩
    subst f
    exists f'.whiskerLeft X
  case whiskerRight f Y _ hf =>
    rcases hf with ⟨f', ⟨hf', hf⟩⟩
    subst f
    exists f'.whiskerRight Y
  case starHom f _ hf =>
    rcases hf with ⟨f', ⟨hf', hf⟩⟩
    subst f
    exists f'.star
  case associator_hom _ _ _ =>
    exists Hom.α_hom _ _ _
  case associator_inv _ _ _ =>
    exists Hom.α_inv _ _ _
  case leftUnitor_hom _ =>
    exists Hom.l_hom _
  case leftUnitor_inv _ =>
    exists Hom.l_inv _
  case rightUnitor_hom _ =>
    exists Hom.ρ_hom _
  case rightUnitor_inv _ =>
    exists Hom.ρ_inv _
  case skewator_hom _ _ =>
    exists Hom.χ_hom _ _
  case skewator_inv _ _ =>
    exists Hom.χ_inv _ _
  case involutor_hom _ =>
    exists Hom.ε_hom _
  case involutor_inv _ =>
    exists Hom.ε_inv _

instance : InvolutiveCategory (TQ C) where
  starHom_id := by coherence
  starHom_comp_starHom := by rintro _ _ _ ⟨f⟩ ⟨g⟩; apply _root_.Quotient.sound; constructor
  skewator_naturality := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩; apply _root_.Quotient.sound; constructor
  involutor_naturality := by rintro _ _ ⟨f⟩; apply _root_.Quotient.sound; constructor
  coherence := by
    intros X Y f g hf hg
    apply coherence_Pure at hf
    rcases hf with ⟨f', ⟨hf', hf⟩⟩
    subst f
    apply coherence_Pure at hg
    rcases hg with ⟨g', ⟨hg', hg⟩⟩
    subst g
    apply _root_.Quotient.sound
    constructor <;> assumption

instance : TwistedCategory (TQ C) where
  twist X := {
    hom := ⟦Hom.twist_hom X⟧
    inv := ⟦Hom.twist_inv X⟧
    hom_inv_id := _root_.Quotient.sound HomEquiv.twist_hom_inv
    inv_hom_id := _root_.Quotient.sound HomEquiv.twist_inv_hom
  }
  twist_naturality := by rintro _ _ ⟨f⟩; apply _root_.Quotient.sound; constructor
  tℓ := by
    intros
    apply _root_.Quotient.sound
    constructor

-- preparation for groupoid: simplifying lemmas

@[simp]
def homMk {X Y : TQ C} (f : X ⟶tq Y) : X ⟶ Y := ⟦f⟧

@[simp]
theorem mk_comp {X Y Z : TQ C} (f : X ⟶tq Y) (g : Y ⟶tq Z) :
    ⟦f.comp g⟧ = @CategoryStruct.comp (TQ C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_id {X : TQ C} : ⟦Hom.id X⟧ = 𝟙 X :=
  rfl

open MonoidalCategory

@[simp]
theorem mk_tensor {X₁ Y₁ X₂ Y₂ : TQ C} (f : X₁ ⟶tq Y₁) (g : X₂ ⟶tq Y₂) :
    ⟦f.tensor g⟧ = @MonoidalCategory.tensorHom (TQ C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_whiskerLeft {X Y₁ Y₂ : TQ C} (f : Y₁ ⟶tq Y₂) :
    ⟦f.whiskerLeft X⟧ = X ◁ ⟦f⟧ := rfl

@[simp]
theorem mk_whiskerRight {X₁ X₂ Y : TQ C} (f : X₁ ⟶tq X₂) :
    ⟦f.whiskerRight Y⟧ = ⟦f⟧ ▷ Y := rfl

@[simp]
theorem mk_α_hom {X Y Z : TQ C} : ⟦Hom.α_hom X Y Z⟧ = (α_ X Y Z).hom :=
  rfl

@[simp]
theorem mk_α_inv {X Y Z : TQ C} : ⟦Hom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
  rfl

@[simp]
theorem mk_ρ_hom {X : TQ C} : ⟦Hom.ρ_hom X⟧ = (ρ_ X).hom :=
  rfl

@[simp]
theorem mk_ρ_inv {X : TQ C} : ⟦Hom.ρ_inv X⟧ = (ρ_ X).inv :=
  rfl

@[simp]
theorem mk_l_hom {X : TQ C} : ⟦Hom.l_hom X⟧ = (λ_ X).hom :=
  rfl

@[simp]
theorem mk_l_inv {X : TQ C} : ⟦Hom.l_inv X⟧ = (λ_ X).inv :=
  rfl

@[simp]
theorem tensor_eq_tensor {X Y : TQ C} : X.tensor Y = X ⊗ Y :=
  rfl

@[simp]
theorem unit_eq_unit : FreeTwistedCategoryQuiver.unit = 𝟙_ (TQ C) :=
  rfl

open InvolutiveCategory

@[simp]
theorem mk_star {X Y : TQ C} (f : X ⟶tq Y) :
    ⟦f.star⟧ = @InvolutiveCategoryStruct.starHom (TQ C) _ _ _ _ _ ⟦f⟧ :=
  rfl

@[simp]
theorem mk_ε_hom {X : TQ C} : ⟦Hom.ε_hom X⟧ = (e_ X).hom :=
  rfl

@[simp]
theorem mk_ε_inv {X : TQ C} : ⟦Hom.ε_inv X⟧ = (e_ X).inv :=
  rfl

@[simp]
theorem mk_χ_hom {X Y : TQ C} : ⟦Hom.χ_hom X Y⟧ = (χ_ X Y).hom :=
  rfl

@[simp]
theorem mk_χ_inv {X Y : TQ C} : ⟦Hom.χ_inv X Y⟧ = (χ_ X Y).inv :=
  rfl

@[simp]
theorem star_eq_star {X : TQ C} : X.star = X⋆ :=
  rfl

open TwistedCategory

@[simp]
theorem mk_ς_hom {X : TQ C} : ⟦Hom.twist_hom X⟧ = (ς_ X).hom :=
  rfl

@[simp]
theorem mk_ς_hom' {X : TQ C} : ⟦Hom.twist_hom X⟧ = (TwistedCategoryStruct.twist X).hom :=
  rfl

@[simp]
theorem mk_ς_inv {X : TQ C} : ⟦Hom.twist_inv X⟧ = (ς_ X).inv :=
  rfl

-- if you've got a ⟦Hom ...⟧, this breaks
-- it up so we can use category-level rewrites
-- instead of Quotient.sound into HomEquiv
macro "simp_mk" : tactic =>
  `(tactic|
    repeat1 (first
      | simp
      | rw [mk_comp]
      | rw [mk_id]
      | rw [mk_tensor]
      | rw [mk_whiskerLeft]
      | rw [mk_whiskerRight]
      | rw [mk_α_hom]
      | rw [mk_α_inv]
      | rw [mk_ρ_hom]
      | rw [mk_ρ_inv]
      | rw [mk_l_hom]
      | rw [mk_l_inv]
      | rw [tensor_eq_tensor]
      | rw [tensor_eq_tensor']
      | rw [unit_eq_unit]
      | rw [unit_eq_unit']
      | rw [mk_star]
      | rw [mk_ε_hom]
      | rw [mk_ε_inv]
      | rw [mk_χ_hom]
      | rw [mk_χ_inv]
      | rw [star_eq_star]
      | rw [star_eq_star']
      | rw [mk_ς_hom]
      | rw [mk_ς_inv]
      | rw [twist_inv_naturality]
      | fail "Nothing to do!"
    )
  )

end CategoryTheory.FreeTwistedCategoryQuiver

