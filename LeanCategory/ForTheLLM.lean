import Mathlib
import LeanCategory.FreeInvolutiveCategory
import LeanCategory.Egger

variable {C : Type u}

namespace CategoryTheory.FreeTwistedCategory

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

infixr:10 " ⟶t " => Hom
-- TODO notation for 𝟙t, ≫t

-- whether a morphism is coherent (aka, doesn't contain twists)
def Hom.pure {X Y : FreeInvolutiveCategory C} : (X ⟶t Y) → Prop
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

inductive HomEquiv : ∀ {X Y : FreeInvolutiveCategory C}, (X ⟶t Y) → (X ⟶t Y) → Prop
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
  | assoc {X Y U V : FreeInvolutiveCategory C} (f : X ⟶t U) (g : U ⟶t V) (h : V ⟶t Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
  | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : FreeInvolutiveCategory C} (f₁ : X₁ ⟶t Y₁) (f₂ : X₂ ⟶t Y₂)
      (g₁ : Y₁ ⟶t Z₁) (g₂ : Y₂ ⟶t Z₂) :
    HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
  | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶t Y₁) (f₂ : X₂ ⟶t Y₂) (f₃ : X₃ ⟶t Y₃) :
      HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
        ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  | ρ_naturality {X Y} (f : X ⟶t Y) :
      HomEquiv ((f.whiskerRight .unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  | l_naturality {X Y} (f : X ⟶t Y) :
      HomEquiv ((f.whiskerLeft .unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  | pentagon {W X Y Z} :
      HomEquiv
        (((Hom.α_hom W X Y).whiskerRight Z).comp
          ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
        ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  | triangle {X Y} :
      HomEquiv ((Hom.α_hom X .unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
        ((Hom.ρ_hom X).whiskerRight Y)
  | star {X Y} {f f' : X ⟶t Y} : HomEquiv f f' → HomEquiv f.star f'.star
  | starHom_id {X} : HomEquiv (Hom.id X).star (Hom.id X.star)
  | starHom_comp_starHom {X Y Z : FreeInvolutiveCategory C} (f : X ⟶t Y) (g : Y ⟶t Z) :
    HomEquiv (f.comp g).star (f.star.comp g.star)
  | χ_hom_inv {X Y} : HomEquiv ((Hom.χ_hom X Y).comp (Hom.χ_inv X Y)) (Hom.id _)
  | χ_inv_hom {X Y} : HomEquiv ((Hom.χ_inv X Y).comp (Hom.χ_hom X Y)) (Hom.id _)
  | χ_naturality {X₁ X₂ Y₁ Y₂} (f : X₁ ⟶t Y₁) (g : X₂ ⟶t Y₂) :
    HomEquiv ((f.star.tensor g.star).comp (Hom.χ_hom Y₁ Y₂))
      ((Hom.χ_hom X₁ X₂).comp (g.tensor f).star)
  | ε_hom_inv {X} : HomEquiv ((Hom.ε_hom X).comp (Hom.ε_inv X)) (Hom.id _)
  | ε_inv_hom {X} : HomEquiv ((Hom.ε_inv X).comp (Hom.ε_hom X)) (Hom.id _)
  | ε_naturality {X Y : FreeInvolutiveCategory C} (f : X ⟶t Y) :
    HomEquiv (f.star.star.comp (Hom.ε_hom Y)) ((Hom.ε_hom X).comp f)
  | f3 {P Q R : FreeInvolutiveCategory C} : HomEquiv ((Hom.α_hom P.star Q.star R.star).comp <|
    ((Hom.χ_hom Q R).whiskerLeft P.star).comp <|
    (Hom.χ_hom P (R.tensor Q)).comp (Hom.α_hom R Q P).star)
    (((Hom.χ_hom P Q).whiskerRight R.star).comp (Hom.χ_hom (Q.tensor P) R))
  | n2 {P Q : FreeInvolutiveCategory C} : HomEquiv ((Hom.χ_hom P.star Q.star).comp <|
    (Hom.χ_hom Q P).star.comp (Hom.ε_hom (P.tensor Q)))
    ((Hom.ε_hom P).tensor (Hom.ε_hom Q))
  | a {R : FreeInvolutiveCategory C} : HomEquiv (Hom.ε_hom R).star (Hom.ε_hom R.star)
  | twist_hom_inv {X} : HomEquiv ((Hom.twist_hom X).comp (Hom.twist_inv X)) (Hom.id _)
  | twist_inv_hom {X} : HomEquiv ((Hom.twist_inv X).comp (Hom.twist_hom X)) (Hom.id _)
  | twist_naturality {X Y : FreeInvolutiveCategory C} (f : X ⟶t Y) :
    HomEquiv (f.star.comp (Hom.twist_hom Y)) ((Hom.twist_hom X).comp f)
  | tℓ {P Q R : FreeInvolutiveCategory C} : HomEquiv
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
  | coherence (X Y : FreeInvolutiveCategory C) (f g : X ⟶t Y) : f.pure → g.pure → HomEquiv f g
  | symm {X Y} (f g : X ⟶t Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : X ⟶t Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h

instance setoidHom (X Y : FreeInvolutiveCategory C) : Setoid (X ⟶t Y) :=
  ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

open HomEquiv

instance categoryFreeTwistedCategory : Category.{u, u} (FreeInvolutiveCategory C) where
  Hom X Y := _root_.Quotient (setoidHom X Y)
  id X := ⟦Hom.id X⟧
  comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg)
  id_comp := by
    rintro X Y ⟨f⟩
    exact _root_.Quotient.sound (id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact _root_.Quotient.sound (comp_id f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact _root_.Quotient.sound (assoc f g h)

instance monoidalFreeTwistedCategory : MonoidalCategory (FreeInvolutiveCategory C) where
  tensorObj X Y := .tensor X Y
  tensorHom := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg)
  whiskerLeft X _ _ f := Quot.map (fun f ↦ Hom.whiskerLeft X f) (fun f f' ↦ .whiskerLeft X f f') f
  whiskerRight f Y := Quot.map (fun f ↦ Hom.whiskerRight f Y) (fun f f' ↦ .whiskerRight f f' Y) f
  tensorHom_def {W X Y Z} := by
    rintro ⟨f⟩ ⟨g⟩
    exact _root_.Quotient.sound (HomEquiv.tensorHom_def _ _)
  id_tensorHom_id _ _ := _root_.Quotient.sound id_tensorHom_id
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact _root_.Quotient.sound (tensorHom_comp_tensorHom _ _ _ _)
  whiskerLeft_id X Y := Quot.sound (HomEquiv.whiskerLeft_id X Y)
  id_whiskerRight X Y := Quot.sound (HomEquiv.id_whiskerRight X Y)
  tensorUnit := .unit
  associator X Y Z := ⟨⟦Hom.α_hom X Y Z⟧, ⟦Hom.α_inv X Y Z⟧,
    _root_.Quotient.sound α_hom_inv, _root_.Quotient.sound α_inv_hom⟩
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    exact _root_.Quotient.sound (associator_naturality _ _ _)
  leftUnitor X := ⟨⟦Hom.l_hom X⟧, ⟦Hom.l_inv X⟧,
    _root_.Quotient.sound l_hom_inv, _root_.Quotient.sound l_inv_hom⟩
  leftUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    exact _root_.Quotient.sound (l_naturality _)
  rightUnitor X :=
    ⟨⟦Hom.ρ_hom X⟧, ⟦Hom.ρ_inv X⟧, _root_.Quotient.sound ρ_hom_inv, _root_.Quotient.sound ρ_inv_hom⟩
  rightUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    exact _root_.Quotient.sound (ρ_naturality _)
  pentagon _ _ _ _ := _root_.Quotient.sound pentagon
  triangle _ _ := _root_.Quotient.sound triangle

instance involutiveFreeTwistedCategory : InvolutiveCategory (FreeInvolutiveCategory C) where
  starObj X := X.star
  starHom := Quotient.map Hom.star (fun _ _ hf  ↦ HomEquiv.star hf)
  starHom_id _ := Quot.sound starHom_id
  starHom_comp_starHom {X Y Z} := by
    rintro ⟨f⟩ ⟨g⟩
    exact _root_.Quotient.sound (starHom_comp_starHom _ _)
  skewator X Y := ⟨⟦Hom.χ_hom X Y⟧, ⟦Hom.χ_inv X Y⟧,
    _root_.Quotient.sound χ_hom_inv, _root_.Quotient.sound χ_inv_hom⟩
  skewator_naturality {X₁ X₂ Y₁ Y₂} := by
    rintro ⟨f₁⟩ ⟨f₂⟩
    exact _root_.Quotient.sound (χ_naturality _ _)
  involutor X := ⟨⟦Hom.ε_hom X⟧, ⟦Hom.ε_inv X⟧,
    _root_.Quotient.sound ε_hom_inv, _root_.Quotient.sound ε_inv_hom⟩
  involutor_naturality {X Y} := by
    rintro ⟨f⟩
    exact _root_.Quotient.sound (HomEquiv.ε_naturality _)
  f3 _ _ _ := _root_.Quotient.sound f3
  n2 _ _ := _root_.Quotient.sound n2
  a _ := _root_.Quotient.sound a

instance freeTwistedCategory : TwistedCategory (FreeInvolutiveCategory C) where
  twist X := ⟨⟦Hom.twist_hom X⟧, ⟦Hom.twist_inv X⟧,
    _root_.Quotient.sound twist_hom_inv, _root_.Quotient.sound twist_inv_hom⟩
  twist_naturality {X Y} := by
    rintro ⟨f⟩
    exact _root_.Quotient.sound (HomEquiv.twist_naturality _)
  tℓ _ _ _ := _root_.Quotient.sound tℓ

@[simp]
def homMk {X Y : FreeInvolutiveCategory V} (f : X ⟶t Y) : categoryFreeTwistedCategory.Hom X Y := ⟦f⟧

@[simp]
theorem mk_comp {X Y Z : FreeInvolutiveCategory C} (f : X ⟶t Y) (g : Y ⟶t Z) :
    ⟦f.comp g⟧ = @CategoryStruct.comp (FreeInvolutiveCategory C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_id {X : FreeInvolutiveCategory C} : ⟦Hom.id X⟧ = 𝟙 X :=
  rfl

open MonoidalCategory

@[simp]
theorem mk_tensor {X₁ Y₁ X₂ Y₂ : FreeInvolutiveCategory C} (f : X₁ ⟶t Y₁) (g : X₂ ⟶t Y₂) :
    ⟦f.tensor g⟧ = @MonoidalCategory.tensorHom (FreeInvolutiveCategory C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_whiskerLeft {X Y₁ Y₂ : FreeInvolutiveCategory C} (f : Y₁ ⟶t Y₂) :
    ⟦f.whiskerLeft X⟧ = X ◁ ⟦f⟧ := rfl

@[simp]
theorem mk_whiskerRight {X₁ X₂ Y : FreeInvolutiveCategory C} (f : X₁ ⟶t X₂) :
    ⟦f.whiskerRight Y⟧ = ⟦f⟧ ▷ Y := rfl

@[simp]
theorem mk_α_hom {X Y Z : FreeInvolutiveCategory C} : ⟦Hom.α_hom X Y Z⟧ = (α_ X Y Z).hom :=
  rfl

@[simp]
theorem mk_α_inv {X Y Z : FreeInvolutiveCategory C} : ⟦Hom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
  rfl

@[simp]
theorem mk_ρ_hom {X : FreeInvolutiveCategory C} : ⟦Hom.ρ_hom X⟧ = (ρ_ X).hom :=
  rfl

@[simp]
theorem mk_ρ_inv {X : FreeInvolutiveCategory C} : ⟦Hom.ρ_inv X⟧ = (ρ_ X).inv :=
  rfl

@[simp]
theorem mk_l_hom {X : FreeInvolutiveCategory C} : ⟦Hom.l_hom X⟧ = (λ_ X).hom :=
  rfl

@[simp]
theorem mk_l_inv {X : FreeInvolutiveCategory C} : ⟦Hom.l_inv X⟧ = (λ_ X).inv :=
  rfl

@[simp]
theorem tensor_eq_tensor {X Y : FreeInvolutiveCategory C} : X.tensor Y = X ⊗ Y :=
  rfl

@[simp]
theorem unit_eq_unit : FreeInvolutiveCategory.unit = 𝟙_ (FreeInvolutiveCategory C) :=
  rfl

open InvolutiveCategory

@[simp]
theorem mk_star {X Y : FreeInvolutiveCategory C} (f : X ⟶t Y) :
    ⟦f.star⟧ = @InvolutiveCategoryStruct.starHom (FreeInvolutiveCategory C) _ _ _ _ _ ⟦f⟧ :=
  rfl

@[simp]
theorem mk_ε_hom {X : FreeInvolutiveCategory C} : ⟦Hom.ε_hom X⟧ = (e_ X).hom :=
  rfl

@[simp]
theorem mk_ε_inv {X : FreeInvolutiveCategory C} : ⟦Hom.ε_inv X⟧ = (e_ X).inv :=
  rfl

@[simp]
theorem mk_χ_hom {X Y : FreeInvolutiveCategory C} : ⟦Hom.χ_hom X Y⟧ = (χ_ X Y).hom :=
  rfl

@[simp]
theorem mk_χ_inv {X Y : FreeInvolutiveCategory C} : ⟦Hom.χ_inv X Y⟧ = (χ_ X Y).inv :=
  rfl

@[simp]
theorem star_eq_star {X : FreeInvolutiveCategory C} : X.star = X⋆ :=
  rfl

open TwistedCategory

@[simp]
theorem mk_ς_hom {X : FreeInvolutiveCategory C} : ⟦Hom.twist_hom X⟧ = (ς_ X).hom :=
  rfl

@[simp]
theorem mk_ς_hom' {X : FreeInvolutiveCategory C} : ⟦Hom.twist_hom X⟧ = (TwistedCategoryStruct.twist X).hom :=
  rfl

@[simp]
theorem mk_ς_inv {X : FreeInvolutiveCategory C} : ⟦Hom.twist_inv X⟧ = (ς_ X).inv :=
  rfl

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

end CategoryTheory.FreeTwistedCategory

