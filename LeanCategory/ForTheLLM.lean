import Mathlib
open CategoryTheory

open Category MonoidalCategory

namespace CategoryTheory

class InvolutiveCategoryStruct (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  starObj : C → C
  starHom : (X ⟶ Y) → (starObj X ⟶ starObj Y)
  skewator : ∀ X Y : C, (starObj X ⊗ starObj Y) ≅ starObj (Y ⊗ X)
  involutor : ∀ X : C, starObj (starObj X) ≅ X

namespace InvolutiveCategory

scoped postfix:max "⋆" => InvolutiveCategoryStruct.starObj
scoped postfix:max "⋆" => InvolutiveCategoryStruct.starHom
scoped notation "χ_" => InvolutiveCategoryStruct.skewator
scoped notation "e_" => InvolutiveCategoryStruct.involutor

end InvolutiveCategory

open InvolutiveCategory

class InvolutiveCategory (C : Type u)
    [Category.{v} C] [MonoidalCategory C] extends InvolutiveCategoryStruct C where
  starHom_id : ∀ X : C, (𝟙 X)⋆ = 𝟙 X⋆ := by cat_disch
  starHom_comp_starHom : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      (f ≫ g)⋆ = f⋆ ≫ g⋆ := by cat_disch
  skewator_naturality : ∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      (f⋆ ⊗ₘ g⋆) ≫ (χ_ Y₁ Y₂).hom = (χ_ X₁ X₂).hom ≫ (g ⊗ₘ f)⋆ := by cat_disch
  involutor_naturality : ∀ {X Y : C} (f : X ⟶ Y),
      f⋆⋆ ≫ (e_ Y).hom = (e_ X).hom ≫ f
  f3 : ∀ P Q R : C,
      (α_ P⋆ Q⋆ R⋆).hom ≫ (P⋆ ◁ (χ_ Q R).hom) ≫ (χ_ P (R ⊗ Q)).hom ≫ (α_ R Q P).hom⋆ =
        ((χ_ P Q).hom ▷ R⋆) ≫ (χ_ (Q ⊗ P) R).hom := by cat_disch
  n2 : ∀ P Q : C,
      (χ_ P⋆ Q⋆).hom ≫ (χ_ Q P).hom⋆ ≫ (e_ (P ⊗ Q)).hom =
        (e_ P).hom ⊗ₘ (e_ Q).hom := by cat_disch
  a : ∀ R : C,
      (e_ R).hom⋆ = (e_ R⋆).hom := by cat_disch

attribute [reassoc (attr := simp), simp] InvolutiveCategory.starHom_id
attribute [reassoc (attr := simp), simp] InvolutiveCategory.starHom_comp_starHom
attribute [reassoc] InvolutiveCategory.skewator_naturality
attribute [reassoc] InvolutiveCategory.involutor_naturality
attribute [reassoc (attr := simp), simp] InvolutiveCategory.f3
attribute [reassoc (attr := simp), simp] InvolutiveCategory.n2
attribute [reassoc (attr := simp), simp] InvolutiveCategory.a

namespace InvolutiveCategory

variable {C : Type u} [𝒞 : Category.{v} C] [MonoidalCategory C] [InvolutiveCategory C]

@[reassoc]
theorem skewator_inv_naturality :
    ∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      (g ⊗ₘ f)⋆ ≫ (χ_ Y₁ Y₂).inv = (χ_ X₁ X₂).inv ≫ (f⋆ ⊗ₘ g⋆) := by
  intros _ _ _ _ f g
  rw [← id_comp (_ ≫ _)]
  rw [← (χ_ _ _).inv_hom_id]
  simp only [Category.assoc]
  rw [← skewator_naturality_assoc f g]
  simp

@[reassoc]
theorem involutor_inv_naturality :
    ∀ {X Y : C} (f : X ⟶ Y),
      f ≫ (e_ Y).inv = (e_ X).inv ≫ f⋆⋆ := by
  intros _ _ f
  rw [← id_comp (_ ≫ _)]
  rw [← (e_ _).inv_hom_id]
  simp only [Category.assoc]
  rw [← involutor_naturality_assoc f]
  simp

@[reassoc (attr := simp)]
theorem hom_inv_star {X Y : C} (f : X ≅ Y) :
    f.hom⋆ ≫ f.inv⋆ = 𝟙 X⋆ := by
  rw [← starHom_comp_starHom]
  simp

@[reassoc (attr := simp)]
theorem hom_inv_star' {X Y : C} (f : X ⟶ Y) [IsIso f] :
    f⋆ ≫ (inv f)⋆ = 𝟙 X⋆ := by
  rw [← starHom_comp_starHom]
  simp

@[reassoc (attr := simp)]
theorem inv_hom_star {X Y : C} (f : X ≅ Y) :
    f.inv⋆ ≫ f.hom⋆ = 𝟙 Y⋆ := by
  rw [← starHom_comp_starHom]
  simp

@[reassoc (attr := simp)]
theorem inv_hom_star' {X Y : C} (f : X ⟶ Y) [IsIso f] :
    (inv f)⋆ ≫ f⋆ = 𝟙 Y⋆ := by
  rw [← starHom_comp_starHom]
  simp

@[simps!]
def starIso {X Y : C} (f : X ≅ Y) : X⋆≅ Y⋆ where
  hom := f.hom⋆
  inv := f.inv⋆

instance star_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso f⋆ :=
  (starIso (asIso f)).isIso_hom

@[simp]
theorem inv_star {X Y : C} (f : X ⟶ Y) [hf : IsIso f] :
    inv f⋆ = (inv f)⋆ := by
  rw [← id_comp (inv f⋆)]
  rw [← starHom_id]
  rw [← hf.inv_hom_id]
  cat_disch

@[reassoc (attr := simp), simp]
theorem starHom_tensorHom {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g)⋆ = (χ_ _ _).inv ≫ (g⋆ ⊗ₘ f⋆) ≫ (χ_ _ _).hom := by
  rw [skewator_naturality, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp), simp]
theorem starHom_whiskerLeft {X X' Y : C} (f : X ⟶ X') :
    (Y ◁ f)⋆ = (χ_ _ _).inv ≫ (f⋆ ▷ Y⋆) ≫ (χ_ _ _).hom := by
  rw [← id_tensorHom, starHom_tensorHom]
  simp

@[reassoc (attr := simp), simp]
theorem starHom_whiskerRight {X X' Y : C} (f : X ⟶ X') :
    (f ▷ Y)⋆ = (χ_ _ _).inv ≫ ((InvolutiveCategoryStruct.starObj Y) ◁ f⋆) ≫ (χ_ _ _).hom := by
  rw [← tensorHom_id, starHom_tensorHom]
  simp

@[reassoc (attr := simp), simp]
theorem involutor_conjugation {X X' : C} (f : X ⟶ X') :
    f⋆⋆ = (e_ _).hom ≫ f ≫ (e_ _).inv := by
  rw [involutor_inv_naturality, Iso.hom_inv_id_assoc]

def star_tensorObj : (𝟙_ C)⋆ ≅ 𝟙_ C :=
  (ρ_ _).symm ≪≫ whiskerLeftIso _ (e_ _).symm ≪≫ χ_ _ _ ≪≫ starIso (ρ_ _) ≪≫ e_ _

@[reassoc (attr := simp), simp]
theorem f3_inv : ∀ P Q R : C,
    (α_ R Q P).inv⋆ ≫ (χ_ P (R ⊗ Q)).inv ≫ (P⋆ ◁ (χ_ Q R).inv) ≫ (α_ P⋆ Q⋆ R⋆).inv =
      (χ_ (Q ⊗ P) R).inv ≫ ((χ_ P Q).inv ▷ R⋆) := by
  intros P Q R
  exact eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp), simp]
theorem n2_inv : ∀ P Q : C,
      (e_ (P ⊗ Q)).inv ≫ (χ_ Q P).inv⋆ ≫ (χ_ P⋆ Q⋆).inv =
        (e_ P).inv ⊗ₘ (e_ Q).inv := by
  intros P Q
  exact eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp), simp]
theorem a_inv : ∀ R : C,
    (e_ R).inv⋆ = (e_ R⋆).inv := by
  intros R
  exact eq_of_inv_eq_inv (by simp)

end InvolutiveCategory

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

variable {C : Type u}

scoped notation "I" => FreeInvolutiveCategory

def sizeOf : I C → ℕ
  | of _ => 0
  | unit => 0
  | tensor X Y => X.sizeOf + Y.sizeOf + 1
  | star X => X.sizeOf + 1

inductive Hom : I C → I C → Type u
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
def Hom.inv {X Y : I C} : (X ⟶i Y) → (Y ⟶i X)
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

inductive HomEquiv : ∀ {X Y : I C}, (X ⟶i Y) → (X ⟶i Y) → Prop
  | refl {X Y} (f : X ⟶i Y) : HomEquiv f f
  | comp {X Y Z} {f f' : X ⟶i Y} {g g' : Y ⟶i Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
  | whiskerLeft (X) {Y Z} (f f' : Y ⟶i Z) :
      HomEquiv f f' → HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
  | whiskerRight {Y Z} (f f' : Y ⟶i Z) (X) :
      HomEquiv f f' → HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
  | tensor {W X Y Z} {f f' : W ⟶i X} {g g' : Y ⟶i Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.tensor g) (f'.tensor g')
  | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶i Y₁) (g : X₂ ⟶i Y₂) :
      HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
  | comp_id {X Y} (f : X ⟶i Y) : HomEquiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : X ⟶i Y) : HomEquiv ((Hom.id _).comp f) f
  | assoc {X Y U V : I C} (f : X ⟶i U) (g : U ⟶i V) (h : V ⟶i Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
  | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : I C} (f₁ : X₁ ⟶i Y₁) (f₂ : X₂ ⟶i Y₂)
      (g₁ : Y₁ ⟶i Z₁) (g₂ : Y₂ ⟶i Z₂) :
    HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
  | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶i Y₁) (f₂ : X₂ ⟶i Y₂) (f₃ : X₃ ⟶i Y₃) :
      HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
        ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  | ρ_naturality {X Y} (f : X ⟶i Y) :
      HomEquiv ((f.whiskerRight .unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  | l_naturality {X Y} (f : X ⟶i Y) :
      HomEquiv ((f.whiskerLeft .unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  | pentagon {W X Y Z} :
      HomEquiv
        (((Hom.α_hom W X Y).whiskerRight Z).comp
          ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
        ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  | triangle {X Y} :
      HomEquiv ((Hom.α_hom X unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
        ((Hom.ρ_hom X).whiskerRight Y)
  | star {X Y} {f f' : X ⟶i Y} : HomEquiv f f' → HomEquiv f.star f'.star
  | starHom_id {X} : HomEquiv (Hom.id X).star (Hom.id X.star)
  | starHom_comp_starHom {X Y Z : I C} (f : X ⟶i Y) (g : Y ⟶i Z) :
    HomEquiv (f.comp g).star (f.star.comp g.star)
  | χ_hom_inv {X Y} : HomEquiv ((Hom.χ_hom X Y).comp (Hom.χ_inv X Y)) (Hom.id _)
  | χ_inv_hom {X Y} : HomEquiv ((Hom.χ_inv X Y).comp (Hom.χ_hom X Y)) (Hom.id _)
  | χ_naturality {X₁ X₂ Y₁ Y₂} (f : X₁ ⟶i Y₁) (g : X₂ ⟶i Y₂) :
    HomEquiv ((f.star.tensor g.star).comp (Hom.χ_hom Y₁ Y₂))
      ((Hom.χ_hom X₁ X₂).comp (g.tensor f).star)
  | ε_hom_inv {X} : HomEquiv ((Hom.ε_hom X).comp (Hom.ε_inv X)) (Hom.id _)
  | ε_inv_hom {X} : HomEquiv ((Hom.ε_inv X).comp (Hom.ε_hom X)) (Hom.id _)
  | ε_naturality {X Y : I C} (f : X ⟶i Y) :
    HomEquiv (f.star.star.comp (Hom.ε_hom Y)) ((Hom.ε_hom X).comp f)
  | f3 {P Q R : I C} : HomEquiv ((Hom.α_hom P.star Q.star R.star).comp <|
    ((Hom.χ_hom Q R).whiskerLeft P.star).comp <|
    (Hom.χ_hom P (R.tensor Q)).comp (Hom.α_hom R Q P).star)
    (((Hom.χ_hom P Q).whiskerRight R.star).comp (Hom.χ_hom (Q.tensor P) R))
  | n2 {P Q : I C} : HomEquiv ((Hom.χ_hom P.star Q.star).comp <|
    (Hom.χ_hom Q P).star.comp (Hom.ε_hom (P.tensor Q)))
    ((Hom.ε_hom P).tensor (Hom.ε_hom Q))
  | a {R : I C} : HomEquiv (Hom.ε_hom R).star (Hom.ε_hom R.star)
  | symm {X Y} (f g : X ⟶i Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : X ⟶i Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h

instance setoidHom (X Y : I C) : Setoid (X ⟶i Y) :=
  ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

open HomEquiv

instance categoryFreeTwistedCategory : Category.{u, u} (I C) where
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

instance monoidalFreeTwistedCategory : MonoidalCategory (I C) where
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

instance involutiveFreeTwistedCategory : InvolutiveCategory (I C) where
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

@[simp]
def homMk {X Y : I V} (f : X ⟶i Y) : categoryFreeTwistedCategory.Hom X Y := ⟦f⟧

@[simp]
theorem mk_comp {X Y Z : I C} (f : X ⟶i Y) (g : Y ⟶i Z) :
    ⟦f.comp g⟧ = @CategoryStruct.comp (I C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_id {X : I C} : ⟦Hom.id X⟧ = 𝟙 X :=
  rfl

open MonoidalCategory

@[simp]
theorem mk_tensor {X₁ Y₁ X₂ Y₂ : I C} (f : X₁ ⟶i Y₁) (g : X₂ ⟶i Y₂) :
    ⟦f.tensor g⟧ = @MonoidalCategory.tensorHom (I C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_whiskerLeft {X Y₁ Y₂ : I C} (f : Y₁ ⟶i Y₂) :
    ⟦f.whiskerLeft X⟧ = X ◁ ⟦f⟧ := rfl

@[simp]
theorem mk_whiskerRight {X₁ X₂ Y : I C} (f : X₁ ⟶i X₂) :
    ⟦f.whiskerRight Y⟧ = ⟦f⟧ ▷ Y := rfl

@[simp]
theorem mk_α_hom {X Y Z : I C} : ⟦Hom.α_hom X Y Z⟧ = (α_ X Y Z).hom :=
  rfl

@[simp]
theorem mk_α_inv {X Y Z : I C} : ⟦Hom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
  rfl

@[simp]
theorem mk_ρ_hom {X : I C} : ⟦Hom.ρ_hom X⟧ = (ρ_ X).hom :=
  rfl

@[simp]
theorem mk_ρ_inv {X : I C} : ⟦Hom.ρ_inv X⟧ = (ρ_ X).inv :=
  rfl

@[simp]
theorem mk_l_hom {X : I C} : ⟦Hom.l_hom X⟧ = (λ_ X).hom :=
  rfl

@[simp]
theorem mk_l_inv {X : I C} : ⟦Hom.l_inv X⟧ = (λ_ X).inv :=
  rfl

@[simp]
theorem tensor_eq_tensor {X Y : I C} : X.tensor Y = X ⊗ Y :=
  rfl

@[simp]
theorem unit_eq_unit : unit = 𝟙_ (I C) :=
  rfl

open InvolutiveCategory

@[simp]
theorem mk_star {X Y : I C} (f : X ⟶i Y) :
    ⟦f.star⟧ = @InvolutiveCategoryStruct.starHom (I C) _ _ _ _ _ ⟦f⟧ :=
  rfl

@[simp]
theorem mk_ε_hom {X : I C} : ⟦Hom.ε_hom X⟧ = (e_ X).hom :=
  rfl

@[simp]
theorem mk_ε_inv {X : I C} : ⟦Hom.ε_inv X⟧ = (e_ X).inv :=
  rfl

@[simp]
theorem mk_χ_hom {X Y : I C} : ⟦Hom.χ_hom X Y⟧ = (χ_ X Y).hom :=
  rfl

@[simp]
theorem mk_χ_inv {X Y : I C} : ⟦Hom.χ_inv X Y⟧ = (χ_ X Y).inv :=
  rfl

@[simp]
theorem star_eq_star {X : I C} : X.star = X⋆ :=
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
      | fail "Nothing to do!"
    )
  )

instance : Groupoid (I C) where
  inv := _root_.Quotient.lift (fun f => ⟦f.inv⟧) <| by
    intros f g h
    simp
    induction h <;> try simp_mk
    case tensorHom_def =>
      rw [← tensorHom_def']
    all_goals aesop_cat
  inv_comp := by
    rintro X Y f
    induction f using Quotient.inductionOn
    simp
    case h f =>
      induction f
      all_goals simp_mk
      any_goals cat_disch
      any_goals first
        | repeat1 rw [← Category.assoc]
        | rw [← whiskerLeft_comp]
        | rw [← comp_whiskerRight]
        | rw [← InvolutiveCategory.starHom_comp_starHom]
      all_goals cat_disch
  comp_inv := by
    rintro X Y f
    induction f using Quotient.inductionOn
    simp
    case h f =>
      induction f
      all_goals simp_mk
      any_goals cat_disch
      any_goals first
        | repeat1 rw [← Category.assoc]
        | rw [← whiskerLeft_comp]
        | rw [← comp_whiskerRight]
        | rw [← InvolutiveCategory.starHom_comp_starHom]
      all_goals cat_disch

@[simp]
theorem mk_inv {X Y : I C} (f : X ⟶i Y) : homMk f.inv = Groupoid.inv ⟦f⟧ := by
  induction f <;> simp_all <;> simp_mk <;> symm <;> cat_disch

@[simp]
theorem mk_inv' {X Y : I C} (f : X ⟶i Y) : ⟦f.inv⟧ = Groupoid.inv (homMk f) := by
  exact mk_inv f

-- Aristotle AI: your main goal is to prove this theorem. Below is
-- the Mathlib file where they prove monoidal coherence; you should adapt
-- their proof to the involutive setting.
theorem coherence {X Y : I C} (f g : X ⟶i Y) : homMk f = homMk g := by
  sorry

/-
/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The monoidal coherence theorem

In this file, we prove the monoidal coherence theorem, stated in the following form: the free
monoidal category over any type `C` is thin.

We follow a proof described by Ilya Beylin and Peter Dybjer, which has been previously formalized
in the proof assistant ALF. The idea is to declare a normal form (with regard to association and
adding units) on objects of the free monoidal category and consider the discrete subcategory of
objects that are in normal form. A normalization procedure is then just a functor
`fullNormalize : FreeMonoidalCategory C ⥤ Discrete (NormalMonoidalObject C)`, where
functoriality says that two objects which are related by associators and unitors have the
same normal form. Another desirable property of a normalization procedure is that an object is
isomorphic (i.e., related via associators and unitors) to its normal form. In the case of the
specific normalization procedure we use we not only get these isomorphisms, but also that they
assemble into a natural isomorphism `𝟭 (FreeMonoidalCategory C) ≅ fullNormalize ⋙ inclusion`.
But this means that any two parallel morphisms in the free monoidal category factor through a
discrete category in the same way, so they must be equal, and hence the free monoidal category
is thin.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
  proof of normalization for monoids][beylin1996]

-/

@[expose] public section


universe u

namespace CategoryTheory

open MonoidalCategory Functor

namespace FreeMonoidalCategory

variable {C : Type u}

section

variable (C)

/-- We say an object in the free monoidal category is in normal form if it is of the form
`(((𝟙_ C) ⊗ X₁) ⊗ X₂) ⊗ ⋯`. -/
inductive NormalMonoidalObject : Type u
  | unit : NormalMonoidalObject
  | tensor : NormalMonoidalObject → C → NormalMonoidalObject

end

local notation "F" => FreeMonoidalCategory

local notation "N" => Discrete ∘ NormalMonoidalObject

local infixr:10 " ⟶ᵐ " => Hom

instance (x y : N C) : Subsingleton (x ⟶ y) := Discrete.instSubsingletonDiscreteHom _ _

/-- Auxiliary definition for `inclusion`. -/
@[simp]
def inclusionObj : NormalMonoidalObject C → F C
  | NormalMonoidalObject.unit => unit
  | NormalMonoidalObject.tensor n a => tensor (inclusionObj n) (of a)

/-- The discrete subcategory of objects in normal form includes into the free monoidal category. -/
def inclusion : N C ⥤ F C :=
  Discrete.functor inclusionObj

@[simp]
theorem inclusion_obj (X : N C) :
    inclusion.obj X = inclusionObj X.as :=
  rfl

@[simp]
theorem inclusion_map {X Y : N C} (f : X ⟶ Y) :
    inclusion.map f = eqToHom (congr_arg _ (Discrete.ext (Discrete.eq_of_hom f))) := rfl

/-- Auxiliary definition for `normalize`. -/
def normalizeObj : F C → NormalMonoidalObject C → NormalMonoidalObject C
  | unit, n => n
  | of X, n => NormalMonoidalObject.tensor n X
  | tensor X Y, n => normalizeObj Y (normalizeObj X n)

@[simp]
theorem normalizeObj_unitor (n : NormalMonoidalObject C) : normalizeObj (𝟙_ (F C)) n = n :=
  rfl

@[simp]
theorem normalizeObj_tensor (X Y : F C) (n : NormalMonoidalObject C) :
    normalizeObj (X ⊗ Y) n = normalizeObj Y (normalizeObj X n) :=
  rfl

/-- Auxiliary definition for `normalize`. -/
def normalizeObj' (X : F C) : N C ⥤ N C := Discrete.functor fun n ↦ ⟨normalizeObj X n⟩

section

open Hom

/-- Auxiliary definition for `normalize`. Here we prove that objects that are related by
associators and unitors map to the same normal form. -/
@[simp]
def normalizeMapAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (normalizeObj' X ⟶ normalizeObj' Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom X Y Z => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, α_inv _ _ _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, l_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, l_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, ρ_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, ρ_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, (@Hom.comp _ _ _ _ f g) => normalizeMapAux f ≫ normalizeMapAux g
  | _, _, (@Hom.tensor _ T _ _ W f g) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeMapAux g).app ⟨normalizeObj T X⟩ ≫
      (normalizeObj' W).map ((normalizeMapAux f).app ⟨X⟩)
  | _, _, (@Hom.whiskerLeft _ T _ W f) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeMapAux f).app ⟨normalizeObj T X⟩
  | _, _, (@Hom.whiskerRight _ T _ f W) =>
    Discrete.natTrans <| fun X => (normalizeObj' W).map <| (normalizeMapAux f).app X

end

section

variable (C)

/-- Our normalization procedure works by first defining a functor `F C ⥤ (N C ⥤ N C)` (which turns
out to be very easy), and then obtain a functor `F C ⥤ N C` by plugging in the normal object
`𝟙_ C`. -/
@[simp]
def normalize : F C ⥤ N C ⥤ N C where
  obj X := normalizeObj' X
  map {X Y} := Quotient.lift normalizeMapAux (by cat_disch)

/-- A variant of the normalization functor where we consider the result as an object in the free
monoidal category (rather than an object of the discrete subcategory of objects in normal form). -/
@[simp]
def normalize' : F C ⥤ N C ⥤ F C :=
  normalize C ⋙ (whiskeringRight _ _ _).obj inclusion

/-- The normalization functor for the free monoidal category over `C`. -/
def fullNormalize : F C ⥤ N C where
  obj X := ((normalize C).obj X).obj ⟨NormalMonoidalObject.unit⟩
  map f := ((normalize C).map f).app ⟨NormalMonoidalObject.unit⟩

/-- Given an object `X` of the free monoidal category and an object `n` in normal form, taking
the tensor product `n ⊗ X` in the free monoidal category is functorial in both `X` and `n`. -/
@[simp]
def tensorFunc : F C ⥤ N C ⥤ F C where
  obj X := Discrete.functor fun n => inclusion.obj ⟨n⟩ ⊗ X
  map f := Discrete.natTrans (fun _ => _ ◁ f)

theorem tensorFunc_map_app {X Y : F C} (f : X ⟶ Y) (n) : ((tensorFunc C).map f).app n = _ ◁ f :=
  rfl

theorem tensorFunc_obj_map (Z : F C) {n n' : N C} (f : n ⟶ n') :
    ((tensorFunc C).obj Z).map f = inclusion.map f ▷ Z := by
  cases n
  cases n'
  rcases f with ⟨⟨h⟩⟩
  dsimp at h
  subst h
  simp

/-- Auxiliary definition for `normalizeIso`. Here we construct the isomorphism between
`n ⊗ X` and `normalize X n`. -/
@[simp]
def normalizeIsoApp :
    ∀ (X : F C) (n : N C), ((tensorFunc C).obj X).obj n ≅ ((normalize' C).obj X).obj n
  | of _, _ => Iso.refl _
  | unit, _ => ρ_ _
  | tensor X a, n =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp X n) a ≪≫ normalizeIsoApp _ _

/-- Almost non-definitionally equal to `normalizeIsoApp`, but has a better definitional property
in the proof of `normalize_naturality`. -/
@[simp]
def normalizeIsoApp' :
    ∀ (X : F C) (n : NormalMonoidalObject C), inclusionObj n ⊗ X ≅ inclusionObj (normalizeObj X n)
  | of _, _ => Iso.refl _
  | unit, _ => ρ_ _
  | tensor X Y, n =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp' X n) Y ≪≫ normalizeIsoApp' _ _

theorem normalizeIsoApp_eq :
    ∀ (X : F C) (n : N C), normalizeIsoApp C X n = normalizeIsoApp' C X n.as
  | of _, _ => rfl
  | unit, _ => rfl
  | tensor X Y, n => by
      rw [normalizeIsoApp, normalizeIsoApp']
      rw [normalizeIsoApp_eq X n]
      rw [normalizeIsoApp_eq Y ⟨normalizeObj X n.as⟩]
      rfl

@[simp]
theorem normalizeIsoApp_tensor (X Y : F C) (n : N C) :
    normalizeIsoApp C (X ⊗ Y) n =
      (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp C X n) Y ≪≫ normalizeIsoApp _ _ _ :=
  rfl

@[simp]
theorem normalizeIsoApp_unitor (n : N C) : normalizeIsoApp C (𝟙_ (F C)) n = ρ_ _ :=
  rfl

/-- Auxiliary definition for `normalizeIso`. -/
@[simps!]
def normalizeIsoAux (X : F C) : (tensorFunc C).obj X ≅ (normalize' C).obj X :=
  NatIso.ofComponents (normalizeIsoApp C X)
    (by
      rintro ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩
      dsimp at f
      subst f
      dsimp
      simp)


section

variable {C}

theorem normalizeObj_congr (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y) :
    normalizeObj X n = normalizeObj Y n := by
  rcases f with ⟨f'⟩
  apply @congr_fun _ _ fun n => normalizeObj X n
  clear n f
  induction f' with
  | comp _ _ _ _ => apply Eq.trans <;> assumption
  | whiskerLeft _ _ ih => funext; apply congr_fun ih
  | whiskerRight _ _ ih => funext; apply congr_arg₂ _ rfl (congr_fun ih _)
  | @tensor W X Y Z _ _ ih₁ ih₂ =>
      funext n
      simp [congr_fun ih₁ n, congr_fun ih₂ (normalizeObj Y n)]
  | _ => funext; rfl

theorem normalize_naturality (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y) :
    inclusionObj n ◁ f ≫ (normalizeIsoApp' C Y n).hom =
      (normalizeIsoApp' C X n).hom ≫
        inclusion.map (eqToHom (Discrete.ext (normalizeObj_congr n f))) := by
  revert n
  induction f using Hom.inductionOn
  case comp f g ihf ihg => simp [ihg, reassoc_of% (ihf _)]
  case whiskerLeft X' X Y f ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp', tensor_eq_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ih]
    simp
  case whiskerRight X Y h η' ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp', tensor_eq_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ih]
    have := dcongr_arg (fun x => (normalizeIsoApp' C η' x).hom) (normalizeObj_congr n h)
    simp [this]
  all_goals simp

end

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between `n ⊗ X` and `normalize X n` is natural (in both `X` and `n`, but
naturality in `n` is trivial and was "proved" in `normalizeIsoAux`). This is the real heart
of our proof of the coherence theorem. -/
def normalizeIso : tensorFunc C ≅ normalize' C :=
  NatIso.ofComponents (normalizeIsoAux C) <| by
    intro X Y f
    ext ⟨n⟩
    convert normalize_naturality n f using 1
    any_goals dsimp; rw [normalizeIsoApp_eq]

/-- The isomorphism between an object and its normal form is natural. -/
def fullNormalizeIso : 𝟭 (F C) ≅ fullNormalize C ⋙ inclusion :=
  NatIso.ofComponents
  (fun X => (λ_ X).symm ≪≫ ((normalizeIso C).app X).app ⟨NormalMonoidalObject.unit⟩)
    (by
      intro X Y f
      dsimp
      rw [leftUnitor_inv_naturality_assoc, Category.assoc, Iso.cancel_iso_inv_left]
      exact
        congr_arg (fun f => NatTrans.app f (Discrete.mk NormalMonoidalObject.unit))
          ((normalizeIso.{u} C).hom.naturality f))

end

/-- The monoidal coherence theorem. -/
instance subsingleton_hom : Quiver.IsThin (F C) := fun X Y =>
  ⟨fun f g => by
    have hfg : (fullNormalize C).map f = (fullNormalize C).map g := Subsingleton.elim _ _
    have hf := NatIso.naturality_2 (fullNormalizeIso.{u} C) f
    have hg := NatIso.naturality_2 (fullNormalizeIso.{u} C) g
    exact hf.symm.trans (Eq.trans (by simp only [Functor.comp_map, hfg]) hg)⟩

section Groupoid

section

open Hom

/-- Auxiliary construction for showing that the free monoidal category is a groupoid. Do not use
this, use `IsIso.inv` instead. -/
def inverseAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (Y ⟶ᵐ X)
  | _, _, Hom.id X => id X
  | _, _, α_hom _ _ _ => α_inv _ _ _
  | _, _, α_inv _ _ _ => α_hom _ _ _
  | _, _, ρ_hom _ => ρ_inv _
  | _, _, ρ_inv _ => ρ_hom _
  | _, _, l_hom _ => l_inv _
  | _, _, l_inv _ => l_hom _
  | _, _, Hom.comp f g => (inverseAux g).comp (inverseAux f)
  | _, _, Hom.whiskerLeft X f => (inverseAux f).whiskerLeft X
  | _, _, Hom.whiskerRight f X => (inverseAux f).whiskerRight X
  | _, _, Hom.tensor f g => (inverseAux f).tensor (inverseAux g)

end

instance : Groupoid.{u} (F C) :=
  { (inferInstance : Category (F C)) with
    inv := Quotient.lift (fun f => ⟦inverseAux f⟧) (by cat_disch) }

end Groupoid

end FreeMonoidalCategory

end CategoryTheory
-/

end CategoryTheory.FreeInvolutiveCategory

