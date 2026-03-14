import Mathlib
import LeanCategory.EggerIncoherent
import LeanCategory.FreeTwistedCategoryBase

namespace CategoryTheory.FreeTwistedCategory

variable {C : Type u}

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
  | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
  | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : T C} (f₁ : X₁ ⟶t Y₁) (f₂ : X₂ ⟶t Y₂)
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
      HomEquiv ((Hom.α_hom X unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
        ((Hom.ρ_hom X).whiskerRight Y)
  -- START OF NAT'S STUFF
  | star {X Y} {f f' : X ⟶t Y} : HomEquiv f f' → HomEquiv f.star f'.star
  | starHom_id {X} : HomEquiv (Hom.id X).star (Hom.id X.star)
  | starHom_comp_starHom {X Y Z : T C} (f : X ⟶t Y) (g : Y ⟶t Z) :
    HomEquiv (f.comp g).star (f.star.comp g.star)
  | χ_hom_inv {X Y} : HomEquiv ((Hom.χ_hom X Y).comp (Hom.χ_inv X Y)) (Hom.id _)
  | χ_inv_hom {X Y} : HomEquiv ((Hom.χ_inv X Y).comp (Hom.χ_hom X Y)) (Hom.id _)
  | χ_naturality {X₁ X₂ Y₁ Y₂} (f : X₁ ⟶t Y₁) (g : X₂ ⟶t Y₂) :
    HomEquiv ((f.star.tensor g.star).comp (Hom.χ_hom Y₁ Y₂))
      ((Hom.χ_hom X₁ X₂).comp (g.tensor f).star)
  | ε_hom_inv {X} : HomEquiv ((Hom.ε_hom X).comp (Hom.ε_inv X)) (Hom.id _)
  | ε_inv_hom {X} : HomEquiv ((Hom.ε_inv X).comp (Hom.ε_hom X)) (Hom.id _)
  | ε_naturality {X Y : T C} (f : X ⟶t Y) :
    HomEquiv (f.star.star.comp (Hom.ε_hom Y)) ((Hom.ε_hom X).comp f)
  | f3 {P Q R : T C} : HomEquiv ((Hom.α_hom P.star Q.star R.star).comp <|
    ((Hom.χ_hom Q R).whiskerLeft P.star).comp <|
    (Hom.χ_hom P (R.tensor Q)).comp (Hom.α_hom R Q P).star)
    (((Hom.χ_hom P Q).whiskerRight R.star).comp (Hom.χ_hom (Q.tensor P) R))
  | n2 {P Q : T C} : HomEquiv ((Hom.χ_hom P.star Q.star).comp <|
    (Hom.χ_hom Q P).star.comp (Hom.ε_hom (P.tensor Q)))
    ((Hom.ε_hom P).tensor (Hom.ε_hom Q))
  | a {R : T C} : HomEquiv (Hom.ε_hom R).star (Hom.ε_hom R.star)
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
  | symm {X Y} (f g : X ⟶t Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : X ⟶t Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h

instance setoidHom (X Y : T C) : Setoid (X ⟶t Y) :=
  ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

open HomEquiv

instance categoryFreeTwistedCategory : Category.{u, u} (T C) where
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

instance monoidalFreeTwistedCategory : MonoidalCategory (T C) where
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

instance involutiveFreeTwistedCategory : InvolutiveCategory (T C) where
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

instance freeTwistedCategory : TwistedCategory (T C) where
  twist X := ⟨⟦Hom.twist_hom X⟧, ⟦Hom.twist_inv X⟧,
    _root_.Quotient.sound twist_hom_inv, _root_.Quotient.sound twist_inv_hom⟩
  twist_naturality {X Y} := by
    rintro ⟨f⟩
    exact _root_.Quotient.sound (HomEquiv.twist_naturality _)
  tℓ _ _ _ := _root_.Quotient.sound tℓ

@[simp]
def homMk {X Y : T V} (f : X ⟶t Y) : categoryFreeTwistedCategory.Hom X Y := ⟦f⟧

@[simp]
theorem mk_comp {X Y Z : T C} (f : X ⟶t Y) (g : Y ⟶t Z) :
    ⟦f.comp g⟧ = @CategoryStruct.comp (T C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_id {X : T C} : ⟦Hom.id X⟧ = 𝟙 X :=
  rfl

open MonoidalCategory

@[simp]
theorem mk_tensor {X₁ Y₁ X₂ Y₂ : T C} (f : X₁ ⟶t Y₁) (g : X₂ ⟶t Y₂) :
    ⟦f.tensor g⟧ = @MonoidalCategory.tensorHom (T C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_whiskerLeft {X Y₁ Y₂ : T C} (f : Y₁ ⟶t Y₂) :
    ⟦f.whiskerLeft X⟧ = X ◁ ⟦f⟧ := rfl

@[simp]
theorem mk_whiskerRight {X₁ X₂ Y : T C} (f : X₁ ⟶t X₂) :
    ⟦f.whiskerRight Y⟧ = ⟦f⟧ ▷ Y := rfl

@[simp]
theorem mk_α_hom {X Y Z : T C} : ⟦Hom.α_hom X Y Z⟧ = (α_ X Y Z).hom :=
  rfl

@[simp]
theorem mk_α_inv {X Y Z : T C} : ⟦Hom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
  rfl

@[simp]
theorem mk_ρ_hom {X : T C} : ⟦Hom.ρ_hom X⟧ = (ρ_ X).hom :=
  rfl

@[simp]
theorem mk_ρ_inv {X : T C} : ⟦Hom.ρ_inv X⟧ = (ρ_ X).inv :=
  rfl

@[simp]
theorem mk_l_hom {X : T C} : ⟦Hom.l_hom X⟧ = (λ_ X).hom :=
  rfl

@[simp]
theorem mk_l_inv {X : T C} : ⟦Hom.l_inv X⟧ = (λ_ X).inv :=
  rfl

@[simp]
theorem tensor_eq_tensor {X Y : T C} : X.tensor Y = X ⊗ Y :=
  rfl

@[simp]
theorem unit_eq_unit : FreeTwistedCategory.unit = 𝟙_ (T C) :=
  rfl

open InvolutiveCategory

@[simp]
theorem mk_star {X Y : T C} (f : X ⟶t Y) :
    ⟦f.star⟧ = @InvolutiveCategoryStruct.starHom (T C) _ _ _ _ _ ⟦f⟧ :=
  rfl

@[simp]
theorem mk_ε_hom {X : T C} : ⟦Hom.ε_hom X⟧ = (e_ X).hom :=
  rfl

@[simp]
theorem mk_ε_inv {X : T C} : ⟦Hom.ε_inv X⟧ = (e_ X).inv :=
  rfl

@[simp]
theorem mk_χ_hom {X Y : T C} : ⟦Hom.χ_hom X Y⟧ = (χ_ X Y).hom :=
  rfl

@[simp]
theorem mk_χ_inv {X Y : T C} : ⟦Hom.χ_inv X Y⟧ = (χ_ X Y).inv :=
  rfl

@[simp]
theorem star_eq_star {X : T C} : X.star = X⋆ :=
  rfl

open TwistedCategory

@[simp]
theorem mk_ς_hom {X : T C} : ⟦Hom.twist_hom X⟧ = (ς_ X).hom :=
  rfl

@[simp]
theorem mk_ς_hom' {X : T C} : ⟦Hom.twist_hom X⟧ = (TwistedCategoryStruct.twist X).hom :=
  rfl

@[simp]
theorem mk_ς_inv {X : T C} : ⟦Hom.twist_inv X⟧ = (ς_ X).inv :=
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

instance : Groupoid (T C) where
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
theorem mk_inv {X Y : T C} (f : X ⟶t Y) : homMk f.inv = Groupoid.inv ⟦f⟧ := by
  induction f <;> simp_all <;> simp_mk <;> symm <;> cat_disch

@[simp]
theorem mk_inv' {X Y : T C} (f : X ⟶t Y) : ⟦f.inv⟧ = Groupoid.inv (homMk f) := by
  exact mk_inv f

end CategoryTheory.FreeTwistedCategory

