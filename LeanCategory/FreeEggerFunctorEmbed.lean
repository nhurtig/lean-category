import LeanCategory.FreeEgger
import LeanCategory.FreeEggerQuiver
/- import LeanCategory.FreeEggerFunctorQuiver -/

namespace CategoryTheory.FreeTwistedCategory.Embed


variable {C : Type u} [userQuiver : Quiver.{v} (FQ C)]

open MonoidalCategory
open InvolutiveCategory
open TwistedCategory
open CategoryTheory.FreeTwistedCategory

#synth (Category (F C))

#check (@FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver C _).Hom
set_option quotPrecheck false in
infixr:10 " ⟶Q " => (@FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver C _).Hom

#check (@FreeTwistedCategory.categoryFreeTwistedCategory C).Hom
set_option quotPrecheck false in
infixr:10 " ⟶β " => (@FreeTwistedCategory.categoryFreeTwistedCategory C).Hom

#synth (Quiver (F C))

/- def projectObj : F C → D -/
/-   | .of X => m X -/
/-   | .unit => 𝟙_ D -/
/-   | .tensor X Y => X.projectObj ⊗ Y.projectObj -/
/-   | .star X => X.projectObj⋆ -/

@[simp]
def FtoFQ : F V → FQ V
  | .of v => .of v
  | .unit => .unit
  | .tensor X Y => .tensor (FtoFQ X) (FtoFQ Y)
  | .star X => .star (FtoFQ X)

@[simp]
def FQtoF' : FQ V → F V
  | .of v => .of v
  | .unit => .unit
  | .tensor X Y => .tensor (FQtoF' X) (FQtoF' Y)
  | .star X => .star (FQtoF' X)

/- def FtoFQ : F V ≃ FQ V where -/
/-   toFun := FtoFQ' -/
/-   invFun := FQtoF' -/
/-   left_inv X := by induction X <;> simp_all -/
/-   right_inv X := by induction X <;> simp_all -/

/- @[simp] -/
/- lemma FtoFQ'_eq_FtoFQ : FtoFQ' X = FtoFQ X := by -/
/-   rfl -/

@[simp]
lemma FtoFQ_of : FtoFQ (.of v) = .of v := by
  rfl

@[simp]
lemma FtoFQ_unit : FtoFQ (𝟙_ (F C)) = 𝟙_ _ := by
  rfl

@[simp]
lemma FtoFQ_tensor {X Y : F C} : FtoFQ (X ⊗ Y) = FtoFQ X ⊗ FtoFQ Y := by
  rfl

@[simp]
lemma FtoFQ_star {X : F C} : FtoFQ X⋆ = (FtoFQ X)⋆ := by
  rfl

open Hom

@[simp]
def embedMapAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → ((FtoFQ X) ⟶Q (FtoFQ Y))
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, l_hom _ => (λ_ _).hom
  | _, _, l_inv _ => (λ_ _).inv
  | _, _, ρ_hom _ => (ρ_ _).hom
  | _, _, ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.comp f g => embedMapAux f ≫ embedMapAux g
  | _, _, Hom.whiskerLeft X p => (FtoFQ X) ◁ embedMapAux p
  | _, _, Hom.whiskerRight p X => embedMapAux p ▷ (FtoFQ X)
  | _, _, Hom.tensor f g => embedMapAux f ⊗ₘ embedMapAux g
  | _, _, Hom.star f => InvolutiveCategoryStruct.starHom (embedMapAux f)
  | _, _, χ_hom _ _ => (χ_ _ _).hom
  | _, _, χ_inv _ _ => (χ_ _ _).inv
  | _, _, ε_hom _ => (e_ _).hom
  | _, _, ε_inv _ => (e_ _).inv
  | _, _, twist_hom _ => (ς_ _).hom
  | _, _, twist_inv _ => (ς_ _).inv

/- /- open MonoidalCategory -/ -/
/- #synth MonoidalCategoryStruct (F C) -/
/- /- attribute [-instance] FreeTwistedCategoryQuiver.categoryFreeTwistedCategoryQuiver -/ -/
/- attribute [-instance] FreeTwistedCategory.categoryFreeTwistedCategory -/
/- attribute [-instance] monoidalFreeTwistedCategory -/
/- #synth MonoidalCategoryStruct (F C) -/
/- #synth MonoidalCategory (F C) -/
/- open CategoryTheory.FreeTwistedCategoryQuiver -/
/- instance : MonoidalCategory (F C) := FreeTwistedCategoryQuiver.monoidalFreeTwistedCategoryQuiver -/
/- #synth MonoidalCategory (F C) -/
/- attribute [-instance] FreeTwistedCategory.categoryFreeTwistedCategory -/
/- attribute [-instance] FreeTwistedCategory.monoidalFreeTwistedCategory -/

@[simp]
def embedMap (X Y : F C) : (X ⟶β Y) → ((FtoFQ X) ⟶Q (FtoFQ Y)) :=
  _root_.Quotient.lift embedMapAux <| by
    intro f g h
    induction h with
    | refl => rfl
    | symm _ _ _ hfg' => exact hfg'.symm
    | trans _ _ hfg hgh => exact hfg.trans hgh
    | comp _ _ hf hg => dsimp only [embedMapAux]; rw [hf, hg]
    | whiskerLeft _ _ _ _ hf => dsimp only [embedMapAux]; rw [hf]
    | whiskerRight _ _ _ _ hf => dsimp only [embedMapAux]; rw [hf]
    | tensor _ _ hfg hfg' => dsimp only [embedMapAux]; rw [hfg, hfg']
    | tensorHom_def f g => dsimp only [embedMapAux]; rw [MonoidalCategory.tensorHom_def]
    | comp_id => dsimp only [embedMapAux]; rw [Category.comp_id]
    | id_comp => dsimp only [embedMapAux]; rw [Category.id_comp]
    | assoc => dsimp only [embedMapAux]; rw [Category.assoc]
    | id_tensorHom_id =>
        dsimp only [embedMapAux]
        simp
    | tensorHom_comp_tensorHom =>
        dsimp only [embedMapAux]; rw [MonoidalCategory.tensorHom_comp_tensorHom]
    | whiskerLeft_id X Y =>
        dsimp only [embedMapAux]
        rw [MonoidalCategory.whiskerLeft_id _ (FtoFQ Y)]
        rfl
    | id_whiskerRight =>
        dsimp only [embedMapAux]
        rw [MonoidalCategory.id_whiskerRight]
        rfl
    | α_hom_inv => dsimp only [embedMapAux]; rw [Iso.hom_inv_id]
    | α_inv_hom => dsimp only [embedMapAux]; rw [Iso.inv_hom_id]
    | associator_naturality =>
        dsimp only [embedMapAux]; rw [MonoidalCategory.associator_naturality]
    | ρ_hom_inv =>
        dsimp only [embedMapAux]
        simp
    | ρ_inv_hom => dsimp only [embedMapAux]; rw [Iso.inv_hom_id]
    | ρ_naturality =>
        dsimp only [embedMapAux]
        simp
    | l_hom_inv => dsimp only [embedMapAux]; rw [Iso.hom_inv_id]
    | l_inv_hom => dsimp only [embedMapAux]; rw [Iso.inv_hom_id]
    | l_naturality =>
        dsimp only [embedMapAux]
        simp
    | pentagon =>
        dsimp only [embedMapAux]
        simp
    | triangle =>
        dsimp only [embedMapAux]
        simp
    -- START NAT'S STUFF
    | star _ hf => dsimp only [embedMapAux]; rw [hf]
    | starHom_comp_starHom _ hf =>
      dsimp only [embedMapAux]; rw [InvolutiveCategory.starHom_comp_starHom]
    | starHom_id =>
        dsimp only [embedMapAux]
        simp
    | ε_hom_inv => dsimp only [embedMapAux]; rw [Iso.hom_inv_id]
    | ε_inv_hom => dsimp only [embedMapAux]; rw [Iso.inv_hom_id]
    | ε_naturality =>
        dsimp only [embedMapAux]
        exact InvolutiveCategory.involutor_naturality _
    | χ_hom_inv => dsimp only [embedMapAux]; rw [Iso.hom_inv_id]
    | χ_inv_hom => dsimp only [embedMapAux]; rw [Iso.inv_hom_id]
    | χ_naturality =>
        dsimp only [embedMapAux]
        exact InvolutiveCategory.skewator_naturality _ _
    | f3 =>
        dsimp only [embedMapAux]
        exact f3 _ _ _
    | n2 =>
        dsimp only [embedMapAux]
        exact n2 _ _
    | a =>
        dsimp only [embedMapAux]
        exact a _
    | twist_hom_inv => dsimp only [embedMapAux]; rw [Iso.hom_inv_id]
    | twist_inv_hom => dsimp only [embedMapAux]; rw [Iso.inv_hom_id]
    | twist_naturality =>
        dsimp only [embedMapAux]
        exact TwistedCategory.twist_naturality _
    | tℓ =>
        dsimp only [embedMapAux]
        exact TwistedCategory.tℓ _ _ _

#synth Category.{u, u} (F C)

#synth Category (F C)
/- #check @Functor (F C) categoryFreeTwistedCategory (F C) categoryFreeTwistedCategoryQuiver -/

#synth Quiver (F C)

/- attribute [-instance] categoryFreeTwistedCategory -/
/- attribute [-instance] categoryFreeTwistedCategoryQuiver -/
/- attribute [-instance] instGroupoid -/

def justBraids := (@categoryFreeTwistedCategory C)
#check @justBraids C

/- #synth Category (F C) -/

/- attribute [instance] categoryFreeTwistedCategory -/
/- def myFunct := Functor (F C) -/
/- attribute [-instance] categoryFreeTwistedCategory -/
/- attribute [instance] categoryFreeTwistedCategoryQuiver -/
/- #check myFunct -/
/- def myFunct' := myFunct (C := C) (F C) -/
/- attribute [-instance] categoryFreeTwistedCategoryQuiver -/
/- #check myFunct' -/

/- attribute [instance] categoryFreeTwistedCategoryQuiver -/
attribute [instance] categoryFreeTwistedCategory
#synth Category (F C)

#check embedMap

def embed : Functor (F C) (FQ C) where
  obj := FtoFQ
  map {X Y} f := embedMap X Y f
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

@[simp]
lemma embed_map_whiskerLeft {X : F C} : embed.map (X ◁ f) = FtoFQ X ◁ embed.map f := by
  unfold embed
  simp
  induction f using Quotient.inductionOn
  rfl

@[simp]
lemma embed_map_whiskerRight {X : F C} : embed.map (f ▷ X) = embed.map f ▷ FtoFQ X := by
  unfold embed
  simp
  induction f using Quotient.inductionOn
  rfl

@[simp]
lemma embed_map_twist_hom {X : F C} : embed.map (ς_ X |>.hom) = (ς_ (FtoFQ X)).hom := by
  rfl
@[simp]
lemma embed_map_twist_inv {X : F C} : embed.map (ς_ X |>.inv) = (ς_ (FtoFQ X)).inv := by
  rfl
@[simp]
lemma embed_map_braid_hom {X Y : F C} :
    embed.map (σ_ X Y |>.hom) = (σ_ (FtoFQ X) (FtoFQ Y)).hom := by
  rfl
@[simp]
lemma embed_map_braid_inv {X Y : F C} :
    embed.map (σ_ X Y |>.inv) = (σ_ (FtoFQ X) (FtoFQ Y)).inv := by
  rfl
@[simp]
lemma embed_map_associator_hom {X Y Z : F C} :
    embed.map (α_ X Y Z |>.hom) = (α_ (FtoFQ X) (FtoFQ Y) (FtoFQ Z)).hom := by
  rfl
@[simp]
lemma embed_map_associator_inv {X Y Z : F C} :
    embed.map (α_ X Y Z |>.inv) = (α_ (FtoFQ X) (FtoFQ Y) (FtoFQ Z)).inv := by
  rfl

/- variable (M : {X Y : F C} → (X ⟶ Y) → -/
/-   ((X.projectObj (FreeTwistedCategory.of <| m ·)) ⟶ (Y.projectObj (.of <| m ·)))) -/
/- def projectFree : F C ⥤ F D := embed (.of <| m ·) (⟦Hom.of <| M ·⟧) -/
/- attribute [instance] FreeTwistedCategory.categoryFreeTwistedCategory -/

end CategoryTheory.FreeTwistedCategory.Embed

