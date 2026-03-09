import LeanCategory.FreeEgger

namespace CategoryTheory.FreeTwistedCategory

open MonoidalCategory
open InvolutiveCategory

def map (f : C → D) : F C → F D
  | .of c => .of <| f c
  | .unit => 𝟙_ _ -- was .unit
  | .tensor X Y => (X.map f) ⊗ (Y.map f) -- was .tensor
  | .star X => (X.map f)⋆ -- was .star

def flatten : F (F C) → F C
  | .of X => X
  | .unit => 𝟙_ _
  | .tensor X Y => X.flatten ⊗ Y.flatten
  | .star X => X.flatten⋆

@[simp]
def length : F C → ℕ
  | .of _ => 1
  | .unit => 0
  | .tensor X Y => X.length + Y.length
  | .star X => X.length

@[simp]
def toFin (X : F C) : F (Fin X.length) := match X with
  | .of _ => .of <| Fin.mk 0 (by simp)
  | .unit => 𝟙_ _
  | .tensor X Y =>
      let X' := X.toFin |>.map (Fin.mk ·.1 (by simp; omega))
      let Y' := Y.toFin |>.map (fun i ↦ Fin.mk (X.length + i.1) (by simp))
      X' ⊗ Y'
  | .star X =>
      let X' := X.toFin |>.map (fun i ↦ Fin.mk (X.length - i.1 - 1) (by simp; omega))
      X'⋆

@[simp] lemma map_of (f : C → D) (c : C) : map f (.of c) = .of (f c) := rfl
@[simp] lemma map_unit (f : C → D) : map f (𝟙_ _) = 𝟙_ _ := rfl
@[simp] lemma map_tensor (f : C → D) (X Y : F C) :
    map f (X ⊗ Y) = (map f X) ⊗ (map f Y) := rfl
@[simp] lemma map_star (f : C → D) (X : F C) : map f X⋆ = (map f X)⋆ := rfl

@[simp] lemma map_map (f : C → D) (g : D → E) (X : F C) : (X.map f).map g = X.map (g ∘ f) := by
  induction X <;> simp_all

@[simp] lemma flatten_of (X : F C) : flatten (.of X) = X := rfl
@[simp] lemma flatten_unit : @flatten C (𝟙_ _) = 𝟙_ _ := rfl
@[simp] lemma flatten_tensor (X Y : F (F C)) :
    flatten (X ⊗ Y) = (flatten X) ⊗ (flatten Y) := rfl
@[simp] lemma flatten_star (X : F (F C)) : flatten X⋆ = (flatten X)⋆ := rfl

@[simp] lemma length_of (c : C) : length (.of c) = 1 := rfl
@[simp] lemma length_unit : @length C (𝟙_ _) = 0 := rfl
@[simp] lemma length_tensor (X Y : F C) : length (X ⊗ Y) = length X + length Y := rfl
@[simp] lemma length_star (X : F C) : length X⋆ = length X := rfl

@[simp] lemma map_of_flatten (f : C → D) (X : F C) :
    (X.map (fun x ↦ .of (f x))).flatten = X.map f := by
  induction X <;> simp_all

@[simp]
def getElem (X : F C) (i : Fin X.length) : C := match X with
  | .of c => c
  | .unit => by
      have hi := i.prop
      contradiction
  | .tensor X Y =>  if hi : i < X.length then
      X.getElem ⟨i, hi⟩
    else
      Y.getElem ⟨i - X.length, by simp at hi; omega⟩
  | .star X => X.getElem ⟨X.length - i - 1, by
      have : X.length > 0 := by
        simp at i
        have hi := i.prop
        omega
      omega⟩


@[simp] lemma getElem_of (c : C) : (FreeTwistedCategory.of c).getElem ⟨0, by simp⟩ = c := rfl
/- @[simp] lemma getElem_star_star (X : F C) (i : ℕ) (h : i < X.length) : (X.star.star)[i]'h = X[i]'h := rfl -/

@[simp] lemma getElem_star_star (X : F C) (i : Fin X.length) : X⋆⋆.getElem i = X.getElem i := by
  simp
  apply congrArg
  ext
  simp
  omega

@[simp] lemma getElem_star_tensor (X Y : F C) (i : Fin (X.length + Y.length)) :
    (X ⊗ Y)⋆.getElem i = (Y⋆ ⊗ X⋆).getElem ⟨i, by simp; omega⟩ := by
  simp ; split <;> split
  any_goals omega -- impossible goals
  any_goals apply congrArg (X.getElem ·)
  any_goals apply congrArg (Y.getElem ·)
  all_goals simp ; omega

/- instance : GetElem (F V) (Fin n) V (fun X _ ↦ X.length = n) where -/
/-   getElem X i h := X.getElem (h ▸ i) -/

/-
@[simp]
def getElem? (i : ℕ) (fromLeft : Bool) : F C → Option C
  | .of c => if i = 0 then .some c else .none
  | .unit => .none
  | .tensor X Y => if fromLeft then
      if i < X.length then
        X.getElem? i fromLeft
      else
        Y.getElem? (i - X.length) fromLeft
    else
      if i < Y.length then
        Y.getElem? i fromLeft
      else
        X.getElem? (i - Y.length) fromLeft
  | .star X => X.getElem? i !fromLeft

lemma getElem_valid {i : ℕ} {fromLeft : Bool} {X : F C} (h : i < X.length) :
    (X.getElem? i fromLeft).isSome := by
  induction X generalizing i fromLeft <;> unfold getElem?
  case of => simp_all
  case unit => simp_all
  case star ih =>
    apply ih
    simp_all
  case tensor ih₁ ih₂ =>
    split <;> split
    · apply ih₁
      simp_all
    · apply ih₂
      simp_all
      omega
    · apply ih₂
      simp_all
    · apply ih₁
      simp_all
      omega

instance : GetElem (F V) ℕ V (fun X i => i < X.length) where
  getElem X i h := by
    cases hv : X.getElem? i true
    case some v => exact v
    case none =>
      rw [Option.isSome_iff_exists.mp (getElem_valid h) |>.choose_spec] at hv
      simp at hv
  -/
  /- getElem? X i := X.getElem? i true -/

/- @[simp] lemma getElem?_of (c : C) : (FreeTwistedCategory.of c)[0]? = c := rfl -/
/- @[simp] lemma getElem?_unit (i : ℕ) : (@FreeTwistedCategory.unit C)[i]? = .none := rfl -/
/- @[simp] lemma getElem?_star_star (X : F C) (i : ℕ) : (X.star.star)[i]? = X[i]? := rfl -/

  /- simp <;> split <;> split <;> simp_all -/
/- @[simp] lemma getElem_star_tensor (X Y : F C) (i : Fin (X.length + Y.length)) : ((X.tensor Y).star)[i] = (X.star.tensor Y.star)[i] := by -/
/-   simp -/
/-   sorry -/


/-
@[simp] lemma getElem_star (X : F V) (i : Fin X.length) : (X.star).getElem i b = X.getElem (X.length - i - 1) i := by
  induction X
  case unit =>
    simp at i ⊢
    simp [GetElem.getElem]
  case of =>
    simp at i ⊢
    simp [GetElem.getElem]
  case star X ih =>
    simp at i ⊢
    have hnempty : X.length ≠ 0 := by
      intros hi
      rw [hi] at i
      have hi := i.prop
      contradiction
    specialize ih <| Fin.mk (X.length - i - 1) (by omega)
    simp at ih
    rw [ih]
    simp_all
    apply getElem_index
    omega
  case tensor X Y ih₁ ih₂ =>
    simp
    rw [getElem_tensor X Y]
    sorry
  sorry

@[simp] lemma getElem_tensor (X Y : F V) {i : ℕ} (hi : i < X.length + Y.length) : (X.tensor Y)[i] =
    if hi : i < X.length then
      X[i]
    else
      Y[i - X.length] := sorry
end
-/


variable {D : Type u'}
  [Category.{v'} D] [MonoidalCategory D] [InvolutiveCategory D] (m : C → D)

open MonoidalCategory
open InvolutiveCategory
open TwistedCategory

def projectObj : F C → D
  | .of X => m X
  | .unit => 𝟙_ D
  | .tensor X Y => X.projectObj ⊗ Y.projectObj
  | .star X => X.projectObj⋆

@[simp]
lemma projectObj_of (X : C) : projectObj m (.of X) = m X := rfl

@[simp]
lemma projectObj_unit : projectObj m (𝟙_ _) = 𝟙_ D := rfl

@[simp]
lemma projectObj_tensor (X Y : F C) : projectObj m (X ⊗ Y) =
    projectObj m X ⊗ projectObj m Y := rfl

@[simp]
lemma projectObj_star (X : F C) : projectObj m X⋆ = (projectObj m X)⋆ := rfl

@[simp]
lemma projectObj_map (f : C → E) (m : E → D) (X : F C) :
    projectObj m (X.map f) = X.projectObj (m ∘ f) := by
  induction X <;> simp_all

@[simp]
lemma projectObj_of_function (m : C → E) (X : F C) :
    projectObj (.of <| m ·) X = X.map m := by
  induction X <;> simp_all

open Hom

variable [TwistedCategory D]

def projectMapAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (projectObj m X ⟶ projectObj m Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, l_hom _ => (λ_ _).hom
  | _, _, l_inv _ => (λ_ _).inv
  | _, _, ρ_hom _ => (ρ_ _).hom
  | _, _, ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.comp f g => projectMapAux f ≫ projectMapAux g
  | _, _, Hom.whiskerLeft X p => projectObj m X ◁ projectMapAux p
  | _, _, Hom.whiskerRight p X => projectMapAux p ▷ projectObj m X
  | _, _, Hom.tensor f g => projectMapAux f ⊗ₘ projectMapAux g
  | _, _, Hom.star f => (projectMapAux f)⋆
  | _, _, χ_hom _ _ => (χ_ _ _).hom
  | _, _, χ_inv _ _ => (χ_ _ _).inv
  | _, _, ε_hom _ => (e_ _).hom
  | _, _, ε_inv _ => (e_ _).inv
  | _, _, twist_hom _ => (ς_ _).hom
  | _, _, twist_inv _ => (ς_ _).inv

@[simp]
def projectMap (X Y : F C) : (categoryFreeTwistedCategory.Hom X Y) →
    (projectObj m X ⟶ projectObj m Y) :=
  _root_.Quotient.lift (projectMapAux m) <| by
    intro f g h
    induction h with
    | refl => rfl
    | symm _ _ _ hfg' => exact hfg'.symm
    | trans _ _ hfg hgh => exact hfg.trans hgh
    | comp _ _ hf hg => dsimp only [projectMapAux]; rw [hf, hg]
    | whiskerLeft _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
    | whiskerRight _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
    | tensor _ _ hfg hfg' => dsimp only [projectMapAux]; rw [hfg, hfg']
    | tensorHom_def f g =>
        dsimp only [projectMapAux, projectObj]; rw [MonoidalCategory.tensorHom_def]
    | comp_id => dsimp only [projectMapAux]; rw [Category.comp_id]
    | id_comp => dsimp only [projectMapAux]; rw [Category.id_comp]
    | assoc => dsimp only [projectMapAux]; rw [Category.assoc]
    | id_tensorHom_id => dsimp only [projectMapAux]; rw [MonoidalCategory.id_tensorHom_id]; rfl
    | tensorHom_comp_tensorHom =>
      dsimp only [projectMapAux]; rw [MonoidalCategory.tensorHom_comp_tensorHom]
    | whiskerLeft_id =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.whiskerLeft_id]
    | id_whiskerRight =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.id_whiskerRight]
    | α_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | α_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | associator_naturality =>
        dsimp only [projectMapAux]; rw [MonoidalCategory.associator_naturality]
    | ρ_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | ρ_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | ρ_naturality =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.rightUnitor_naturality]
    | l_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | l_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | l_naturality =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.leftUnitor_naturality]
    | pentagon =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.pentagon]
    | triangle =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.triangle]
    -- START NAT'S STUFF
    | star _ hf => dsimp only [projectMapAux]; rw [hf]
    | starHom_comp_starHom _ hf =>
      dsimp only [projectMapAux]; rw [InvolutiveCategory.starHom_comp_starHom]
    | starHom_id => dsimp only [projectMapAux, projectObj]; rw [InvolutiveCategory.starHom_id]
    | ε_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | ε_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | ε_naturality =>
        dsimp only [projectMapAux, projectObj]
        exact InvolutiveCategory.involutor_naturality _
    | χ_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | χ_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | χ_naturality =>
        dsimp only [projectMapAux, projectObj]
        exact InvolutiveCategory.skewator_naturality _ _
    | f3 =>
        dsimp only [projectMapAux, projectObj]
        exact f3 _ _ _
    | n2 =>
        dsimp only [projectMapAux, projectObj]
        exact n2 _ _
    | a =>
        dsimp only [projectMapAux, projectObj]
        exact a _
    | twist_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | twist_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | twist_naturality =>
        dsimp only [projectMapAux, projectObj]
        exact TwistedCategory.twist_naturality _
    | tℓ =>
        dsimp only [projectMapAux, projectObj]
        exact tℓ _ _ _

def project : F C ⥤ D where
  obj := projectObj m
  map := projectMap m _ _
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

variable {D : Type u'} [Quiver.{v'} (F D)] (m : C → D)

def projectFree : F C ⥤ F D := project (FreeTwistedCategory.of <| m ·)

end CategoryTheory.FreeTwistedCategory

