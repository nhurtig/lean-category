import Mathlib
import Mathlib.CategoryTheory.Discrete.Basic
import LeanCategory.FreeEgger

@[expose] public section

universe u

namespace CategoryTheory

open InvolutiveCategory MonoidalCategory Functor

namespace FreeTwistedCategory

variable {C : Type u}

section

variable (C)

/-- We say an object in the free monoidal category is in normal form if it is of the form
`(((𝟙_ C) ⊗ X₁) ⊗ X₂) ⊗ ⋯`. -/
inductive NormalInvolutiveMonoidalObject : Type u
  | unit : NormalInvolutiveMonoidalObject
  | tensor : NormalInvolutiveMonoidalObject → C → Bool → NormalInvolutiveMonoidalObject

end

/- local notation "F" => FreeMonoidalCategory -/

local notation "N" => Discrete ∘ NormalInvolutiveMonoidalObject

instance (x y : N C) : Subsingleton (x ⟶ y) := Discrete.instSubsingletonDiscreteHom _ _

/-- Auxiliary definition for `inclusion`. -/
@[simp]
def inclusionObj : NormalInvolutiveMonoidalObject C → F C
  | NormalInvolutiveMonoidalObject.unit => unit
  | NormalInvolutiveMonoidalObject.tensor n a b => tensor (inclusionObj n) <|
      if b then (of a).star else (of a)

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

-- bool starts out false, but is true when things are starred
def normalizeObj : Bool → F C → NormalInvolutiveMonoidalObject C → NormalInvolutiveMonoidalObject C
  | _, unit, n => n
  | b, of X, n => NormalInvolutiveMonoidalObject.tensor n X b
  | false, tensor X Y, n => normalizeObj false Y (normalizeObj false X n)
  | true, tensor X Y, n => normalizeObj true X (normalizeObj true Y n)
  | b, star X, n => normalizeObj (!b) X n

@[simp]
theorem normalizeObj_unitor (n : NormalInvolutiveMonoidalObject C) : normalizeObj b (𝟙_ (F C)) n = n :=
  rfl

@[simp]
theorem normalizeObj_tensor_nostar (X Y : F C) (n : NormalInvolutiveMonoidalObject C) :
    normalizeObj false (X ⊗ Y) n = normalizeObj false Y (normalizeObj false X n) :=
  rfl

@[simp]
theorem normalizeObj_tensor_star (X Y : F C) (n : NormalInvolutiveMonoidalObject C) :
    normalizeObj true (X ⊗ Y) n = normalizeObj true X (normalizeObj true Y n) :=
  rfl

@[simp]
theorem normalizeObj_star (X : F C) (n : NormalInvolutiveMonoidalObject C) :
    normalizeObj b X⋆ n = normalizeObj (!b) X n :=
  rfl

/-- Auxiliary definition for `normalize`. -/
def normalizeObj' (starred : Bool) (X : F C) : N C ⥤ N C := Discrete.functor fun n ↦ ⟨normalizeObj starred X n⟩

section

open Hom

#check MonoidalCategory.tensorHom_def
/-- Auxiliary definition for `normalize`. Here we prove that objects that are related by
associators and unitors map to the same normal form. -/
@[simp]
def normalizeMapAux : ∀ {X Y : F C}, (starred : Bool) → (X ⟶ᵐ Y) → (normalizeObj' starred X ⟶ normalizeObj' starred Y)
  | _, _, _, Hom.id _ => 𝟙 _
  | _, _, true, α_hom X Y Z => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, false, α_hom X Y Z => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, true, α_inv _ _ _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, false, α_inv _ _ _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, true, l_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, false, l_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, true,  l_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, false,  l_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, true, ρ_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, false, ρ_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, true, ρ_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, false, ρ_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, true, χ_hom _ _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, false, χ_hom _ _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, true, χ_inv _ _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, false, χ_inv _ _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, true, ε_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, false, ε_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, true, ε_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, false, ε_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, starred, (@Hom.comp _ _ _ _ f g) => normalizeMapAux starred f ≫ normalizeMapAux starred g
  | _, _, false, (@Hom.tensor _ T _ _ W f g) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeMapAux false g).app ⟨normalizeObj false T X⟩ ≫
      (normalizeObj' false W).map ((normalizeMapAux false f).app ⟨X⟩)
  | _, _, true, (@Hom.tensor _ T _ _ W f g) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeObj' true T).map ((normalizeMapAux true g).app ⟨X⟩) ≫
      (normalizeMapAux true f).app ⟨normalizeObj true W X⟩
  | _, _, false, (@Hom.whiskerLeft _ T _ W f) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeMapAux false f).app ⟨normalizeObj false T X⟩
  | _, _, true, (@Hom.whiskerLeft _ T _ W f) =>
    Discrete.natTrans <| fun X => (normalizeObj' true T).map <| (normalizeMapAux true f).app X
  | _, _, false, (@Hom.whiskerRight _ T _ f W) =>
    Discrete.natTrans <| fun X => (normalizeObj' false W).map <| (normalizeMapAux false f).app X
  | _, _, true, (@Hom.whiskerRight _ T _ f W) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeMapAux true f).app ⟨normalizeObj true W X⟩
  | _, _, false, (@Hom.star _ _ W f) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeMapAux true f).app ⟨X⟩
  | _, _, true, (@Hom.star _ _ W f) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeMapAux false f).app ⟨X⟩
  | _, _, _, twist_hom _ => sorry
  | _, _, _, twist_inv _ => sorry

end

section

variable (C)

/-- Our normalization procedure works by first defining a functor `F C ⥤ (N C ⥤ N C)` (which turns
out to be very easy), and then obtain a functor `F C ⥤ N C` by plugging in the normal object
`𝟙_ C`. -/
@[simp]
def normalize (starred : Bool) : F C ⥤ N C ⥤ N C where
  obj X := normalizeObj' starred X
  map {X Y} := _root_.Quotient.lift (normalizeMapAux starred) (by cat_disch)

/-- A variant of the normalization functor where we consider the result as an object in the free
monoidal category (rather than an object of the discrete subcategory of objects in normal form). -/
@[simp]
def normalize' (starred : Bool) : F C ⥤ N C ⥤ F C :=
  normalize C starred ⋙ (whiskeringRight _ _ _).obj inclusion

/-- The normalization functor for the free monoidal category over `C`. -/
def fullNormalize : F C ⥤ N C where
  obj X := ((normalize C false).obj X).obj ⟨NormalInvolutiveMonoidalObject.unit⟩
  map f := ((normalize C false).map f).app ⟨NormalInvolutiveMonoidalObject.unit⟩

/-- Given an object `X` of the free monoidal category and an object `n` in normal form, taking
the tensor product `n ⊗ X` in the free monoidal category is functorial in both `X` and `n`. -/
@[simp]
def tensorFunc : Bool → F C ⥤ N C ⥤ F C
  | false => {
      obj X := Discrete.functor fun n => inclusion.obj ⟨n⟩ ⊗ X
      map f := Discrete.natTrans (fun n =>  _ ◁ f)
      /- map_id := sorry -/
      /- map_comp := sorry -/
      }
  | true => {
      obj X := Discrete.functor fun n => X ⊗ inclusion.obj ⟨n⟩
      map f := Discrete.natTrans (fun n =>  f ▷ _)
      /- map_id := sorry -/
      /- map_comp := sorry -/
      }

theorem tensorFunc_map_app_false {X Y : F C} (f : X ⟶ Y) (n) : ((tensorFunc C false).map f).app n = _ ◁ f :=
  rfl

theorem tensorFunc_map_app_true {X Y : F C} (f : X ⟶ Y) (n) : ((tensorFunc C true).map f).app n = f ▷ _ :=
  rfl

theorem tensorFunc_obj_map_false (Z : F C) {n n' : N C} (f : n ⟶ n') :
    ((tensorFunc C false).obj Z).map f = inclusion.map f ▷ Z := by
  cases n
  cases n'
  rcases f with ⟨⟨h⟩⟩
  dsimp at h
  subst h
  simp


lemma x {C : Type u} {a : C} {x : N C} : True := by
  have : ((tensorFunc C true).obj (of a)).obj x ≅ ((normalize' C true).obj (of a)).obj x := by
    simp [normalizeObj', normalizeObj]
    sorry
  sorry
/- C : Type u -/
/- a✝ : C -/
/- x✝ : (Discrete ∘ NormalInvolutiveMonoidalObject) C -/
/- ⊢ ((tensorFunc C true).obj (of a✝)).obj x✝ ≅ ((normalize' C true).obj (of a✝)).obj x✝ -/



/-- Auxiliary definition for `normalizeIso`. Here we construct the isomorphism between
`n ⊗ X` and `normalize X n`. -/
@[simp]
def normalizeIsoApp :
    ∀ (starred : Bool) (X : F C) (n : N C), ((tensorFunc C starred).obj X).obj n ≅ ((normalize' C starred).obj X).obj n
  | false, of _, _ => Iso.refl _
  | true, of _, _ => Iso.refl _
  | false, unit, _ => ρ_ _
  | true, unit, _ => λ_ _
  | false, tensor X a, n =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp false X n) a ≪≫ normalizeIsoApp false _ _
  | _, star X, n =>
      (normalizeIsoApp X n)

/-- Almost non-definitionally equal to `normalizeIsoApp`, but has a better definitional property
in the proof of `normalize_naturality`. -/
@[simp]
def normalizeIsoApp' :
    ∀ (X : F C) (n : NormalInvolutiveMonoidalObject C), inclusionObj n ⊗ X ≅ inclusionObj (normalizeObj X n)
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

theorem normalizeObj_congr (n : NormalInvolutiveMonoidalObject C) {X Y : F C} (f : X ⟶ Y) :
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

theorem normalize_naturality (n : NormalInvolutiveMonoidalObject C) {X Y : F C} (f : X ⟶ Y) :
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
  (fun X => (λ_ X).symm ≪≫ ((normalizeIso C).app X).app ⟨NormalInvolutiveMonoidalObject.unit⟩)
    (by
      intro X Y f
      dsimp
      rw [leftUnitor_inv_naturality_assoc, Category.assoc, Iso.cancel_iso_inv_left]
      exact
        congr_arg (fun f => NatTrans.app f (Discrete.mk NormalInvolutiveMonoidalObject.unit))
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
