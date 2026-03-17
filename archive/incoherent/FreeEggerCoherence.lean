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
def injectObj : NormalInvolutiveMonoidalObject C → FreeInvolutiveCategory C
  | NormalInvolutiveMonoidalObject.unit => unit
  | NormalInvolutiveMonoidalObject.tensor n a b => tensor (injectObj n) <|
      if b then (of a).star else (of a)

/-- The discrete subcategory of objects in normal form includes into the free monoidal category. -/
def inject : N C ⥤ FreeInvolutiveCategory C :=
  Discrete.functor injectObj

@[simp]
theorem inject_obj (X : N C) :
    inject.obj X = injectObj X.as :=
  rfl

-- TODO comment this out cuz it looks wacky
@[simp]
theorem inject_map {X Y : N C} (f : X ⟶ Y) :
    inject.map f = eqToHom (congr_arg _ (Discrete.ext (Discrete.eq_of_hom f))) := rfl

-- bool starts out false, but is true when things are starred
def extend_normalObj : Bool → FreeInvolutiveCategory C → NormalInvolutiveMonoidalObject C → NormalInvolutiveMonoidalObject C
  | _, unit, n => n
  | b, of X, n => NormalInvolutiveMonoidalObject.tensor n X b
  | false, tensor X Y, n => extend_normalObj false Y (extend_normalObj false X n)
  | true, tensor X Y, n => extend_normalObj true X (extend_normalObj true Y n)
  | b, star X, n => extend_normalObj (b.not) X n

/- @[simp] -/
/- def normalizeObj : F C → NormalInvolutiveMonoidalObject C → NormalInvolutiveMonoidalObject C -/
/-   | unit, n => n -/
/-   | of X, n => NormalInvolutiveMonoidalObject.tensor n X false -/
/-   | tensor X Y, n => normalizeObj X (normalizeObj Y n) -/
/-   | star unit, n => n -/
/-   | star (of X), n => n.tensor X true -/
/-   | star (tensor X Y), n => normalizeObj Y (normalizeObj X n) -/
/-   | star (star X), n => normalizeObj X n -/

@[simp]
theorem normalizeObj_unitor (n : NormalInvolutiveMonoidalObject C) : extend_normalObj b (𝟙_ (FreeInvolutiveCategory C)) n = n :=
  rfl

@[simp]
theorem normalizeObj_tensor_nostar (X Y : FreeInvolutiveCategory C) (n : NormalInvolutiveMonoidalObject C) :
    extend_normalObj false (X ⊗ Y) n = extend_normalObj false Y (extend_normalObj false X n) :=
  rfl

@[simp]
theorem normalizeObj_tensor_star (X Y : FreeInvolutiveCategory C) (n : NormalInvolutiveMonoidalObject C) :
    extend_normalObj true (X ⊗ Y) n = extend_normalObj true X (extend_normalObj true Y n) :=
  rfl

@[simp]
theorem normalizeObj_star (X : FreeInvolutiveCategory C) (n : NormalInvolutiveMonoidalObject C) :
    extend_normalObj b X⋆ n = extend_normalObj (b.not) X n :=
  rfl

/-- Auxiliary definition for `normalize`. -/
def extend_normalObj' (starred : Bool) (X : FreeInvolutiveCategory C) : N C ⥤ N C := Discrete.functor fun n ↦ ⟨extend_normalObj starred X n⟩

@[simp]
lemma extend_normalObj'_obj (X : FreeInvolutiveCategory C) (starred : Bool) (n : N C) :
    (extend_normalObj' starred X).obj n = ⟨extend_normalObj starred X n.as⟩ := rfl

@[simp]
lemma extend_normalObj'_unitor (starred : Bool) (n : N C) :
    (extend_normalObj' starred (𝟙_ (FreeInvolutiveCategory C))).obj n = n := by
  cases n
  dsimp [extend_normalObj']

@[simp]
lemma extend_normalObj'_tensor_nostar (X Y : FreeInvolutiveCategory C) (n : N C) :
    (extend_normalObj' false (X ⊗ Y)).obj n = (extend_normalObj' false Y).obj ((extend_normalObj' false X).obj n) := by
  cases n
  dsimp [extend_normalObj', normalizeObj_tensor_nostar, extend_normalObj]

section

open Hom

#check MonoidalCategory.tensorHom_def
/-- Auxiliary definition for `normalize`. Here we prove that objects that are related by
associators and unitors map to the same normal form. -/
@[simp]
def extend_normalMapAux : ∀ {X Y : FreeInvolutiveCategory C}, (starred : Bool) → (X ⟶ᵐ Y) → (extend_normalObj' starred X ⟶ extend_normalObj' starred Y)
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
  | _, _, starred, (@Hom.comp _ _ _ _ f g) => extend_normalMapAux starred f ≫ extend_normalMapAux starred g
  | _, _, false, (@Hom.tensor _ T _ _ W f g) =>
    Discrete.natTrans <| fun ⟨X⟩ => (extend_normalMapAux false g).app ⟨extend_normalObj false T X⟩ ≫
      (extend_normalObj' false W).map ((extend_normalMapAux false f).app ⟨X⟩)
  | _, _, true, (@Hom.tensor _ T _ _ W f g) =>
    Discrete.natTrans <| fun ⟨X⟩ => (extend_normalObj' true T).map ((extend_normalMapAux true g).app ⟨X⟩) ≫
      (extend_normalMapAux true f).app ⟨extend_normalObj true W X⟩
  | _, _, false, (@Hom.whiskerLeft _ T _ W f) =>
    Discrete.natTrans <| fun ⟨X⟩ => (extend_normalMapAux false f).app ⟨extend_normalObj false T X⟩
  | _, _, true, (@Hom.whiskerLeft _ T _ W f) =>
    Discrete.natTrans <| fun X => (extend_normalObj' true T).map <| (extend_normalMapAux true f).app X
  | _, _, false, (@Hom.whiskerRight _ T _ f W) =>
    Discrete.natTrans <| fun X => (extend_normalObj' false W).map <| (extend_normalMapAux false f).app X
  | _, _, true, (@Hom.whiskerRight _ T _ f W) =>
    Discrete.natTrans <| fun ⟨X⟩ => (extend_normalMapAux true f).app ⟨extend_normalObj true W X⟩
  | _, _, false, (@Hom.star _ _ W f) =>
    Discrete.natTrans <| fun ⟨X⟩ => (extend_normalMapAux true f).app ⟨X⟩
  | _, _, true, (@Hom.star _ _ W f) =>
    Discrete.natTrans <| fun ⟨X⟩ => (extend_normalMapAux false f).app ⟨X⟩
  | _, _, _, twist_hom _ => sorry
  | _, _, _, twist_inv _ => sorry

end

section

variable (C)

/-- Our normalization procedure works by first defining a functor `F C ⥤ (N C ⥤ N C)` (which turns
out to be very easy), and then obtain a functor `F C ⥤ N C` by plugging in the normal object
`𝟙_ C`. -/
@[simp]
def extend_normal (starred : Bool) : FreeInvolutiveCategory C ⥤ N C ⥤ N C where
  obj X := extend_normalObj' starred X
  map {X Y} := _root_.Quotient.lift (extend_normalMapAux starred) (by cat_disch)

/-- A variant of the normalization functor where we consider the result as an object in the free
monoidal category (rather than an object of the discrete subcategory of objects in normal form). -/
@[simp]
def extend_normal' (starred : Bool) : FreeInvolutiveCategory C ⥤ N C ⥤ FreeInvolutiveCategory C :=
  extend_normal C starred ⋙ (whiskeringRight _ _ _).obj inject

def extendFunctor (starred : Bool) (n : N C) : FreeInvolutiveCategory C ⥤ N C where
  obj X := ((extend_normal C starred).obj X).obj n
  map f := ((extend_normal C starred).map f).app n

@[simp]
lemma extendFunctor_obj (X : FreeInvolutiveCategory C) (starred : Bool) (n : N C) :
    (extendFunctor C starred n).obj X = ((extend_normal C starred).obj X).obj n :=
  rfl

/-- The normalization functor for the free monoidal category over `C`. -/
def project : FreeInvolutiveCategory C ⥤ N C := extendFunctor C false ⟨NormalInvolutiveMonoidalObject.unit⟩

@[simp]
lemma project_obj (X : FreeInvolutiveCategory C) :
    (project C).obj X = ((extend_normal C false).obj X).obj ⟨NormalInvolutiveMonoidalObject.unit⟩ :=
  rfl

@[simp]
lemma my_silly_simp : injectObj (extend_normalObj b X n.as) = ((extendFunctor C b n) ⋙ inject).obj X := by
  rfl

@[simp]
lemma my_silly_simp' : injectObj (extend_normalObj (!false) X n.as) = ((extendFunctor C true n) ⋙ inject).obj X := by
  rfl

@[simp]
lemma wtf_guys : !false = true := by
  rfl

@[simp]
lemma wtf_guys' : !true = false := by
  rfl

#check Bool

-- injectObj (extend_normalObj (!false) Z n.as)
-- to
-- (extendFunctor C true n ⋙ inject)
@[simp]
def canonicalIso : ∀ (X : FreeInvolutiveCategory C) (starred : Bool) (n : N C), (injectObj n.as) ⊗ (if starred then X⋆ else X) ≅ (extendFunctor C starred n ⋙ inject).obj X
  | unit, false, _ => ρ_ _
  | unit, true, _ => (whiskerLeftIso _ star_tensorObj_aux) ≪≫ ρ_ _
  | of X, false, _ => Iso.refl _
  | of X, true, _ => Iso.refl _
  | tensor X Y, false, n =>
      (α_ _ _ _).symm ≪≫ whiskerRightIso (canonicalIso X false n) _ ≪≫ canonicalIso Y false (⟨extend_normalObj false X n.as⟩)
  | tensor X Y, true, n =>
      whiskerLeftIso _ (χ_ _ _).symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso (canonicalIso Y true n) _ ≪≫ canonicalIso X true (⟨extend_normalObj false Y⋆ n.as⟩)
  | star X, true, n => (whiskerLeftIso _ (e_ _)) ≪≫ canonicalIso X false n
  | star X, false, n => canonicalIso X true n

attribute [-simp] star_tensorObj_aux

lemma canonicalIso_natural_nostar (X Y : FreeInvolutiveCategory C) (f : X ⟶ Y) (n : N C) :
    ((injectObj n.as) ◁ f ≫ (canonicalIso C Y false n).hom =
      (canonicalIso C X false n).hom ≫ ((extendFunctor C false n ⋙ inject).map f)) ∧
    ((injectObj n.as) ◁ f⋆ ≫ (canonicalIso C Y true n).hom =
          (canonicalIso C X true n).hom ≫ ((extendFunctor C true n ⋙ inject).map f)) := by
  induction f using Quotient.inductionOn
  case h =>
  rename_i f
  induction f
  /- any_goals simp_mk -/
  case α_hom X Y Z =>
    simp_mk
    rw [my_silly_simp]
    rw [← whisker_exchange_assoc (canonicalIso C Z true n).hom (χ_ Y X).inv]
    /- simp -/
    sorry
  all_goals sorry
  case comp ih₁ ih₂ =>
    simp_mk
    rw [ih₂, ← Category.assoc, ih₁]
    simp
  /- any_goals simp -/
  /- all_goals sorry -/
  /- cases n -/
  /- cases starred -/
  /- sorry -/
  /- all_goals simp [canonicalIso, extend_normalObj, extend_normalObj', tensor_eq_tensor, Iso -/

def fullNormalizeIso : 𝟭 (FreeInvolutiveCategory C) ≅ project C ⋙ inject :=
  NatIso.ofComponents (fun X => (λ_ _).symm ≪≫ canonicalIso C X false ⟨NormalInvolutiveMonoidalObject.unit⟩) <| by
    rintro X Y ⟨f⟩
    simp
    rw [leftUnitor_inv_naturality_assoc, Iso.cancel_iso_inv_left]
    induction f
    sorry
/-- Given an object `X` of the free monoidal category and an object `n` in normal form, taking
the tensor product `n ⊗ X` in the free monoidal category is functorial in both `X` and `n`. -/
@[simp]
def tensorFunc : Bool → FreeInvolutiveCategory C ⥤ N C ⥤ FreeInvolutiveCategory C
  | false => {
      obj X := Discrete.functor fun n => inject.obj ⟨n⟩ ⊗ X
      map f := Discrete.natTrans (fun n =>  _ ◁ f)
      /- map_id := sorry -/
      /- map_comp := sorry -/
      }
  | true => {
      obj X := Discrete.functor fun n => inject.obj ⟨n⟩ ⊗ X⋆
      map f := Discrete.natTrans (fun n => _ ◁ f⋆)
      /- map_id := sorry -/
      /- map_comp := sorry -/
      }

theorem tensorFunc_map_app_false {X Y : FreeInvolutiveCategory C} (f : X ⟶ Y) (n) : ((tensorFunc C false).map f).app n = _ ◁ f :=
  rfl

theorem tensorFunc_map_app_true {X Y : FreeInvolutiveCategory C} (f : X ⟶ Y) (n) : ((tensorFunc C true).map f).app n = _ ◁ f⋆ :=
  rfl

theorem tensorFunc_obj_map_false (Z : FreeInvolutiveCategory C) {n n' : N C} (f : n ⟶ n') :
    ((tensorFunc C false).obj Z).map f = inject.map f ▷ Z := by
  cases n
  cases n'
  rcases f with ⟨⟨h⟩⟩
  dsimp at h
  subst h
  simp

theorem tensorFunc_obj_map_true (Z : FreeInvolutiveCategory C) {n n' : N C} (f : n ⟶ n') :
    ((tensorFunc C true).obj Z).map f = inject.map f ▷ Z⋆ := by
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
    ∀ (starred : Bool) (X : FreeInvolutiveCategory C) (n : N C), ((tensorFunc C starred).obj X).obj n ≅ ((extend_normal' C starred).obj X).obj n
  | false, of _, _ => Iso.refl _
  | true, of _, _ => Iso.refl _
  | false, unit, _ => ρ_ _
  | true, unit, _ =>
      whiskerLeftIso _ star_tensorObj_aux ≪≫ ρ_ _
  | false, tensor X a, n =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp false X n) a ≪≫ normalizeIsoApp false _ _
  | true, tensor X a, n =>
      whiskerLeftIso _ (χ_ _ _).symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp true a n) _ ≪≫ normalizeIsoApp true X _
  | false, star X, n =>
      normalizeIsoApp true X n
  | true, star X, n =>
      whiskerLeftIso _ (e_ _) ≪≫ normalizeIsoApp false X n

/-- Almost non-definitionally equal to `normalizeIsoApp`, but has a better definitional property
in the proof of `normalize_naturality`. -/
@[simp]
def normalizeIsoApp' :
    ∀ (starred : Bool) (X : FreeInvolutiveCategory C) (n : NormalInvolutiveMonoidalObject C), injectObj n ⊗ (if starred then X⋆ else X) ≅ injectObj (extend_normalObj starred X n)
  | false, of _, _ => Iso.refl _
  | true, of _, _ => Iso.refl _
  | false, unit, _ => ρ_ _
  | true, unit, _ =>
      whiskerLeftIso _ star_tensorObj_aux ≪≫ ρ_ _
  | false, tensor X a, n =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp' false X n) a ≪≫ normalizeIsoApp' false _ _
  | true, tensor X a, n =>
      whiskerLeftIso _ (χ_ _ _).symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp' true a n) _ ≪≫ normalizeIsoApp' true X _
  | false, star X, n =>
      normalizeIsoApp' true X n
  | true, star X, n =>
      whiskerLeftIso _ (e_ _) ≪≫ normalizeIsoApp' false X n

/- theorem normalizeIsoApp_eq_star : -/
/-     ∀ (X : F C) (n : N C), normalizeIsoApp C true X n = normalizeIsoApp' C true X⋆ n.as := sorry -/

/- theorem normalizeIsoApp_eq_nostar : -/
/-     ∀ (X : F C) (n : N C), normalizeIsoApp C false X n = normalizeIsoApp' C false X n.as -/
/-   | of _, _ => rfl -/
/-   | unit, _ => rfl -/
/-   | tensor X Y, n => by -/
/-       rw [normalizeIsoApp, normalizeIsoApp'] -/
/-       rw [normalizeIsoApp_eq X n] -/
/-       rw [normalizeIsoApp_eq Y ⟨normalizeObj X n.as⟩] -/
/-       rfl -/

@[simp]
theorem normalizeIsoApp_tensor_nostar (X Y : FreeInvolutiveCategory C) (n : N C) :
    normalizeIsoApp C false (X ⊗ Y) n =
      (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp C false X n) Y ≪≫ normalizeIsoApp _ false _ _ :=
  rfl

@[simp]
theorem normalizeIsoApp_tensor_star (X Y : FreeInvolutiveCategory C) (n : N C) :
    normalizeIsoApp C true (X ⊗ Y) n =
      whiskerLeftIso _ (χ_ _ _).symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp C true Y n) _ ≪≫ normalizeIsoApp C true X _ :=
  rfl

@[simp]
theorem normalizeIsoApp_unitor_nostar (n : N C) : normalizeIsoApp C false (𝟙_ (FreeInvolutiveCategory C)) n = ρ_ _ :=
  rfl

@[simp]
theorem normalizeIsoApp_unitor_star (n : N C) : normalizeIsoApp C true (𝟙_ (FreeInvolutiveCategory C)) n = whiskerLeftIso _ star_tensorObj_aux ≪≫ ρ_ _ :=
  rfl

/-- Auxiliary definition for `normalizeIso`. -/
@[simps!]
def normalizeIsoAux (starred : Bool) (X : FreeInvolutiveCategory C) : (tensorFunc C starred).obj X ≅ (extend_normal' C starred).obj X :=
  NatIso.ofComponents (normalizeIsoApp C starred X)
    (by
      rintro ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩
      dsimp at f
      subst f
      dsimp
      simp)


section

variable {C}

theorem normalizeObj_congr (starred : Bool) (n : NormalInvolutiveMonoidalObject C) {X Y : FreeInvolutiveCategory C} (f : X ⟶ Y) :
    extend_normalObj starred X n = extend_normalObj starred Y n := by
  rcases f with ⟨f'⟩
  apply @congr_fun _ _ fun n => extend_normalObj starred X n
  clear n f
  induction f' with
  | comp _ _ _ _ => apply Eq.trans <;> assumption
  | whiskerLeft _ _ ih =>
      funext; cases starred
      · apply congr_fun ih
      · apply congr_fun ih
  | whiskerRight _ _ ih => funext; apply congr_arg₂ _ rfl (congr_fun ih _)
  | @tensor W X Y Z _ _ ih₁ ih₂ =>
      funext n
      simp [congr_fun ih₁ n, congr_fun ih₂ (extend_normalObj Y n)]
  | _ => funext; rfl

theorem normalize_naturality (n : NormalInvolutiveMonoidalObject C) {X Y : FreeInvolutiveCategory C} (f : X ⟶ Y) :
    injectObj n ◁ f ≫ (normalizeIsoApp' C Y n).hom =
      (normalizeIsoApp' C X n).hom ≫
        inject.map (eqToHom (Discrete.ext (normalizeObj_congr n f))) := by
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
def normalizeIso : tensorFunc C ≅ extend_normal' C :=
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
instance subsingleton_hom : Quiver.IsThin (FreeInvolutiveCategory C) := fun X Y =>
  ⟨fun f g => by
    have hfg : (project C).map f = (project C).map g := Subsingleton.elim _ _
    have hf := NatIso.naturality_2 (fullNormalizeIso.{u} C) f
    have hg := NatIso.naturality_2 (fullNormalizeIso.{u} C) g
    exact hf.symm.trans (Eq.trans (by simp only [Functor.comp_map, hfg]) hg)⟩

section Groupoid

section

open Hom

/-- Auxiliary construction for showing that the free monoidal category is a groupoid. Do not use
this, use `IsIso.inv` instead. -/
def inverseAux : ∀ {X Y : FreeInvolutiveCategory C}, (X ⟶ᵐ Y) → (Y ⟶ᵐ X)
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

instance : Groupoid.{u} (FreeInvolutiveCategory C) :=
  { (inferInstance : Category (FreeInvolutiveCategory C)) with
    inv := Quotient.lift (fun f => ⟦inverseAux f⟧) (by cat_disch) }

end Groupoid

end FreeMonoidalCategory

end CategoryTheory
