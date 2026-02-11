import Mathlib

variable {V : Type u} [Quiver.{v} (List V)]

inductive Hom : List V → List V → Type max u v
  | of : (X ⟶ Y) → Hom X Y
  -- | id : (X : List V) → Hom X X
  | id : (X = Y) → Hom X Y
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  -- | whiskerLeft (X : F C) {Y₁ Y₂} (f : Hom Y₁ Y₂) : Hom (X.tensor Y₁) (X.tensor Y₂)
  -- | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : F C) : Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W ++ X) (Y ++ Z)

open CategoryTheory

def StrictMonoidalProduct (X : Type u) := List X

notation "S " => StrictMonoidalProduct

instance myThingTODO : CategoryStruct (S V) where
  Hom := Hom
  id _ := Hom.id rfl
  -- id := Hom.id
  comp := Hom.comp

-- infixr:10 " ⟶ᵐ " => Hom
-- instance : Append (S V) where
--   append := List.append

instance : Monoid (S V) where
  one := []
  mul := List.append
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

-- @[simp]
-- theorem mul_assoc' [Monoid G] : ∀ a b c : G, a * b * c = a * (b * c) :=
--   Semigroup.mul_assoc

-- notation "𝟙ᵐ" => Hom.id
-- infixr:70 " ≫ᵐ " => Hom.comp
def myTensor {W X Y Z : S V} (f : W ⟶ Y) (g : X ⟶ Z) : (W * X) ⟶ (Y * Z) := Hom.tensor f g

infixr:70 " ⊗ " => myTensor
-- infixr:70 " ⊗ " => List.append

-- def Hom.eqToHom {X Y : List V} (h : X = Y) : Hom X Y := by
--   rw [h]
--   exact Hom.id _

@[simp]
def Hom.whiskerLeft (X : S V) {Y₁ Y₂ : S V} (f : Y₁ ⟶ Y₂) : (X * Y₁) ⟶ (X * Y₂) :=
  (𝟙 X) ⊗ f

@[simp]
def Hom.whiskerRight {X₁ X₂ : S V} (f : X₁ ⟶ X₂) (Y : S V) : (X₁ * Y) ⟶ (X₂ * Y) :=
  f ⊗ (𝟙 Y)

infixr:81 " ◁ " => Hom.whiskerLeft
infixl:81 " ▷ " => Hom.whiskerRight

#check eqToHom
#check List.append_nil

-- variable {X Y : S V}
-- #check X ⟶ Y
-- #check X ⟶ Y
-- #synth Quiver (S V)

inductive HomEquiv : ∀ {A B : S V}, (A ⟶ B) → (A ⟶ B) → Prop
  | refl (f : X ⟶ Y) : HomEquiv f f
  | comp {f f' : X ⟶ Y} {g g' : Y ⟶ Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f ≫ g) (f' ≫ g')
  | tensor {f f' : W ⟶ X} {g g' : Y ⟶ Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f ⊗ g) (f' ⊗ g')
  | comp_id (f : X ⟶ Y) : HomEquiv (f ≫ (𝟙 _)) f
  | id_comp (f : X ⟶ Y) : HomEquiv ((𝟙 _ ) ≫ f) f
  | assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
      HomEquiv ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
  | tensor_assoc (f : P ⟶ Q) (g : W ⟶ X) (h : Y ⟶ Z) :
      HomEquiv (((f ⊗ g) ⊗ h) ≫ (.id (mul_assoc Q X Z))) ((.id (mul_assoc P W Y)) ≫ (f ⊗ (g ⊗ h)))
  -- | tensor_assoc (f : P ⟶ Q) (g : W ⟶ X) (h : Y ⟶ Z) :
  --     HomEquiv (((f ⊗ g) ⊗ h) ≫ (eqToHom (mul_assoc Q X Z))) ((eqToHom (mul_assoc P W Y)) ≫ (f ⊗ (g ⊗ h)))
  -- | tensor_id_left (f : X ⟶ Y) : HomEquiv (((𝟙 1) ⊗ f)) f
  | tensor_id_left (f : X ⟶ Y) : HomEquiv (((𝟙 1) ⊗ f) ≫ (.id (one_mul Y))) ((.id (one_mul X)) ≫ f)
  | tensor_id_right (f : X ⟶ Y) : HomEquiv ((f ⊗ (𝟙 1)) ≫ (.id (mul_one Y))) ((.id (mul_one X)) ≫ f)
  -- | tensor_id_left (f : X ⟶ Y) : HomEquiv (((𝟙 1) ⊗ f) ≫ (eqToHom (one_mul Y))) ((eqToHom (one_mul X)) ≫ f)
  -- | tensor_id_right (f : X ⟶ Y) : HomEquiv ((f ⊗ (𝟙 1)) ≫ (eqToHom (mul_one Y))) ((eqToHom (mul_one X)) ≫ f)
  | id_tensorHom_id {X Y : S V} : HomEquiv ((𝟙 X) ⊗ (𝟙 Y)) (𝟙 _)
  | tensorHom_comp_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
      (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    HomEquiv ((f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂)) ((f₁ ≫ g₁) ⊗ (f₂ ≫ g₂))

  | id_comp_id : HomEquiv (.id p ≫ .id q) (.id (by simp [p, q]))
  | id_tensor_id : HomEquiv (.id p ⊗ .id q) (.id (by simp [p, q]))

  | symm (f g : X ⟶ Y) : HomEquiv f g → HomEquiv g f
  | trans {f g h : X ⟶ Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h

#check HomEquiv

  -- | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  -- | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  -- | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) :
  --     HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
  --       ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  -- | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  -- | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  -- | ρ_naturality {X Y} (f : X ⟶ᵐ Y) :
  --     HomEquiv ((f.whiskerRight unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  -- | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  -- | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  -- | l_naturality {X Y} (f : X ⟶ᵐ Y) :
  --     HomEquiv ((f.whiskerLeft unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  -- | pentagon {W X Y Z} :
  --     HomEquiv
  --       (((Hom.α_hom W X Y).whiskerRight Z).comp
  --         ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
  --       ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  -- | triangle {X Y} :
  --     HomEquiv ((Hom.α_hom X unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
  --       ((Hom.ρ_hom X).whiskerRight Y)

-- TODO Trans, symm, Equivalence

@[refl]
lemma HomEquiv.refl' {X Y : S V} (f : X ⟶ Y) : HomEquiv f f := HomEquiv.refl f

@[simp]
lemma HomEquiv.whiskerLeft (X : S V) {Y Z} {f f' : Y ⟶ Z} :
    HomEquiv f f' → HomEquiv (X ◁ f) (X ◁ f') := by
  intro hf
  apply HomEquiv.tensor
  · rfl
  · exact hf

@[simp]
lemma HomEquiv.whiskerRight {X Y} {f f' : X ⟶ Y} (Z : S V) :
    HomEquiv f f' → HomEquiv (f ▷ Z) (f' ▷ Z) := by
  intro hf
  apply HomEquiv.tensor
  · exact hf
  · rfl

  -- | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
  --     HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
@[simp]
lemma HomEquiv.tensorHom_def {X₁ Y₁ X₂ Y₂ : S V} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    HomEquiv (f ⊗ g) (f ▷ X₂ ≫ Y₁ ◁ g) := by
  simp
  symm
  trans
  tensorhom_comp_tensorhom
  sorry

@[simp]
lemma HomEquiv.whiskerLeft_id (X Y : S V) : HomEquiv (X ◁ (𝟙 Y)) (𝟙 (X * Y)) :=
  id_tensorHom_id

-- | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
-- | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
@[simp]
lemma HomEquiv.id_whiskerRight (X Y : S V) : HomEquiv ((𝟙 X) ▷ Y) (𝟙 (X * Y)) :=
  id_tensorHom_id

-- def Hom.associator {X Y Z : S V} : (X * (Y * Z)) ⟶ ((X * Y) * Z) := by
--   apply eqToHom
--   simp [mul

instance setoidHom (X Y : S V) : Setoid (X ⟶ Y) :=
⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

def myHom (X Y : List V) := Quotient (setoidHom X Y)

open HomEquiv

-- def StrictMonoidalProduct' (X : Type u) := List X

-- notation "S' " => StrictMonoidalProduct'

-- instance : Monoid (S' V) where
--   one := []
--   mul := List.append
--   mul_assoc := List.append_assoc
--   one_mul := List.nil_append
--   mul_one := List.append_nil

@[simp]
instance hi : Category (S V) where
  Hom X Y := myHom X Y
  id X := ⟦𝟙 X⟧
  comp f g := Quotient.map₂ (· ≫ ·) (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg) f g
  id_comp {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    constructor
  comp_id {X Y} := by
    rintro ⟨f⟩
    apply Quotient.sound
    constructor
  assoc {W X Y Z} := by
    rintro ⟨f⟩ ⟨g⟩ ⟨h⟩
    apply Quotient.sound
    constructor

#check eqToHom

#check eqToIso
#check eqToHom_naturality
-- z maps from b : β → f b ⟶ g b
-- β := List (Fin 3) (0 = A, 1 = B, 2 = C)
-- j = (A ⊗ B) ⊗ C
-- j' = A ⊗ (B ⊗ C)
-- f, g : β → C

@[simp]
theorem eqToHom_awesome [CategoryStruct C] {X Y : C} (p : X = Y) (q : Y = X) :
    eqToHom p ≫ eqToHom q = 𝟙 X ≫ 𝟙 X := by
  cases p
  cases q
  simp

-- #check Quotient.mk
-- @[simp]
-- theorem eqToHom_awesome2 {X Y : S V} (p : X = Y) (q : Y = X) :
--     Quotient.mk setoidHom (eqToHom p ≫ eqToHom q) = Quotient.mk (𝟙 X) := by
--   cases p
--   cases q
--   simp

-- sim. for tensor

#check HomEquiv.id_comp_id

lemma hi' {X Y Z : S V} {p : X = Y} {q : Y = Z} : HomEquiv (eqToHom p ≫ eqToHom q) (eqToHom (p.trans q)) := by
  cases p
  cases q
  simp
  apply HomEquiv.comp_id

instance : MonoidalCategory (S V) where
  tensorObj X Y := X * Y
  tensorHom f g := Quotient.map₂ (· ⊗ ·) (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg) f g
  tensorUnit := 1
  associator X Y Z := {
    hom := ⟦.id (by simp [mul_assoc])⟧ -- Quotient.mk (eqToHom (mul_assoc X Y Z)),
    inv := ⟦.id (by simp [mul_assoc])⟧ -- Quotient.mk (eqToHom (mul_assoc X Y Z)),
    hom_inv_id := by
      apply Quotient.sound
      simp
      apply HomEquiv.id_comp_id
    inv_hom_id := by
      apply Quotient.sound
      simp
      apply HomEquiv.id_comp_id
  }
  leftUnitor X := {
    hom := ⟦.id (by simp [one_mul])⟧,
    inv := ⟦.id (by simp [one_mul])⟧,
    hom_inv_id := by
      apply Quotient.sound
      simp
      apply HomEquiv.id_comp_id
    inv_hom_id := by
      apply Quotient.sound
      simp
      apply HomEquiv.id_comp_id
  }
  -- by
  --   apply eqToIso
  --   exact one_mul X
  rightUnitor X := {
    hom := ⟦.id (by simp [mul_one])⟧,
    inv := ⟦.id (by simp [mul_one])⟧,
    hom_inv_id := by
      apply Quotient.sound
      simp
      apply HomEquiv.id_comp_id
    inv_hom_id := by
      apply Quotient.sound
      simp
      apply HomEquiv.id_comp_id
  }
  -- rightUnitor X := by
  --   apply eqToIso
  --   exact mul_one X
  whiskerLeft X {Y₁ Y₂} f := Quotient.map (X ◁ ·) (fun _ _ hf ↦ HomEquiv.whiskerLeft X hf) f
  whiskerRight {X₁ X₂} f Y := Quotient.map (· ▷ Y) (fun _ _ hf ↦ HomEquiv.whiskerRight Y hf) f
  tensorHom_def {X₁ Y₁ X₂ Y₂} := by
    rintro ⟨f⟩ ⟨g⟩
    apply Quotient.sound
    apply HomEquiv.tensorHom_def
  id_tensorHom_id _ _ := Quotient.sound id_tensorHom_id
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact Quotient.sound (tensorHom_comp_tensorHom _ _ _ _)
  whiskerLeft_id X Y := Quotient.sound (HomEquiv.whiskerLeft_id X Y)
  id_whiskerRight X Y := Quotient.sound (HomEquiv.id_whiskerRight X Y)
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} := by
    -- intros f₁ f₂ f₃
    -- induction f₁ using Quotient.inductionOn
    -- induction f₂ using Quotient.inductionOn
    -- induction f₃ using Quotient.inductionOn
    -- simp
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    simp
    apply Quotient.sound
    apply HomEquiv.tensor_assoc
  leftUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    simp
    apply Quotient.sound
    simp
    apply HomEquiv.tensor_id_left
    -- trans
    -- · apply comp_id
    -- · symm; trans
    --   · apply id_comp
    --   · symm
    --     apply HomEquiv.tensor_id_left
  rightUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    simp
    apply Quotient.sound
    simp
    apply HomEquiv.tensor_id_right
  pentagon W X Y Z := by
    simp
    -- can we rewrite the right thingy using eqToHom_awesome ?
    -- nope. This is b/c that only works on X ⟶ Y ≫ Y ⟶ Z, not X Y Z
    apply Quotient.sound
    symm
    trans
    · apply id_comp_id
    · symm
      trans
      · apply comp
        · apply id_tensor_id
        · apply comp
          · rfl
          · apply id_tensor_id
      · trans
        · apply comp
          · rfl
          · apply id_comp_id
        · apply id_comp_id
  triangle X Y := by
    simp
    apply Quotient.sound
    trans
    · apply comp
      · rfl
      · apply id_tensor_id
    · trans
      · apply id_comp_id
      · symm
        apply id_tensor_id
