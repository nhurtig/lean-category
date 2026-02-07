import Mathlib
import LeanCategory.MonoidalWord
import LeanCategory.Instances

universe u

namespace BraidGroupoid

open CategoryTheory
open scoped MonoidalCategory
open scoped BraidGroupoid

-- The composition of a hom with its inverse is the identity up to HomEquiv
@[simp, grind]
lemma HomEquiv.comp_inv {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵇ Y) :
    HomEquiv (f.comp f.inv) (Hom.id X) := by
  induction f
  any_goals (constructor; done)
  case comp f g ihf ihg =>
    simp
    calc
      HomEquiv _ ((f.comp (g.comp (g.inv))).comp f.inv) := by
        grind [assoc]
      HomEquiv _ ((f.comp (Hom.id _)).comp f.inv) := by
        apply HomEquiv.comp
        · apply HomEquiv.comp
          · apply HomEquiv.refl
          · assumption
        · apply HomEquiv.refl
      HomEquiv _ (f.comp f.inv) := by
        apply HomEquiv.comp
        · exact comp_id f
        · apply HomEquiv.refl
      HomEquiv _ (Hom.id _) := by assumption
  case tensor f g ihf ihg =>
    calc
      HomEquiv _ _ := by
        apply tensorHom_comp_tensorHom
      HomEquiv _ _ := by
        apply tensor ihf ihg
      HomEquiv _ _ := by
        apply id_tensorHom_id

-- The inverse of an inverse is the original hom, up to HomEquiv
@[simp, grind]
lemma HomEquiv.inv_inv {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵇ Y) : HomEquiv f.inv.inv f := by
  induction f
  any_goals rfl
  case comp ihf ihg =>
    apply comp ihf ihg
  case tensor ihf ihg =>
    apply tensor ihf ihg

-- The composition of the inverse of a hom with itself is the identity up to HomEquiv
@[simp, grind]
lemma HomEquiv.inv_comp {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵇ Y) :
    HomEquiv (f.inv.comp f) (Hom.id Y) := by
  calc
    HomEquiv (f.inv.comp f) _ := by
      symm
      apply comp_id
    HomEquiv _ _ := by
      apply comp
      · rfl
      · symm
        apply HomEquiv.comp_inv f.inv
    HomEquiv _ (f.inv.comp ((f.comp f.inv).comp f.inv.inv)) := by
      grind [assoc]
    HomEquiv _ _ := by
      apply comp
      · rfl
      · apply comp
        · apply HomEquiv.comp_inv f
        · rfl
    HomEquiv _ _ := by
      apply comp
      · rfl
      · apply id_comp
    HomEquiv _ _ := by
      apply HomEquiv.comp_inv f.inv

-- If two homs are equivalent, then their inverses are also equivalent
@[simp, grind]
lemma HomEquiv.inv {α : Type u} {X Y : MonoidalWord α} {f g : X ⟶ᵇ Y} : HomEquiv f g → HomEquiv f.inv g.inv := by
  intro h
  calc
    HomEquiv f.inv _ := by
      symm -- todo grep for symm/rfl
      apply comp_id
    HomEquiv _ _ := by
      apply comp
      · rfl
      · symm
        apply comp_inv g
    HomEquiv _ _ := by
      apply comp
      · rfl
      · apply comp
        · symm
          exact h
        · rfl
    HomEquiv _ ((f.inv.comp f).comp g.inv) := by
      grind [assoc]
    HomEquiv _ _ := by
      apply comp
      · apply inv_comp
      · rfl
    HomEquiv _ _ := by
      apply id_comp

end BraidGroupoid

/-

/-- Project braid relations along the inverse. -/
def HomEquiv.inv {α β : Type u} {X Y : MonoidalWord α}
        {f g : X ⟶ᵇ Y} : HomEquiv f g → HomEquiv f.inv g.inv := by
    intro h
    induction h with
    | refl f => exact refl _
    | symm h ih => exact symm ih
    | trans hfg hgh ihfg ihgh => exact trans ihfg ihgh
    | comp hf hg ihf ihg => exact comp ihg ihf
    | whiskerLeft X f f' hf ih => exact whiskerLeft _ _ _ ih
    | whiskerRight f f' X hf ih => exact whiskerRight _ _ _ ih
    | tensor hf hg ihf ihg => exact tensor ihf ihg
    | tensorHom_def f g =>
        apply symm
        calc HomEquiv ((Hom.whiskerLeft _ g.inv).comp (f.inv.whiskerRight _))
                      (((Hom.id _).tensor g.inv).comp (f.inv.tensor (Hom.id _))) := by
                apply comp
                · apply symm
                  calc HomEquiv _ _ := by
                        apply tensorHom_def
                       HomEquiv _ ((Hom.id (_)).comp (Hom.whiskerLeft _ g.inv)) := by
                        grind
                       HomEquiv _ _ := by
                        grind
                · apply symm
                  calc HomEquiv _ _ := by
                        apply tensorHom_def
                       HomEquiv _ ((f.inv.whiskerRight _).comp (Hom.id _)) := by
                        grind
                       HomEquiv _ _ := by
                        grind
              HomEquiv _ _ := by
                apply tensorHom_comp_tensorHom
              HomEquiv _ _ := by
                apply tensor
                · grind
                · grind
    | comp_id f => exact id_comp f.inv
    | id_comp f => exact comp_id f.inv
    | assoc f g h =>
        apply symm
        apply assoc
    | id_tensorHom_id => exact id_tensorHom_id
    | tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ => apply tensorHom_comp_tensorHom
    | whiskerLeft_id X Y => apply whiskerLeft_id
    | id_whiskerRight X Y => apply id_whiskerRight
    | α_comp_inv => exact α_comp_inv
    | α_inv_comp => exact α_inv_comp
    | α_naturality f₁ f₂ f₃ =>
        calc HomEquiv ((Hom.α_inv _ _ _).comp ((f₁.inv.tensor f₂.inv).tensor f₃.inv)) _ := by
                apply symm
                apply comp_id
             HomEquiv _ _ := by
                apply comp
                · apply refl
                · apply symm
                  apply α_comp_inv
             HomEquiv _ (((Hom.α_inv _ _ _).comp (((f₁.inv.tensor f₂.inv).tensor f₃.inv).comp (Hom.α_hom _ _ _))).comp (Hom.α_inv _ _ _)) := by
                grind [assoc]
             HomEquiv _ _ := by
                apply comp
                · apply comp
                  · apply refl
                  · apply α_naturality
                · apply refl
             HomEquiv _ (((Hom.α_inv _ _ _).comp (Hom.α_hom _ _ _)).comp ((f₁.inv.tensor (f₂.inv.tensor f₃.inv)).comp (Hom.α_inv _ _ _))) := by
                grind [assoc]
             HomEquiv _ _ := by
                apply comp
                · apply α_inv_comp
                · apply refl
             HomEquiv _ _ := by
                apply id_comp
    | ρ_comp_inv => exact ρ_comp_inv
    | ρ_inv_comp => exact ρ_inv_comp
    | ρ_naturality f =>
        calc HomEquiv ((Hom.ρ_inv _).comp (f.inv.whiskerRight .unit)) _ := by
                apply symm
                apply comp_id
             HomEquiv _ _ := by
                apply comp
                · apply refl
                · apply symm
                  apply ρ_comp_inv
             HomEquiv _ (((Hom.ρ_inv _).comp ((f.inv.whiskerRight .unit).comp (Hom.ρ_hom _))).comp (Hom.ρ_inv _)) := by
                grind [assoc]
             HomEquiv _ _ := by
                apply comp
                · apply comp
                  · apply refl
                  · apply ρ_naturality
                · apply refl
             HomEquiv _ (((Hom.ρ_inv _).comp (Hom.ρ_hom _)).comp (f.inv.comp (Hom.ρ_inv _))) := by
                grind [assoc]
             HomEquiv _ _ := by
                apply comp
                · apply ρ_inv_comp
                · apply refl
             HomEquiv _ _ := by
                apply id_comp
    | l_comp_inv => exact l_comp_inv
    | l_inv_comp => exact l_inv_comp
    | l_naturality f =>
        calc HomEquiv ((Hom.l_inv _).comp (f.inv.whiskerLeft .unit)) _ := by
                apply symm
                apply comp_id
             HomEquiv _ _ := by
                apply comp
                · apply refl
                · apply symm
                  apply l_comp_inv
             HomEquiv _ (((Hom.l_inv _).comp ((f.inv.whiskerLeft .unit).comp (Hom.l_hom _))).comp (Hom.l_inv _)) := by
                grind [assoc]
             HomEquiv _ _ := by
                apply comp
                · apply comp
                  · apply refl
                  · apply l_naturality
                · apply refl
             HomEquiv _ (((Hom.l_inv _).comp (Hom.l_hom _)).comp (f.inv.comp (Hom.l_inv _))) := by
                grind [assoc]
             HomEquiv _ _ := by
                apply comp
                · apply l_inv_comp
                · apply refl
             HomEquiv _ _ := by
                apply id_comp
    | pentagon =>
        simp
        sorry
    | triangle => exact triangle
    | σ_inv_left => exact σ_inv_left
    | σ_inv_right => exact σ_inv_right
    | braiding_naturality_right f =>
        exact braiding_naturality_right (f.project map)
    | braiding_naturality_left f Z =>
        exact braiding_naturality_left (f.project map) (Z.project map)
    | hexagon_forward => exact hexagon_forward
    | hexagon_reverse => exact hexagon_reverse

/--
The projection functor induced by a partial label map.
-/
@[simp]
def projectFunctor {α β : Type u} (map : α → Option β) : MonoidalWord α ⥤ MonoidalWord β where
    obj X := X.project map
    map {X Y} f :=
        Quotient.lift (fun g => ⟦g.project map⟧) (by
            intro g h hg
            exact Quotient.sound (HomEquiv.project map hg)) f
    map_comp {X Y Z} := by
        rintro ⟨f⟩ ⟨g⟩
        rfl

/-- The projection functor is lax monoidal with identity unit and tensorator. -/
@[simp]
instance projectFunctor_laxMonoidal {α β : Type u} (map : α → Option β) :
        (projectFunctor map).LaxMonoidal where
    ε := 𝟙 _
    μ _ _ := 𝟙 _
    μ_natural_left := by
        rintro X Y ⟨f⟩ X'
        cat_disch
    μ_natural_right := by
        rintro X Y X' ⟨f⟩
        cat_disch

/-- The projection functor preserves braiding strictly. -/
instance projectFunctor_laxBraided {α β : Type u} (map : α → Option β) :
        (projectFunctor map).LaxBraided where

-/

open CategoryTheory

namespace BraidGroupoid

instance (α : Type u) : Groupoid (MonoidalWord α) where
    inv {X Y} f := Quotient.lift (fun g => ⟦g.inv⟧) (by
        intro f g h
        apply Quotient.sound
        apply HomEquiv.inv h) f
    comp_inv f := by
      induction f using Quotient.inductionOn
      apply Quotient.sound
      apply HomEquiv.comp_inv
    inv_comp  f := by
      induction f using Quotient.inductionOn
      apply Quotient.sound
      apply HomEquiv.inv_comp

/-- A shorthand class for braided monoidal groupoids. -/
class BraidedGroupoid (C : Type u) [Category C] [MonoidalCategory C]
    [BraidedCategory C] [Groupoid C]

/-- The free braided monoidal groupoid on a type of labels. -/
instance (α : Type u) : BraidedGroupoid (MonoidalWord α) where

end BraidGroupoid
