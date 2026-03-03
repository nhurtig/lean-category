import Mathlib
import LeanCategory.CatMorphisms

universe u

namespace KnitCategory

open scoped KnitCategory
open BraidGroupoid
open CategoryTheory

@[grind]
inductive HomEquiv {α : Type u} : ∀ {X Y : MonoidalWord α}, (X ⟶ᵏ Y) → (X ⟶ᵏ Y) → Prop
    | refl {X Y} (f : X ⟶ᵏ Y) : HomEquiv f f
    | merge_braid {X Y} (f : X ⟶ Y) (g : Y ⟶ Z) : HomEquiv (Hom.comp (.braid f) (.braid g)) (.braid (f ≫ g))
    | swap (L₁ : Layer X Y) : HomEquiv ((Hom.layer L₁).comp ((Hom.braid (𝟙 Y)).comp (.layer L₂))) ((Hom.layer L₁).comp ((Hom.braid (𝟙 Y)).comp (.layer L₂)))
    -- | layer : sorry
    | comp {X Y Z} {f f' : X ⟶ᵏ Y} {g g' : Y ⟶ᵏ Z} :
        HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
    | comp_id {X Y} (f : X ⟶ᵏ Y) : HomEquiv (f.comp (Hom.id _)) f
    | id_comp {X Y} (f : X ⟶ᵏ Y) : HomEquiv ((Hom.id _).comp f) f
    | assoc {X Y U V : MonoidalWord α} (f : X ⟶ᵏ U) (g : U ⟶ᵏ V) (h : V ⟶ᵏ Y) :
        HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
    | symm {X Y} {f g : X ⟶ᵏ Y} : HomEquiv f g → HomEquiv g f
    | trans {X Y} {f g h : X ⟶ᵏ Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h

@[refl]
def HomEquiv.refl' {α : Type u} {X Y : MonoidalWord α} (f : X ⟶ᵏ Y) : HomEquiv f f := .refl f

@[symm]
def HomEquiv.symm' {α : Type u} {X Y : MonoidalWord α} {f g : X ⟶ᵏ Y}
    (h : HomEquiv f g) : HomEquiv g f := .symm h

instance : Trans (HomEquiv (α := α) (X := X) (Y := Y)) (HomEquiv) (HomEquiv) where
    trans := .trans

instance : Equivalence (HomEquiv (α := α) (X := X) (Y := Y)) where
    refl := .refl
    symm := .symm
    trans := .trans

instance : HasEquiv (X ⟶ᵏ Y) where
    Equiv := HomEquiv

end KnitCategory
