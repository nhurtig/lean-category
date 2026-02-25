import LeanCategory.PreFreeEggerFunctor
import LeanCategory.FreeEgger

variable {P Q : Type u}
variable [StarMonoid P] [Quiver.{v} P] [StarMonoid Q] [Quiver.{v} Q]

variable (m : P → Q)
variable (M : {X Y : P} → (X ⟶ Y) → (m X ⟶ m Y))

#check Hom.myfunct m M

#check Quiver

open CategoryTheory

#synth Category (S P)
#check S P ⥤ S Q

instance : S P ⥤ S Q where
  obj X := m X.val
  map {X Y} f := Quotient.lift (⟦HomAwesome.myfunctS m M ·⟧) sorry f

