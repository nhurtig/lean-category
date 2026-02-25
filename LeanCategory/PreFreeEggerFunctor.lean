import LeanCategory.PreFreeEgger

variable {P Q : Type u}
variable [StarMonoid P] [Quiver.{v} P] [StarMonoid Q] [Quiver.{v} Q]

#check MonoidHom

variable (m : P →⋆* Q)
variable (M : {X Y : P} → (X ⟶ Y) → (m X ⟶ m Y))

#check Quiver

open CategoryTheory

/- #synth Category (S P) -/
/- #check S P ⥤ S Q -/

#check Hom
abbrev PHom := @Hom P
abbrev QHom := @Hom Q
#check QHom

#synth Quiver (S P)

def Hom.myfunct : PHom X Y → QHom (m X) (m Y)
  | .of f => .of <| M f
  | .id X => .id <| m X
  | .comp f g => .comp f.myfunct g.myfunct
  -- TODO: get the eqToHom working. Not working b/c there's no CategoryStruct instance for raw Hom; just for Hom (S V)
  -- alternative: just define Hom.myfunct' below directly on the (S V) structure
  | .tensor f g => .comp (.comp (eqToHom sorry) (.tensor f.myfunct g.myfunct)) _
  | _ => sorry

#synth Quiver (S P)
#check preHom
abbrev PHom' := @Hom (S P)
abbrev QHom' := @Hom (S Q)

#check FreeMonoidalCategory
-- maybe try lifting m to a S-hom?
variable (m' : (S P) →⋆* (S Q))
def Hom.myfunct'arst {X Y : S P} : (X ⟶ Y) → ((m' X) ⟶ (m' Y))
  /- | .id _ => sorry -/
  /- | .of f => .of <| M f -/
  /- | .id X => .id <| m X -/
  | .comp f g => .comp (Hom.myfunct'arst m' f) (Hom.myfunct'arst m' g)
  /- | .tensor f g => .comp (.comp (eqToHom sorry) (.tensor f.myfunct g.myfunct)) _ -/
  /- | _ => sorry -/

def Hom.myfunctS {X Y : S P} : (X ⟶ Y) → ((S.mk <| m X.val) ⟶  ⟨m Y.val⟩) := by
  simp [Quiver.Hom]
  exact Hom.myfunct m M

