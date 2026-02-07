-- really easy, or should be: decide equivalence over the free category
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

#check Category

-- OKAY, I understand now. Mathlib/CategoryTheory/Monoidal/Free/Basic.lean
-- does all the ugly, stupid, silly stuff: here's our representation, and
-- here's when it's equivalent to other stuff. Ah, turns out that's a monoidal
-- category, go figure.
