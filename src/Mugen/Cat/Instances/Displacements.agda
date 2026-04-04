module Mugen.Cat.Instances.Displacements where

open import Cat.Displayed.Base
open import Cat.Displayed.Total

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Cat.Instances.StrictOrders

--------------------------------------------------------------------------------
-- The Category of Displacement Algebras

Displacements-over : ∀ (o r : Level) → Displayed (Strict-orders o r) (o ⊔ lsuc r) o
Displacements-over o r = with-thin-display record where
  Ob[_] A = Displacement-on A
  Hom[_] f X Y = is-displacement-hom X Y f
  id' {a = A} {x = X} = id-is-displacement-hom {A = A} X
  _∘'_ {a = A} {b = B} {c = C} {x = X} {y = Y} {z = Z} {f = f} {g = g} =
    ∘-is-displacement-hom {A = A} {B = B} {C = C} {X = X} {Y = Y} {Z = Z} {f = f} {g = g}

Displacements : ∀ o r → Precategory (lsuc o ⊔ lsuc r) (o ⊔ r)
Displacements o r = ∫ (Displacements-over o r)
