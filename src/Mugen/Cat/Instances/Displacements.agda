module Mugen.Cat.Instances.Displacements where

open import Cat.Displayed.Base
open import Cat.Displayed.Total

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Cat.Instances.StrictOrders

--------------------------------------------------------------------------------
-- The Category of Displacement Algebras

Displacements-over : ∀ (o r : Level) → Displayed (Strict-orders o r) (o ⊔ lsuc r) o
Displacements-over o r .Displayed.Ob[_] A = Displacement-on A
Displacements-over o r .Displayed.Hom[_] f X Y = is-displacement-hom X Y f
Displacements-over o r .Displayed.Hom[_]-set f X Y = hlevel 2
Displacements-over o r .Displayed.id' = id-is-displacement-hom _
Displacements-over o r .Displayed._∘'_ = ∘-is-displacement-hom
Displacements-over o r .Displayed.idr' _ = prop!
Displacements-over o r .Displayed.idl' _ = prop!
Displacements-over o r .Displayed.assoc' _ _ _ = prop!

Displacements : ∀ o r → Precategory (lsuc o ⊔ lsuc r) (o ⊔ r)
Displacements o r = ∫ (Displacements-over o r)
