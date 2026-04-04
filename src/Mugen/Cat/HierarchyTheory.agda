module Mugen.Cat.HierarchyTheory where

open import Cat.Diagram.Monad
open import Cat.Instances.Monads

open import Mugen.Prelude
open import Mugen.Cat.Instances.StrictOrders
open import Mugen.Order.StrictOrder

--------------------------------------------------------------------------------
-- Hierarchy Theories
--
-- A hierarchy theory is defined to be a monad on the category of strict orders.
-- We also define the McBride Hierarchy Theory.

Hierarchy-theory-on
  : ∀ {o r}
  → Functor (Strict-orders o r) (Strict-orders o r)
  → Type (lsuc o ⊔ lsuc r)
Hierarchy-theory-on = Monad-on

Hierarchy-theory : ∀ o r → Type (lsuc o ⊔ lsuc r)
Hierarchy-theory o r = Σ[ F ∈ Functor (Strict-orders o r) (Strict-orders o r) ] Hierarchy-theory-on F

-- And they form a category

Hierarchy-theories : ∀ o r → Precategory (lsuc (o ⊔ r)) (lsuc (o ⊔ r))
Hierarchy-theories o r = Monads (Strict-orders o r)
