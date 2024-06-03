module Mugen.Cat.HierarchyTheory where

import Cat.Reasoning as Cat
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

Hierarchy-theory : ∀ o r → Type (lsuc o ⊔ lsuc r)
Hierarchy-theory o r = Monad (Strict-orders o r)

-- And they form a category

Hierarchy-theories : ∀ o r → Precategory (lsuc (o ⊔ r)) (lsuc (o ⊔ r))
Hierarchy-theories o r = Monads (Strict-orders o r)

--------------------------------------------------------------------------------
-- Misc. Definitions

preserves-monos : ∀ {o r} (H : Hierarchy-theory o r) → Type (lsuc o ⊔ lsuc r)
preserves-monos {o} {r} H = ∀ {X Y} → (f : Hom X Y) → is-monic f → is-monic (H.M₁ f)
  where
    module H = Monad H
    open Cat (Strict-orders o r)
