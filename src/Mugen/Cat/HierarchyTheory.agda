module Mugen.Cat.HierarchyTheory where

open import Cat.Diagram.Monad
import Cat.Reasoning as Cat

open import Mugen.Prelude
open import Mugen.Cat.StrictOrders
open import Mugen.Order.StrictOrder

--------------------------------------------------------------------------------
-- Heirarchy Theories
--
-- A heirarchy theory is defined to be a monad on the category of strict orders.
-- We also define the McBride Heirarchy Theory.

Hierarchy-theory : ∀ o r → Type (lsuc o ⊔ lsuc r)
Hierarchy-theory o r = Monad (Strict-orders o r)

--------------------------------------------------------------------------------
-- Misc. Definitions

preserves-monos : ∀ {o r} (H : Hierarchy-theory o r) → Type (lsuc o ⊔ lsuc r)
preserves-monos {o} {r} H = ∀ {X Y} → (f : Hom X Y) → is-monic f → is-monic (H.M₁ f)
  where
    module H = Monad H
    open Cat (Strict-orders o r)
