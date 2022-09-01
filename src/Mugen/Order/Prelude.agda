module Mugen.Order.Prelude where

open import Mugen.Prelude

open import Relation.Order using (is-preorder; is-partial-order) public

--------------------------------------------------------------------------------
-- Posets

record Poset-on {o} (r : Level) (A : Type o) : Type (o ⊔ lsuc r) where
  field
    _≤_ : A → A → Type r
    has-is-partial-order : is-partial-order _≤_

Poset : ∀ o r → Type (lsuc o ⊔ lsuc r)
Poset o r = SetStructure (Poset-on {o} r)

module Poset {o r} (P : Poset o r) where
  open Poset-on (structure P)
