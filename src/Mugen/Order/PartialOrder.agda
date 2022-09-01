module Mugen.Order.PartialOrder where

open import Mugen.Prelude

open import Relation.Order using (is-preorder; is-partial-order) public

private variable
  o r : Level
  A : Type o

--------------------------------------------------------------------------------
-- Partial Orders

record PartialOrder-on {o} (r : Level) (A : Type o) : Type (o ⊔ lsuc r) where
  field
    _≤_ : A → A → Type r
    has-partial-order : is-partial-order _≤_

  open is-partial-order has-partial-order public

PartialOrder : ∀ o r → Type (lsuc o ⊔ lsuc r)
PartialOrder o r = SetStructure (PartialOrder-on {o} r)


module PartialOrder {o r} (A : PartialOrder o r) where
  open PartialOrder-on (structure A) public

_[_≤_] : (A : PartialOrder o r) → ⌞ A ⌟ → ⌞ A ⌟ → Type r
A [ x ≤ y ] = PartialOrder._≤_ A x y
