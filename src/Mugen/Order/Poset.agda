module Mugen.Order.Poset where

open import Mugen.Prelude

open import Relation.Order using (is-preorder; is-partial-order) public

--------------------------------------------------------------------------------
-- Preorders

record Preorder-on {o} (r : Level) (A : Type o) : Type (o ⊔ lsuc r) where
  field
    _≤_ : A → A → Type r
    has-is-preorder : is-preorder _≤_

  open is-preorder has-is-preorder public

Preorder : ∀ o r → Type (lsuc o ⊔ lsuc r)
Preorder o r = SetStructure (Preorder-on {o} r)

module Preorder {o r} (P : Preorder o r) where
  open Preorder-on (structure P) public

--------------------------------------------------------------------------------
-- Posets

record Poset-on {o} (r : Level) (A : Type o) : Type (o ⊔ lsuc r) where
  field
    _≤_ : A → A → Type r
    has-is-partial-order : is-partial-order _≤_

  open is-partial-order has-is-partial-order public

Poset : ∀ o r → Type (lsuc o ⊔ lsuc r)
Poset o r = SetStructure (Poset-on {o} r)

module Poset {o r} (P : Poset o r) where
  open Poset-on (structure P) public

