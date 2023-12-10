module Mugen.Algebra.Displacement.Instances.Opposite where

open import Mugen.Prelude
open import Mugen.Order.Instances.Opposite renaming (Opposite to Opposite-poset)
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid

private variable
  o r : Level

--------------------------------------------------------------------------------
-- The Opposite Displacement Algebra
-- Section 3.3.8
--
-- Given a displacement algebra '𝒟', we can define another displacement
-- algebra with the same monoid structure, but with a reverse order.

Opposite : ∀ {A : Poset o r}
  → Displacement-on A → Displacement-on (Opposite-poset A)
Opposite {A = A} 𝒟 = to-displacement-on displacement where
  open Displacement-on 𝒟

  displacement : make-displacement (Opposite-poset A)
  displacement .make-displacement.ε = ε
  displacement .make-displacement._⊗_ = _⊗_
  displacement .make-displacement.idl = idl
  displacement .make-displacement.idr = idr
  displacement .make-displacement.associative = associative
  displacement .make-displacement.left-strict-invariant p =
    left-invariant p , λ q → sym $ injectiver-on-related p (sym q)

module OpProperties {A : Poset o r} {𝒟 : Displacement-on A} where
  open Displacement-on 𝒟

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  Opposite-has-ordered-monoid : has-ordered-monoid 𝒟 → has-ordered-monoid (Opposite 𝒟)
  Opposite-has-ordered-monoid 𝒟-ordered-monoid =
    right-invariant→has-ordered-monoid (Opposite 𝒟) right-invariant
    where
      open is-ordered-monoid 𝒟-ordered-monoid
