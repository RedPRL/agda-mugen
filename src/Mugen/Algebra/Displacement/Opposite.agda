module Mugen.Algebra.Displacement.Opposite where

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid

open import Mugen.Order.Opposite
open import Mugen.Order.StrictOrder

--------------------------------------------------------------------------------
-- The Opposite Displacement Algebra
-- Section 3.3.8
--
-- Given a displacement algebra '𝒟', we can define another displacement
-- algebra with the same monoid structure, but with a reverse order.

_^opᵈ : ∀ {o r} → Displacement-algebra o r → Displacement-algebra o r
𝒟 ^opᵈ = to-displacement-algebra displacement where
  open Displacement-algebra 𝒟

  displacement : make-displacement-algebra (strict-order ^opˢ)
  displacement .make-displacement-algebra.ε = ε
  displacement .make-displacement-algebra._⊗_ = _⊗_
  displacement .make-displacement-algebra.idl = idl
  displacement .make-displacement-algebra.idr = idr
  displacement .make-displacement-algebra.associative = associative
  displacement .make-displacement-algebra.left-invariant = left-invariant

module OpProperties {o r} {𝒟 : Displacement-algebra o r} where
  open Displacement-algebra 𝒟

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  op-has-ordered-monoid : has-ordered-monoid 𝒟 → has-ordered-monoid (𝒟 ^opᵈ)
  op-has-ordered-monoid 𝒟-ordered-monoid = right-invariant→has-ordered-monoid (𝒟 ^opᵈ) λ y≤x →
    from-op≤ strict-order (right-invariant (to-op≤ strict-order y≤x))
    where
      open is-ordered-monoid 𝒟-ordered-monoid
