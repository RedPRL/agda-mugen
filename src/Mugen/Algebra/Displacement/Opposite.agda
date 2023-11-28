module Mugen.Algebra.Displacement.Opposite where

open import Mugen.Prelude
open import Mugen.Order.Poset
open import Mugen.Order.Opposite
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid

--------------------------------------------------------------------------------
-- The Opposite Displacement Algebra
-- Section 3.3.8
--
-- Given a displacement algebra '𝒟', we can define another displacement
-- algebra with the same monoid structure, but with a reverse order.

_^opᵈ : ∀ {o r} → Displacement-algebra o r → Displacement-algebra o r
𝒟 ^opᵈ = to-displacement-algebra displacement where
  open Displacement-algebra 𝒟

  displacement : make-displacement-algebra (poset ^opˢ)
  displacement .make-displacement-algebra.ε = ε
  displacement .make-displacement-algebra._⊗_ = _⊗_
  displacement .make-displacement-algebra.idl = idl
  displacement .make-displacement-algebra.idr = idr
  displacement .make-displacement-algebra.associative = associative
  displacement .make-displacement-algebra.left-strict-invariant p =
    left-invariant p , λ q → sym $ injr-on-related p (sym q)

module OpProperties {o r} {𝒟 : Displacement-algebra o r} where
  open Displacement-algebra 𝒟

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  op-has-ordered-monoid : has-ordered-monoid 𝒟 → has-ordered-monoid (𝒟 ^opᵈ)
  op-has-ordered-monoid 𝒟-ordered-monoid = right-invariant→has-ordered-monoid (𝒟 ^opᵈ) right-invariant
    where
      open is-ordered-monoid 𝒟-ordered-monoid
