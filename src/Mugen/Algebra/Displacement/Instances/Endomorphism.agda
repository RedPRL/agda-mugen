-- vim: nowrap
module Mugen.Algebra.Displacement.Instances.Endomorphism where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Cat.Diagram.Monad
import Cat.Reasoning as Cat

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Cat.Monad
open import Mugen.Cat.StrictOrders
open import Mugen.Order.StrictOrder
open import Mugen.Order.Instances.Endomorphism
  renaming (Endomorphism to Endomorphism-poset)

import Mugen.Order.Reasoning as Reasoning

private variable
  o r : Level

--------------------------------------------------------------------------------
-- Endomorphism Displacements
-- Section 3.4
--
-- Given a Monad 'H' on the category of strict orders, we can construct a displacement
-- algebra whose carrier set is the set of endomorphisms 'Free H Δ → Free H Δ' between
-- free H-algebras in the Eilenberg-Moore category.
open Algebra-hom

module _ (H : Monad (Strict-orders o r)) (Δ : Poset o r) where
  private
    module H = Monad H
    module EM = Cat (Eilenberg-Moore (Strict-orders o r) H)
    module Endo = Reasoning (Endomorphism-poset H Δ)

    Fᴴ⟨Δ⟩ : Algebra (Strict-orders o r) H
    Fᴴ⟨Δ⟩ = Functor.F₀ (Free (Strict-orders o r) H) Δ

    Endomorphism-type : Type (lsuc o ⊔ lsuc r)
    Endomorphism-type = EM.Hom Fᴴ⟨Δ⟩ Fᴴ⟨Δ⟩

    --------------------------------------------------------------------------------
    -- Left Invariance

    ∘-left-strict-invariant : ∀ (σ δ τ : Endomorphism-type)
      → δ Endo.≤ τ → σ EM.∘ δ Endo.≤[ δ ≡ τ ] σ EM.∘ τ
    ∘-left-strict-invariant σ δ τ (lift δ≤τ) =
      (lift λ α → Strictly-monotone.pres-≤ (σ .morphism) (δ≤τ α)) ,
      λ p → free-algebra-hom-path H $ ext λ α →
      Strictly-monotone.injective-on-related (σ .morphism) (δ≤τ α) (p #ₚ (H.unit.η Δ # α))

  --------------------------------------------------------------------------------
  -- Bundles
  --
  -- We do this with copatterns for performance reasons.

  open Displacement-on

  Endomorphism : Displacement-on (Endomorphism-poset H Δ)
  Endomorphism .ε = EM.id
  Endomorphism ._⊗_ = EM._∘_
  Endomorphism .has-is-displacement .is-displacement.has-is-monoid .has-is-semigroup .has-is-magma .has-is-set = Endo.Ob-is-set
  Endomorphism .has-is-displacement .is-displacement.has-is-monoid .has-is-semigroup .associative = EM.assoc _ _ _
  Endomorphism .has-is-displacement .is-displacement.has-is-monoid .idl = EM.idl _
  Endomorphism .has-is-displacement .is-displacement.has-is-monoid .idr = EM.idr _
  Endomorphism .has-is-displacement .is-displacement.left-strict-invariant {σ} {δ} {τ} = ∘-left-strict-invariant σ δ τ
