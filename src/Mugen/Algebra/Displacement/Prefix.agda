module Mugen.Algebra.Displacement.Prefix where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Data.List

open import Mugen.Algebra.Displacement
open import Mugen.Order.Prefix
open import Mugen.Order.StrictOrder

--------------------------------------------------------------------------------
-- Prefix Displacements
--
-- Given a set 'A', we can define a displacement algebra on 'List A',
-- where 'xs ≤ ys' if 'xs' is a prefix of 'ys'.
--
-- Most of the order theoretic properties come from 'Mugen.Order.Prefix'.

module Pre {ℓ} {A : Type ℓ} (aset : is-set A) where

  --------------------------------------------------------------------------------
  -- Left Invariance

  ++-left-invariant : ∀ (xs ys zs : List A) → Prefix A ys zs → Prefix A (xs ++ ys) (xs ++ zs)
  ++-left-invariant [] ys zs ys<zs = ys<zs
  ++-left-invariant (x ∷ xs) ys zs ys<zs = ptail refl (++-left-invariant xs ys zs ys<zs)

  prefix-is-displacement-algebra : is-displacement-algebra (Prefix A) [] _++_
  prefix-is-displacement-algebra .is-displacement-algebra.has-monoid = ++-is-monoid aset
  prefix-is-displacement-algebra .is-displacement-algebra.has-strict-order = prefix-is-strict-order aset
  prefix-is-displacement-algebra .is-displacement-algebra.left-invariant {x} {y} {z} = ++-left-invariant x y z

Pre : ∀ {o} → Set o → DisplacementAlgebra o o
⌞ Pre A ⌟ = List ∣ A ∣
Pre A .structure .DisplacementAlgebra-on._<_ = Prefix ∣ A ∣
Pre A .structure .DisplacementAlgebra-on.ε = []
Pre A .structure .DisplacementAlgebra-on._⊗_ = _++_
Pre A .structure .DisplacementAlgebra-on.has-displacement-algebra = Pre.prefix-is-displacement-algebra (is-tr A)
⌞ Pre A ⌟-set = ListPath.List-is-hlevel 0 (is-tr A)

module PreProperties {ℓ} {A : Set ℓ} where

  --------------------------------------------------------------------------------
  -- Bottoms

  prefix-has-bottom : has-bottom (Pre A)
  prefix-has-bottom .has-bottom.bot = []
  prefix-has-bottom .has-bottom.is-bottom [] = inl refl
  prefix-has-bottom .has-bottom.is-bottom (_ ∷ _) = inr phead
