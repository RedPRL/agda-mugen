module Mugen.Algebra.Displacement.NonPositive where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Int
open import Mugen.Algebra.Displacement.Nat
open import Mugen.Algebra.Displacement.Opposite

open import Mugen.Data.Int
open import Mugen.Data.Nat

--------------------------------------------------------------------------------
-- The Non-Positive Integers
-- These have a terse definition as the opposite order of Nat+

NonPositive+ : DisplacementAlgebra lzero lzero
NonPositive+ = Op Nat+

open Op Nat+

--------------------------------------------------------------------------------
-- The non-positive integers are a subalgebra of the integers.

NonPositive+⊆Int+ : is-displacement-subalgebra NonPositive+ Int+
NonPositive+⊆Int+ .is-displacement-subalgebra.into ⟨$⟩ x = - x
NonPositive+⊆Int+ .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-ε = refl
NonPositive+⊆Int+ .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-⊗ = +ℤ-negate
NonPositive+⊆Int+ .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.strictly-mono {x} {y} = negate-anti-mono y x
NonPositive+⊆Int+ .is-displacement-subalgebra.inj = negate-inj _ _

non-positive-+-has-joins : has-joins NonPositive+
non-positive-+-has-joins .has-joins.join = min
non-positive-+-has-joins .has-joins.joinl {x} {y} =
  from-op≤ $
  ≤-strengthen (min x y) x $
  min-≤l x y
non-positive-+-has-joins .has-joins.joinr {x} {y} =
  from-op≤ $
  ≤-strengthen (min x y) y $
  min-≤r x y
non-positive-+-has-joins .has-joins.universal {x} {y} {z} z≤x z≤y =
  from-op≤ $
  ≤-strengthen z (min x y) $
  min-is-glb x y z
    (to-≤ z x (to-op≤ z≤x))
    (to-≤ z y (to-op≤ z≤y))
