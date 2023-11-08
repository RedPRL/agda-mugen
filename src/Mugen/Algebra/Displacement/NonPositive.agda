module Mugen.Algebra.Displacement.NonPositive where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Int
open import Mugen.Algebra.Displacement.Nat
open import Mugen.Algebra.Displacement.Opposite

open import Mugen.Order.Opposite

open import Mugen.Data.Int
open import Mugen.Data.Nat

--------------------------------------------------------------------------------
-- The Non-Positive Integers
-- Section 3.3.1
--
-- These have a terse definition as the opposite order of Nat+,
-- so we just use that.

NonPositive+ : Displacement-algebra lzero lzero
NonPositive+ = Nat+ ^opᵈ

--------------------------------------------------------------------------------
-- Joins

non-positive-+-has-joins : has-joins NonPositive+
non-positive-+-has-joins .has-joins.join = min
non-positive-+-has-joins .has-joins.joinl {x} {y} =
  from-op≤ Nat< $
  ≤-strengthen (min x y) x $
  min-≤l x y
non-positive-+-has-joins .has-joins.joinr {x} {y} =
  from-op≤ Nat< $
  ≤-strengthen (min x y) y $
  min-≤r x y
non-positive-+-has-joins .has-joins.universal {x} {y} {z} z≤x z≤y =
  from-op≤ Nat< $
  ≤-strengthen z (min x y) $
  min-is-glb x y z
    (Equiv.from ≤≃non-strict (to-op≤ Nat< z≤x))
    (Equiv.from ≤≃non-strict (to-op≤ Nat< z≤y))

--------------------------------------------------------------------------------
-- Subalgebra

NonPositive+⊆Int+ : is-displacement-subalgebra NonPositive+ Int+
NonPositive+⊆Int+ = to-displacement-subalgebra subalg where
  subalg : make-displacement-subalgebra NonPositive+ Int+
  subalg .make-displacement-subalgebra.into x = - x
  subalg .make-displacement-subalgebra.pres-ε = refl
  subalg .make-displacement-subalgebra.pres-⊗ = +ℤ-negate 
  subalg .make-displacement-subalgebra.strictly-mono x y = negate-anti-mono y x
  subalg .make-displacement-subalgebra.inj = negate-inj _ _

NonPositive-is-subsemilattice : is-displacement-subsemilattice non-positive-+-has-joins Int+-has-joins
NonPositive-is-subsemilattice .is-displacement-subsemilattice.has-displacement-subalgebra = NonPositive+⊆Int+
NonPositive-is-subsemilattice .is-displacement-subsemilattice.pres-joins zero zero = refl
NonPositive-is-subsemilattice .is-displacement-subsemilattice.pres-joins zero (suc y) = refl
NonPositive-is-subsemilattice .is-displacement-subsemilattice.pres-joins (suc x) zero = refl
NonPositive-is-subsemilattice .is-displacement-subsemilattice.pres-joins (suc x) (suc y) = refl
