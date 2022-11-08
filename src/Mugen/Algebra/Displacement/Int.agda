module Mugen.Algebra.Displacement.Int where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement

open import Mugen.Data.Int

--------------------------------------------------------------------------------
-- Integers
-- Section 3.3.1
--
-- This is the evident displacement algebra on the integers.
-- All of the interesting properties are proved in 'Mugen.Data.Int';
-- this module serves only to bundle them together.

+ℤ-is-displacement-algebra : is-displacement-algebra _<ℤ_ 0ℤ _+ℤ_
+ℤ-is-displacement-algebra .is-displacement-algebra.has-monoid = +ℤ-0ℤ-is-monoid
+ℤ-is-displacement-algebra .is-displacement-algebra.has-strict-order = <ℤ-is-strict-order
+ℤ-is-displacement-algebra .is-displacement-algebra.left-invariant {x} = +ℤ-left-invariant x

Int+ : DisplacementAlgebra lzero lzero
⌞ Int+ ⌟ = Int
Int+ .structure .DisplacementAlgebra-on._<_ = _<ℤ_
Int+ .structure .DisplacementAlgebra-on.ε = 0ℤ
Int+ .structure .DisplacementAlgebra-on._⊗_ = _+ℤ_
Int+ .structure .DisplacementAlgebra-on.has-displacement-algebra = +ℤ-is-displacement-algebra
⌞ Int+ ⌟-set = Int-is-set

--------------------------------------------------------------------------------
-- Ordered Monoid

int+-has-ordered-monoid : has-ordered-monoid Int+
int+-has-ordered-monoid = right-invariant→has-ordered-monoid Int+ $ λ {_} {_} {z} →
  +ℤ-weak-right-invariant z

--------------------------------------------------------------------------------
-- Joins

int+-has-joins : has-joins Int+
int+-has-joins .has-joins.join = maxℤ
int+-has-joins .has-joins.joinl {x} {y} = ≤ℤ-strengthen (maxℤ-≤l x y)
int+-has-joins .has-joins.joinr {x} {y} = ≤ℤ-strengthen (maxℤ-≤r x y)
int+-has-joins .has-joins.universal {x} {y} {z} x≤z y≤z =
  ≤ℤ-strengthen (maxℤ-is-lub (to-≤ℤ x≤z) (to-≤ℤ y≤z))
