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

Int+ : Displacement-algebra lzero lzero
Int+ = to-displacement-algebra mk where
  mk : make-displacement-algebra ℤ-Strict-order
  mk .make-displacement-algebra.ε = pos 0
  mk .make-displacement-algebra._⊗_ = _+ℤ_
  mk .make-displacement-algebra.idl = +ℤ-idl _
  mk .make-displacement-algebra.idr = +ℤ-idr _
  mk .make-displacement-algebra.associative {x} {y} {z} = +ℤ-associative x y z
  mk .make-displacement-algebra.left-invariant {x} {y} {z} = +ℤ-left-invariant x y z

--------------------------------------------------------------------------------
-- Ordered Monoid

Int+-has-ordered-monoid : has-ordered-monoid ℤ-Displacement
Int+-has-ordered-monoid =
  right-invariant→has-ordered-monoid ℤ-Displacement
    (+ℤ-weak-right-invariant _ _ _)


--------------------------------------------------------------------------------
-- Joins

Int+-has-joins : has-joins Int+
Int+-has-joins .has-joins.join = maxℤ
Int+-has-joins .has-joins.joinl {x} {y} = ≤ℤ-strengthen x (maxℤ x y) (maxℤ-≤l x y)
Int+-has-joins .has-joins.joinr {x} {y} = ≤ℤ-strengthen y (maxℤ x y) (maxℤ-≤r x y)
Int+-has-joins .has-joins.universal {x} {y} {z} x≤z y≤z =
  ≤ℤ-strengthen (maxℤ x y) z (maxℤ-is-lub x y z (to-≤ℤ x z x≤z) (to-≤ℤ y z y≤z))
