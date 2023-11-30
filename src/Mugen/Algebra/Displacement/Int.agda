module Mugen.Algebra.Displacement.Int where

open import Data.Int.Inductive

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
  mk .make-displacement-algebra.left-strict-invariant {x} {y} {z} p =
    +ℤ-left-invariant x y z p , +ℤ-injr x y z

--------------------------------------------------------------------------------
-- Ordered Monoid

Int+-has-ordered-monoid : has-ordered-monoid Int+
Int+-has-ordered-monoid =
  right-invariant→has-ordered-monoid Int+
    (+ℤ-right-invariant _ _ _)

--------------------------------------------------------------------------------
-- Joins

Int+-has-joins : has-joins Int+
Int+-has-joins .has-joins.join = maxℤ
Int+-has-joins .has-joins.joinl {x} {y} = maxℤ-≤l x y
Int+-has-joins .has-joins.joinr {x} {y} = maxℤ-≤r x y
Int+-has-joins .has-joins.universal {x} {y} {z} = maxℤ-is-lub x y z
