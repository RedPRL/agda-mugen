module Mugen.Algebra.Displacement.Instances.Int where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Data.Int
open import Mugen.Order.Instances.Int

open import Mugen.Data.Int

--------------------------------------------------------------------------------
-- Integers
-- Section 3.3.1
--
-- This is the evident displacement algebra on the integers.
-- All of the interesting properties are proved in 'Mugen.Data.Int';
-- this module serves only to bundle them together.

Int-displacement : Displacement-on Int-poset
Int-displacement = to-displacement-on mk where
  mk : make-displacement Int-poset
  mk .make-displacement.ε = pos 0
  mk .make-displacement._⊗_ = _+ℤ_
  mk .make-displacement.idl = +ℤ-idl _
  mk .make-displacement.idr = +ℤ-idr _
  mk .make-displacement.associative {x} {y} {z} = +ℤ-associative x y z
  mk .make-displacement.left-strict-invariant {x} {y} {z} p =
    +ℤ-left-invariant x y z p , +ℤ-injectiver x y z

--------------------------------------------------------------------------------
-- Ordered Monoid

Int-has-ordered-monoid : has-ordered-monoid Int-displacement
Int-has-ordered-monoid =
  right-invariant→has-ordered-monoid Int-displacement
    (+ℤ-right-invariant _ _ _)
