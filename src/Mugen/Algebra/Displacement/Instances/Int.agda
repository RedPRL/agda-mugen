module Mugen.Algebra.Displacement.Instances.Int where

open import Data.Int
open import Order.Instances.Int

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Order.Instances.Int

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
  mk .make-displacement.idl = +ℤ-zerol _
  mk .make-displacement.idr = +ℤ-zeror _
  mk .make-displacement.associative {x} {y} {z} = +ℤ-assoc x y z
  mk .make-displacement.left-strict-invariant {x} {y} {z} p =
    +ℤ-mono-l x y z p , +ℤ-injectiver x y z

--------------------------------------------------------------------------------
-- Ordered Monoid

Int-has-ordered-monoid : has-ordered-monoid Int-displacement
Int-has-ordered-monoid =
  right-invariant→has-ordered-monoid Int-displacement $ +ℤ-mono-r _ _ _
