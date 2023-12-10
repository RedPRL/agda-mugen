module Mugen.Algebra.Displacement.Instances.Nat where

open import Data.Nat

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Subalgebra
open import Mugen.Algebra.Displacement.Instances.Int
open import Mugen.Order.StrictOrder
open import Mugen.Order.Instances.Nat
open import Mugen.Order.Instances.Int

open import Mugen.Data.Int

--------------------------------------------------------------------------------
-- Natural Numbers
-- Section 3.3.1
--
-- This is the evident displacement algebra on natural numbers.
-- All of the interesting algebraic/order theoretic properties are proven in
-- 'Mugen.Data.Nat'; this module is just bundling together those proofs.

Nat-displacement : Displacement-on Nat-poset
Nat-displacement = to-displacement-on mk where
  mk : make-displacement Nat-poset
  mk .make-displacement.ε = 0
  mk .make-displacement._⊗_ = _+_
  mk .make-displacement.idl = refl
  mk .make-displacement.idr = +-zeror _
  mk .make-displacement.associative {x} {y} {z} = +-associative x y z
  mk .make-displacement.left-strict-invariant p =
    +-preserves-≤l _ _ _ p , +-inj _ _ _

--------------------------------------------------------------------------------
-- Ordered Monoid

Nat-has-ordered-monoid : has-ordered-monoid Nat-displacement
Nat-has-ordered-monoid =
  right-invariant→has-ordered-monoid Nat-displacement λ {x} {y} {z} →
  +-preserves-≤r x y z

--------------------------------------------------------------------------------
-- Subdisplacement

Nat→Int-is-full-subdisplacement
  : is-full-subdisplacement Nat-displacement Int-displacement Nat→Int
Nat→Int-is-full-subdisplacement = to-full-subdisplacement mk where
  mk : make-full-subdisplacement Nat-displacement Int-displacement Nat→Int
  mk .make-full-subdisplacement.injective = pos-injective
  mk .make-full-subdisplacement.full p = p
  mk .make-full-subdisplacement.pres-ε = refl
  mk .make-full-subdisplacement.pres-⊗ {x} {y} = +ℤ-pos x y
  mk .make-full-subdisplacement.pres-≤ p = p
