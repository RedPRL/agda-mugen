module Mugen.Order.Instances.NonPositive where

open import Data.Nat

open import Mugen.Prelude

open import Mugen.Order.StrictOrder
open import Mugen.Order.Lattice
open import Mugen.Order.Instances.Nat
open import Mugen.Order.Instances.Int
open import Mugen.Order.Instances.Opposite

open import Mugen.Data.Int

--------------------------------------------------------------------------------
-- The Non-Positive Integers
-- Section 3.3.1
--
-- These have a terse definition as the opposite order of Nat+,
-- so we just use that.

NonPositive : Poset lzero lzero
NonPositive = Opposite Nat-poset

--------------------------------------------------------------------------------
-- Inclusion to Int-poset

NonPositive→Int : Strictly-monotone NonPositive Int-poset
NonPositive→Int .Strictly-monotone.hom x = - x
NonPositive→Int .Strictly-monotone.pres-< p .fst = negate-anti-mono _ _ p
NonPositive→Int .Strictly-monotone.pres-< p .snd = negate-injective _ _

abstract
  NonPositive→Int-is-full-subposet : is-full-subposet NonPositive→Int
  NonPositive→Int-is-full-subposet .is-full-subposet.injective = negate-injective _ _
  NonPositive→Int-is-full-subposet .is-full-subposet.full {_} {zero} _ = 0≤x
  NonPositive→Int-is-full-subposet .is-full-subposet.full {zero} {suc _} ()
  NonPositive→Int-is-full-subposet .is-full-subposet.full {suc _} {suc _} p = s≤s p

--------------------------------------------------------------------------------
-- Joins

NonPositive-has-joins : has-joins NonPositive
NonPositive-has-joins .has-joins.join = min
NonPositive-has-joins .has-joins.joinl {x} {y} = min-≤l x y
NonPositive-has-joins .has-joins.joinr {x} {y} = min-≤r x y
NonPositive-has-joins .has-joins.universal {x} {y} {z} = min-is-glb x y z

abstract
  NonPositive→Int-is-full-subsemilattice : is-full-subsemilattice NonPositive-has-joins Int-has-joins NonPositive→Int
  NonPositive→Int-is-full-subsemilattice .is-full-subsemilattice.has-is-full-subposet = NonPositive→Int-is-full-subposet
  NonPositive→Int-is-full-subsemilattice .is-full-subsemilattice.pres-join = negate-min _ _
