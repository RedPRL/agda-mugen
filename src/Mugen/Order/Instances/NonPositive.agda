module Mugen.Order.Instances.NonPositive where

open import Data.Nat
open import Data.Int
open import Order.Instances.Int

open import Mugen.Prelude

open import Mugen.Order.StrictOrder
open import Mugen.Order.Lattice
open import Mugen.Order.Instances.Nat
open import Mugen.Order.Instances.Int
open import Mugen.Order.Instances.Opposite

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
NonPositive→Int .Strictly-monotone.hom x = negℤ (pos x)
NonPositive→Int .Strictly-monotone.pres-≤[]-equal p .fst = negℤ-anti _ _ (pos≤pos p)
NonPositive→Int .Strictly-monotone.pres-≤[]-equal p .snd q = pos-injective $ negℤ-injective _ _ q

abstract
  NonPositive→Int-is-full-subposet : is-full-subposet NonPositive→Int
  NonPositive→Int-is-full-subposet .is-full-subposet.injective p = pos-injective $ negℤ-injective _ _ p
  NonPositive→Int-is-full-subposet .is-full-subposet.full {_} {zero} _ = 0≤x
  NonPositive→Int-is-full-subposet .is-full-subposet.full {zero} {suc _} ()
  NonPositive→Int-is-full-subposet .is-full-subposet.full {suc _} {suc _} (neg≤neg p) = s≤s p

--------------------------------------------------------------------------------
-- Joins

NonPositive-has-joins : has-joins NonPositive
NonPositive-has-joins .has-joins.join = min
NonPositive-has-joins .has-joins.joinl {x} {y} = min-≤l x y
NonPositive-has-joins .has-joins.joinr {x} {y} = min-≤r x y
NonPositive-has-joins .has-joins.universal {x} {y} {z} = min-univ x y z

abstract
  NonPositive→Int-is-full-subsemilattice : is-full-subsemilattice NonPositive-has-joins Int-has-joins NonPositive→Int
  NonPositive→Int-is-full-subsemilattice .is-full-subsemilattice.has-is-full-subposet = NonPositive→Int-is-full-subposet
  NonPositive→Int-is-full-subsemilattice .is-full-subsemilattice.pres-join = negℤ-distrib-min _ _
