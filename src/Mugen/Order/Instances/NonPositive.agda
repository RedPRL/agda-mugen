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

Non-positive : Poset lzero lzero
Non-positive = Opposite Nat-poset

--------------------------------------------------------------------------------
-- Inclusion to Int-poset

Non-positive→Int : Strictly-monotone Non-positive Int-poset
Non-positive→Int .Strictly-monotone.hom x = negℤ (pos x)
Non-positive→Int .Strictly-monotone.pres-≤[]-equal p .fst = negℤ-anti _ _ (pos≤pos p)
Non-positive→Int .Strictly-monotone.pres-≤[]-equal p .snd q = pos-injective $ negℤ-injective _ _ q

abstract
  Non-positive→Int-is-full-subposet : is-full-subposet Non-positive→Int
  Non-positive→Int-is-full-subposet .is-full-subposet.injective p = pos-injective $ negℤ-injective _ _ p
  Non-positive→Int-is-full-subposet .is-full-subposet.full {_} {zero} _ = 0≤x
  Non-positive→Int-is-full-subposet .is-full-subposet.full {zero} {suc _} ()
  Non-positive→Int-is-full-subposet .is-full-subposet.full {suc _} {suc _} (neg≤neg p) = s≤s p

--------------------------------------------------------------------------------
-- Joins

Non-positive-has-joins : has-joins Non-positive
Non-positive-has-joins .has-joins.join = min
Non-positive-has-joins .has-joins.joinl {x} {y} = min-≤l x y
Non-positive-has-joins .has-joins.joinr {x} {y} = min-≤r x y
Non-positive-has-joins .has-joins.universal {x} {y} {z} = min-univ x y z

abstract
  Non-positive→Int-is-full-subsemilattice : is-full-subsemilattice Non-positive-has-joins Int-has-joins Non-positive→Int
  Non-positive→Int-is-full-subsemilattice .is-full-subsemilattice.has-is-full-subposet = Non-positive→Int-is-full-subposet
  Non-positive→Int-is-full-subsemilattice .is-full-subsemilattice.pres-join = negℤ-distrib-min _ _
