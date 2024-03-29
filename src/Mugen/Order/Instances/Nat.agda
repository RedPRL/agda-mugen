module Mugen.Order.Instances.Nat where

open import Data.Nat
import Data.Int as Int
open import Order.Instances.Int

open import Mugen.Prelude
open import Mugen.Order.StrictOrder
open import Mugen.Order.Lattice
open import Mugen.Order.Instances.Int

--------------------------------------------------------------------------------
-- Bundles

Nat-poset : Poset lzero lzero
Nat-poset .Poset.Ob = Nat
Nat-poset .Poset._≤_ = _≤_
Nat-poset .Poset.≤-thin = ≤-is-prop
Nat-poset .Poset.≤-refl = ≤-refl
Nat-poset .Poset.≤-trans = ≤-trans
Nat-poset .Poset.≤-antisym = ≤-antisym

--------------------------------------------------------------------------------
-- Inclusion to Int-poset

Nat→Int : Strictly-monotone Nat-poset Int-poset
Nat→Int .Strictly-monotone.hom = Int.Int.pos
Nat→Int .Strictly-monotone.pres-≤[]-equal p .fst = Int.pos≤pos p
Nat→Int .Strictly-monotone.pres-≤[]-equal p .snd = Int.pos-injective

abstract
  Nat→Int-is-full-subposet : is-full-subposet Nat→Int
  Nat→Int-is-full-subposet .is-full-subposet.injective = Int.pos-injective
  Nat→Int-is-full-subposet .is-full-subposet.full (Int.pos≤pos p) = p

--------------------------------------------------------------------------------
-- Joins

Nat-has-joins : has-joins Nat-poset
Nat-has-joins .has-joins.join = max
Nat-has-joins .has-joins.joinl = max-≤l _ _
Nat-has-joins .has-joins.joinr = max-≤r _ _
Nat-has-joins .has-joins.universal = max-univ _ _ _

abstract
  Nat→Int-is-subsemilattice : is-full-subsemilattice Nat-has-joins Int-has-joins Nat→Int
  Nat→Int-is-subsemilattice .is-full-subsemilattice.has-is-full-subposet = Nat→Int-is-full-subposet
  Nat→Int-is-subsemilattice .is-full-subsemilattice.pres-join = refl

--------------------------------------------------------------------------------
-- Bottoms

Nat-has-bottom : has-bottom Nat-poset
Nat-has-bottom .has-bottom.bot = zero
Nat-has-bottom .has-bottom.is-bottom = 0≤x
