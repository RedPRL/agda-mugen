module Mugen.Order.Instances.Int where

open import Mugen.Prelude
open import Mugen.Data.Int
open import Mugen.Order.Lattice

-------------------------------------------------------------------------------
-- Bundles

Int-poset : Poset lzero lzero
Int-poset = poset where
  poset : Poset _ _
  poset .Poset.Ob = Int
  poset .Poset._≤_ = _≤ℤ_
  poset .Poset.≤-refl = ≤ℤ-refl _
  poset .Poset.≤-trans = ≤ℤ-trans _ _ _
  poset .Poset.≤-thin = ≤ℤ-is-prop _ _
  poset .Poset.≤-antisym = ≤ℤ-antisym _ _

--------------------------------------------------------------------------------
-- Joins

Int-has-joins : has-joins Int-poset
Int-has-joins .has-joins.join = maxℤ
Int-has-joins .has-joins.joinl {x} {y} = maxℤ-≤l x y
Int-has-joins .has-joins.joinr {x} {y} = maxℤ-≤r x y
Int-has-joins .has-joins.universal {x} {y} {z} = maxℤ-is-lub x y z
