module Mugen.Order.Instances.Int where

open import Data.Int
open import Order.Instances.Int

open import Mugen.Prelude
open import Mugen.Order.Lattice

--------------------------------------------------------------------------------
-- Joins

Int-has-joins : has-joins Int-poset
Int-has-joins .has-joins.join = maxℤ
Int-has-joins .has-joins.joinl {x} {y} = maxℤ-≤l x y
Int-has-joins .has-joins.joinr {x} {y} = maxℤ-≤r x y
Int-has-joins .has-joins.universal {x} {y} {z} = maxℤ-univ x y z
