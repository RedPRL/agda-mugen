module Mugen.Algebra.Displacement.Nat where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Int

import Mugen.Data.Nat as Nat
import Mugen.Data.Int as Int

--------------------------------------------------------------------------------
-- Natural Numbers
-- Section 3.3.1
--
-- This is the evident displacement algebra on natural numbers.
-- All of the interesting algebraic/order theoretic properties are proven in
-- 'Mugen.Data.Nat'; this module is just bundling together those proofs.

Nat+ : Displacement-algebra lzero lzero
Nat+ = to-displacement-algebra displacement where
  displacement : make-displacement-algebra Nat.Nat≤
  displacement .make-displacement-algebra.ε = 0
  displacement .make-displacement-algebra._⊗_ = _+_
  displacement .make-displacement-algebra.idl = refl
  displacement .make-displacement-algebra.idr = Nat.+-zeror _
  displacement .make-displacement-algebra.associative {x} {y} {z} = Nat.+-associative x y z
  displacement .make-displacement-algebra.≤-left-invariant = Nat.+-preserves-≤l _ _ _
  displacement .make-displacement-algebra.injr-on-≤ _ = Nat.+-inj _ _ _

--------------------------------------------------------------------------------
-- Ordered Monoid

nat-+-has-ordered-monoid : has-ordered-monoid Nat+
nat-+-has-ordered-monoid = right-invariant→has-ordered-monoid Nat+ λ {x} {y} {z} →
  Nat.+-preserves-≤r x y z

--------------------------------------------------------------------------------
-- Joins

nat-+-has-joins : has-joins Nat+
nat-+-has-joins .has-joins.join = Nat.max
nat-+-has-joins .has-joins.joinl {x} {y} = Nat.max-≤l x y
nat-+-has-joins .has-joins.joinr {x} {y} = Nat.max-≤r x y
nat-+-has-joins .has-joins.universal {x} {y} {z} x≤z y≤z =
  Nat.max-is-lub x y z x≤z y≤z

--------------------------------------------------------------------------------
-- Bottoms

nat-+-has-bottom : has-bottom Nat+
nat-+-has-bottom .has-bottom.bot = 0
nat-+-has-bottom .has-bottom.is-bottom x = Nat.0≤x

--------------------------------------------------------------------------------
-- Subalgebra

Nat+⊆Int+ : is-displacement-subalgebra Nat+ Int+
Nat+⊆Int+ = to-displacement-subalgebra subalg where
    subalg : make-displacement-subalgebra _ _
    subalg .make-displacement-subalgebra.into = Int.pos
    subalg .make-displacement-subalgebra.pres-ε = refl
    subalg .make-displacement-subalgebra.pres-⊗ = Int.+ℤ-pos
    subalg .make-displacement-subalgebra.mono _ _ x≤y = x≤y
    subalg .make-displacement-subalgebra.inj = Int.pos-inj

Nat-is-subsemilattice : is-displacement-subsemilattice nat-+-has-joins Int+-has-joins
Nat-is-subsemilattice .is-displacement-subsemilattice.has-displacement-subalgebra = Nat+⊆Int+
Nat-is-subsemilattice .is-displacement-subsemilattice.pres-joins x y = refl
