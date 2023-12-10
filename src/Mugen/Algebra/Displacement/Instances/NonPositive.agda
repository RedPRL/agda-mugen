module Mugen.Algebra.Displacement.Instances.NonPositive where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Subalgebra
open import Mugen.Algebra.Displacement.Instances.Int
open import Mugen.Algebra.Displacement.Instances.Nat
open import Mugen.Algebra.Displacement.Instances.Opposite

open import Mugen.Order.Instances.NonPositive
  renaming (NonPositive to NonPositive-poset)

open import Mugen.Data.Int

--------------------------------------------------------------------------------
-- The Non-Positive Integers
-- Section 3.3.1
--
-- These have a terse definition as the opposite order of Nat+,
-- so we just use that.

NonPositive : Displacement-on NonPositive-poset
NonPositive = Opposite Nat-displacement

--------------------------------------------------------------------------------
-- Inclusion into Int

NonPositive→Int-is-full-subdisplacement
  : is-full-subdisplacement NonPositive Int-displacement NonPositive→Int
NonPositive→Int-is-full-subdisplacement = to-full-subdisplacement subalg where
  subalg : make-full-subdisplacement NonPositive Int-displacement NonPositive→Int
  subalg .make-full-subdisplacement.pres-ε = refl
  subalg .make-full-subdisplacement.pres-⊗ {x} {y} = +ℤ-negate x y
  subalg .make-full-subdisplacement.pres-≤ {x} {y} = negate-anti-mono y x
  subalg .make-full-subdisplacement.injective = negate-injective _ _
  subalg .make-full-subdisplacement.full {x} {y} = negate-anti-full y x
