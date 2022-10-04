module Mugen.Algebra.Displacement.Nat where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Int

import Mugen.Data.Nat as Nat
import Mugen.Data.Int as Int

+-is-displacement-algebra : is-displacement-algebra Nat._<_ 0 _+_
+-is-displacement-algebra .is-displacement-algebra.has-monoid = Nat.+-0-is-monoid
+-is-displacement-algebra .is-displacement-algebra.has-strict-order = Nat.<-is-strict-order
+-is-displacement-algebra .is-displacement-algebra.left-invariant {x} {y} {z} = Nat.+-<-left-invariant x y z

Nat+ : DisplacementAlgebra lzero lzero
⌞ Nat+ ⌟ = Nat
Nat+ .structure .DisplacementAlgebra-on._<_ = Nat._<_
Nat+ .structure .DisplacementAlgebra-on.ε = 0
Nat+ .structure .DisplacementAlgebra-on._⊗_ = _+_
Nat+ .structure .DisplacementAlgebra-on.has-displacement-algebra = +-is-displacement-algebra
⌞ Nat+ ⌟-set = Nat.Nat-is-set

nat-+-has-ordered-monoid : has-ordered-monoid Nat+
nat-+-has-ordered-monoid = right-invariant→has-ordered-monoid Nat+ λ {x} {y} {z} →
  Nat.+-≤-right-invariant x y z

nat-+-has-bottom : has-bottom Nat+
nat-+-has-bottom .has-bottom.bot = 0
nat-+-has-bottom .has-bottom.is-bottom x = Nat.≤-strengthen 0 x (Nat.0≤x x)

nat-+-has-joins : has-joins Nat+
nat-+-has-joins .has-joins.join = Nat.max
nat-+-has-joins .has-joins.joinl {x} {y} = Nat.≤-strengthen x (Nat.max x y) (Nat.max-≤l x y)
nat-+-has-joins .has-joins.joinr {x} {y} = Nat.≤-strengthen y (Nat.max x y) (Nat.max-≤r x y)
nat-+-has-joins .has-joins.universal {x} {y} {z} x≤z y≤z =
  Nat.≤-strengthen (Nat.max x y) z (Nat.max-is-lub x y z (Nat.to-≤ x z x≤z) (Nat.to-≤ y z y≤z))

Nat+⊆Int+ : is-displacement-subalgebra Nat+ Int+
Nat+⊆Int+ .is-displacement-subalgebra.into ⟨$⟩ x = Int.pos x
Nat+⊆Int+ .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-ε = refl
Nat+⊆Int+ .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-⊗ _ _ = refl
Nat+⊆Int+ .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.strictly-mono x<y = x<y
Nat+⊆Int+ .is-displacement-subalgebra.inj = Int.pos-inj
