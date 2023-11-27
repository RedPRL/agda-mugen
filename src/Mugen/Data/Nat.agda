module Mugen.Data.Nat where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude hiding (Nat-is-set)
open import Mugen.Order.Poset

open import Data.Nat public


--------------------------------------------------------------------------------
-- Algebra

+-is-magma : is-magma _+_
+-is-magma .has-is-set = Nat-is-set

+-is-semigroup : is-semigroup _+_
+-is-semigroup .has-is-magma = +-is-magma
+-is-semigroup .associative {x} {y} {z} = +-associative x y z

+-0-is-monoid : is-monoid 0 _+_
+-0-is-monoid .has-is-semigroup = +-is-semigroup
+-0-is-monoid .idl {x} = refl
+-0-is-monoid .idr {x} = +-zeror x

--------------------------------------------------------------------------------
-- Order

≡→≤ : ∀ {x y} → x ≡ y → x ≤ y
≡→≤ {x = zero} {y = y} p = 0≤x
≡→≤ {x = suc x} {y = zero} p = absurd (suc≠zero p)
≡→≤ {x = suc x} {y = suc y} p = s≤s (≡→≤ (suc-inj p))

≤-is-partial-order : is-partial-order _≤_
≤-is-partial-order .is-partial-order.≤-refl = ≤-refl
≤-is-partial-order .is-partial-order.≤-trans = ≤-trans
≤-is-partial-order .is-partial-order.≤-thin = ≤-is-prop
≤-is-partial-order .is-partial-order.≤-antisym = ≤-antisym

max-zerol : ∀ x → max 0 x ≡ x
max-zerol zero = refl
max-zerol (suc x) = refl

max-zeror : ∀ x → max x 0 ≡ x
max-zeror zero = refl
max-zeror (suc x) = refl

max-is-lub : ∀ x y z → x ≤ z → y ≤ z → max x y ≤ z
max-is-lub zero zero z 0≤x 0≤x = 0≤x
max-is-lub zero (suc y) (suc z) 0≤x (s≤s q) = s≤s q
max-is-lub (suc x) zero (suc z) (s≤s p) 0≤x = s≤s p
max-is-lub (suc x) (suc y) (suc z) (s≤s p) (s≤s q) = s≤s (max-is-lub x y z p q)

min-is-glb : ∀ x y z → z ≤ x → z ≤ y → z ≤ min x y
min-is-glb x y zero 0≤x 0≤x = 0≤x
min-is-glb (suc x) (suc y) (suc z) (s≤s p) (s≤s q) = s≤s (min-is-glb x y z p q)

--------------------------------------------------------------------------------
-- Bundles

Nat≤ : Poset lzero lzero
Nat≤ .Poset.Ob = Nat
Nat≤ .Poset.poset-on .Poset-on._≤_ = _≤_
Nat≤ .Poset.poset-on .Poset-on.has-is-poset = ≤-is-partial-order
