module Mugen.Data.Nat where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude hiding (Nat-is-set)
open import Mugen.Order.StrictOrder

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

≤-strengthen : ∀ x y → x ≤ y → x ≡ y ⊎ x < y
≤-strengthen zero zero 0≤x = inl refl
≤-strengthen zero (suc y) 0≤x = inr (s≤s 0≤x)
≤-strengthen (suc x) (suc y) (s≤s p) =
  [ (λ p → inl (ap suc p))
  , (λ p → inr (s≤s p))
  ] (≤-strengthen x y p)

<-weaken : ∀ x y → x < y → x ≤ y
<-weaken x (suc y) (s≤s p) = ≤-sucr p

≡→≤ : ∀ {x y} → x ≡ y → x ≤ y
≡→≤ {x = zero} {y = y} p = 0≤x
≡→≤ {x = suc x} {y = zero} p = absurd (zero≠suc (sym p))
≡→≤ {x = suc x} {y = suc y} p = s≤s (≡→≤ (suc-inj p))

≤≃non-strict : ∀ {x y} → (x ≤ y) ≃ non-strict _<_ x y
≤≃non-strict {x = x} {y = y} =
  prop-ext
    ≤-is-prop
    (disjoint-⊎-is-prop (Nat-is-set x y) ≤-is-prop λ (p , q) → <-irrefl p q)
    (≤-strengthen _ _)
    [ (λ p → subst (λ z → x ≤ z) p ≤-refl) , <-weaken x y ]

<-is-strict-order : is-strict-order _<_
<-is-strict-order .is-strict-order.<-irrefl {x} = <-irrefl refl
<-is-strict-order .is-strict-order.<-trans {x} {y} {z} p q = ≤-trans (≤-sucr p) q
<-is-strict-order .is-strict-order.<-thin {x} {y} = ≤-is-prop
<-is-strict-order .is-strict-order.has-is-set = Nat-is-set

+-<-left-invariant : ∀ x y z → y < z → x + y < x + z
+-<-left-invariant x y z p =
  ≤-trans
    (≡→≤ (sym (+-sucr x y)))
    (+-preserves-≤l (suc y) z x p)

+-<-right-invariant : ∀ x y z → x < y → x + z < y + z
+-<-right-invariant x y z p = +-preserves-≤r (suc x) y z p

-- Lack of double orders forces our hand here.
+-≤-right-invariant : ∀ x y z → non-strict _<_ x y → non-strict _<_ (x + z) (y + z)
+-≤-right-invariant x y z p =
  Equiv.to ≤≃non-strict (+-preserves-≤r x y z (Equiv.from ≤≃non-strict p))

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
