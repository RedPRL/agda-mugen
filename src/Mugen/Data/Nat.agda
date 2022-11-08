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
+-is-semigroup .associative {x} {y} {z} = sym (+-associative x y z)

+-0-is-monoid : is-monoid 0 _+_
+-0-is-monoid .has-is-semigroup = +-is-semigroup
+-0-is-monoid .idl {x} = refl
+-0-is-monoid .idr {x} = +-zeror x

--------------------------------------------------------------------------------
-- Order

<-irrefl : ∀ {x} → x < x → ⊥
<-irrefl (s≤s x<x) = <-irrefl x<x

<-ascend : ∀ {x} → x < suc x
<-ascend {x} = ≤-refl

<-weaken : ∀ {x y} → x < y → x ≤ y
<-weaken x<y = ≤-trans ≤-ascend x<y

≤-strengthen : ∀ {x y} → x ≤ y → x ≡ y ⊎ x < y
≤-strengthen {y = zero} 0≤x = inl refl
≤-strengthen {y = suc y} 0≤x = inr (s≤s 0≤x)
≤-strengthen (s≤s x≤y) = ⊎-map (ap suc) s≤s (≤-strengthen x≤y)

to-≤ : ∀ {x y} → x ≡ y ⊎ x < y → x ≤ y
to-≤ {x = x} (inl x≡y) = subst (x ≤_) x≡y ≤-refl
to-≤ (inr x<y) = ≤-trans ≤-ascend x<y

<-trans : ∀ {x y z} → x < y → y < z → x < z
<-trans x<y y<z = ≤-trans x<y (≤-trans ≤-ascend y<z)

<-is-strict-order : is-strict-order _<_
<-is-strict-order .is-strict-order.irrefl = <-irrefl 
<-is-strict-order .is-strict-order.trans = <-trans
<-is-strict-order .is-strict-order.has-prop = ≤-prop

module Nat-<-Reasoning where
  infix  1 begin-<_ begin-≤_
  infixr 2 step-< step-≤ step-≡
  infix  3 _<∎

  -- Used to block evaluation of _<ℤ_
  data _IsRelatedTo_ : Nat → Nat → Type where
    done : ∀ x → x IsRelatedTo x
    strong : ∀ x y → x < y → x IsRelatedTo y
    weak : ∀ x y → x ≤ y → x IsRelatedTo y

  Strong : ∀ {x y} → x IsRelatedTo y → Type
  Strong (done _) = ⊥
  Strong (strong _ _ _) = ⊤
  Strong (weak _ _ _) = ⊥

  begin-<_ : ∀ {x y} → (x<y : x IsRelatedTo y) → {Strong x<y} → x < y
  begin-< (strong _ _ x<y) = x<y

  begin-≤_ : ∀ {x y} → (x≤y : x IsRelatedTo y) → x ≤ y
  begin-≤ done x = ≤-refl
  begin-≤ strong x y x<y = <-weaken x<y
  begin-≤ weak x y x≤y = x≤y

  step-< : ∀ x {y z} → y IsRelatedTo z → x < y → x IsRelatedTo z
  step-< x (done y) x<y = strong x y x<y
  step-< x (strong y z y<z) x<y = strong x z (<-trans x<y y<z)
  step-< x (weak y z y≤z) x<y = strong x z (≤-trans x<y y≤z)

  step-≤ : ∀ x {y z} → y IsRelatedTo z → x ≤ y → x IsRelatedTo z
  step-≤ x (done y) x≤y = weak x y x≤y
  step-≤ x (strong y z y<z) x≤y = strong x z (≤-trans (s≤s x≤y) y<z)
  step-≤ x (weak y z y≤z) x≤y = weak x z (≤-trans x≤y y≤z)

  step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
  step-≡ x (done y) p = subst (x IsRelatedTo_) p (done x)
  step-≡ x (strong y z y<z) p = strong x z (subst (_< z) (sym p) y<z)
  step-≡ x (weak y z y≤z) p = weak x z (subst (_≤ z) (sym p) y≤z)

  _<∎ : ∀ x → x IsRelatedTo x
  _<∎ x = done x

  syntax step-< x q p = x <⟨ p ⟩ q
  syntax step-≤ x q p = x ≤⟨ p ⟩ q
  syntax step-≡ x q p = x ≡̇⟨ p ⟩ q

open Nat-<-Reasoning

+-<-left-invariant : ∀ {y z} x → y < z → x + y < x + z
+-<-left-invariant zero y<z = y<z
+-<-left-invariant (suc x) y<z = s≤s (+-<-left-invariant x y<z)

+-<-right-invariant : ∀ {x y} z → x < y → x + z < y + z
+-<-right-invariant z (s≤s x<y) = s≤s (+-preserves-≤r _ _ z x<y)

+-≤-right-invariant : ∀ {x y} z → non-strict _<_ x y → non-strict _<_ (x + z) (y + z)
+-≤-right-invariant z (inl x≡y) = inl (ap (_+ z) x≡y)
+-≤-right-invariant z (inr x<y) = inr (+-<-right-invariant z x<y)

max-zerol : ∀ x → max 0 x ≡ x
max-zerol zero = refl
max-zerol (suc x) = refl

max-zeror : ∀ x → max x 0 ≡ x
max-zeror zero = refl
max-zeror (suc x) = refl

max-is-lub : ∀ {x y z} → x ≤ z → y ≤ z → max x y ≤ z
max-is-lub 0≤x 0≤x = 0≤x
max-is-lub 0≤x (s≤s y≤z) = s≤s y≤z
max-is-lub (s≤s x≤z) 0≤x = s≤s x≤z
max-is-lub (s≤s x≤z) (s≤s y≤z) = s≤s (max-is-lub x≤z y≤z)

min-is-glb : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ min x y
min-is-glb 0≤x 0≤x = 0≤x
min-is-glb (s≤s z≤x) (s≤s z≤y) = s≤s (min-is-glb z≤x z≤y)
