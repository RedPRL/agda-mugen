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

<-irrefl : ∀ x → x < x → ⊥
<-irrefl zero    0<0 = 0<0
<-irrefl (suc x) x<x = <-irrefl x x<x

<-suc : ∀ x → x < suc x
<-suc zero = tt
<-suc (suc x) = <-suc x

≤-suc : ∀ x → x ≤ suc x
≤-suc zero = tt
≤-suc (suc x) = ≤-suc x

<-weaken : ∀ x y → x < y → x ≤ y
<-weaken x y x<y = ≤-trans x (suc x) y (≤-suc x) x<y

≤-strengthen : ∀ x y → x ≤ y → x ≡ y ⊎ x < y
≤-strengthen zero zero x≤y = inl refl
≤-strengthen zero (suc y) x≤y = inr (0≤x y)
≤-strengthen (suc x) (suc y) x≤y = ⊎-map (ap suc) (λ x<y → x<y) (≤-strengthen x y x≤y)

to-≤ : ∀ x y → x ≡ y ⊎ x < y → x ≤ y
to-≤ x y (inl x≡y) = subst (x ≤_) x≡y (≤-refl x)
to-≤ x y (inr x<y) = ≤-trans x (suc x) y (≤-suc x) x<y

≤-plusl : ∀ x y → x ≤ y + x
≤-plusl x zero = ≤-refl x
≤-plusl x (suc y) = ≤-trans x (suc x) (suc y + x) (≤-suc x) (≤-plusl x y)

≤-plusr : ∀ x y → x ≤ x + y
≤-plusr zero y = 0≤x y
≤-plusr (suc x) y = ≤-plusr x y

<-trans : ∀ x y z → x < y → y < z → x < z
<-trans x y z x<y y<z = ≤-trans (suc x) y z x<y (≤-trans y (suc y) z (≤-suc y) y<z)

<-prop : ∀ x y → is-prop (x < y)
<-prop x y = ≤-prop (suc x) y

<-is-strict-order : is-strict-order _<_
<-is-strict-order .is-strict-order.irrefl {x} = <-irrefl x 
<-is-strict-order .is-strict-order.trans {x} {y} {z} = <-trans x y z
<-is-strict-order .is-strict-order.has-prop {x} {y} = <-prop x y

<-≤-trans : ∀ x y z → x < y → y ≤ z → x < z
<-≤-trans x y z = ≤-trans (suc x) y z

≤-<-trans : ∀ x y z → x ≤ y → y < z → x < z
≤-<-trans x y z = ≤-trans (suc x) (suc y) z

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
  begin-≤ done x = ≤-refl x
  begin-≤ strong x y x<y = <-weaken x y x<y
  begin-≤ weak x y x≤y = x≤y

  step-< : ∀ x {y z} → y IsRelatedTo z → x < y → x IsRelatedTo z
  step-< x (done y) x<y = strong x y x<y
  step-< x (strong y z y<z) x<y = strong x z (<-trans x y z x<y y<z)
  step-< x (weak y z y≤z) x<y = strong x z (<-≤-trans x y z x<y y≤z)

  step-≤ : ∀ x {y z} → y IsRelatedTo z → x ≤ y → x IsRelatedTo z
  step-≤ x (done y) x≤y = weak x y x≤y
  step-≤ x (strong y z y<z) x≤y = strong x z (≤-<-trans x y z x≤y y<z)
  step-≤ x (weak y z y≤z) x≤y = weak x z (≤-trans x y z x≤y y≤z)

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

+-<-left-invariant : ∀ x y z → y < z → x + y < x + z
+-<-left-invariant zero y z y<z = y<z
+-<-left-invariant (suc x) y z y<z = +-<-left-invariant x y z y<z

+-<-right-invariant : ∀ x y z → x < y → x + z < y + z
+-<-right-invariant zero (suc y) z x<y = ≤-plusl z y
+-<-right-invariant (suc x) (suc y) z x<y = +-<-right-invariant x y z x<y

+-≤-right-invariant : ∀ x y z → non-strict _<_ x y → non-strict _<_ (x + z) (y + z)
+-≤-right-invariant x y z (inl x≡y) = inl (ap (_+ z) x≡y)
+-≤-right-invariant x y z (inr x<y) = inr (+-<-right-invariant x y z x<y)

max-zerol : ∀ x → max 0 x ≡ x
max-zerol zero = refl
max-zerol (suc x) = refl

max-zeror : ∀ x → max x 0 ≡ x
max-zeror zero = refl
max-zeror (suc x) = refl

max-is-lub : ∀ x y z → x ≤ z → y ≤ z → max x y ≤ z
max-is-lub zero zero zero x≤z y≤z = tt
max-is-lub zero zero (suc z) x≤z y≤z = tt
max-is-lub zero (suc y) (suc z) x≤z y≤z = y≤z
max-is-lub (suc x) zero (suc z) x≤z y≤z = x≤z
max-is-lub (suc x) (suc y) (suc z) x≤z y≤z = max-is-lub x y z x≤z y≤z

min-is-glb : ∀ x y z → z ≤ x → z ≤ y → z ≤ min x y
min-is-glb zero zero zero z≤x z≤y = tt
min-is-glb zero (suc y) zero z≤x z≤y = tt
min-is-glb (suc x) zero zero z≤x z≤y = tt
min-is-glb (suc x) (suc y) zero z≤x z≤y = tt
min-is-glb (suc x) (suc y) (suc z) z≤x z≤y = min-is-glb x y z z≤x z≤y
