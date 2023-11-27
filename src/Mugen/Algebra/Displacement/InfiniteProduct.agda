module Mugen.Algebra.Displacement.InfiniteProduct where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Order.Poset
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid

--------------------------------------------------------------------------------
-- Infinite Products
-- Section 3.3.5
--
-- The infinite product of a displacement algebra '𝒟' consists
-- of functions 'Nat → 𝒟'. Multiplication is performed pointwise,
-- and ordering is given by 'f ≤ g' if '∀ n. f n ≤ n'.

module Inf {o r} (𝒟 : Displacement-algebra o r) where
  private
    module 𝒟 = Displacement-algebra 𝒟
    open 𝒟 using (ε; _⊗_)

  _⊗∞_ : (Nat → ⌞ 𝒟 ⌟) → (Nat → ⌞ 𝒟 ⌟) → (Nat → ⌞ 𝒟 ⌟)
  f ⊗∞ g = λ n → f n ⊗ g n

  ε∞ : Nat → ⌞ 𝒟 ⌟
  ε∞ _ = ε

  ⊗∞-associative : ∀ {f g h : Nat → ⌞ 𝒟 ⌟} → (f ⊗∞ (g ⊗∞ h)) ≡ ((f ⊗∞ g) ⊗∞ h)
  ⊗∞-associative = funext λ x → 𝒟.associative

  ⊗∞-idl : ∀ {f : Nat → ⌞ 𝒟 ⌟} → (ε∞ ⊗∞ f) ≡ f
  ⊗∞-idl = funext λ x → 𝒟.idl

  ⊗∞-idr : ∀ {f : Nat → ⌞ 𝒟 ⌟} → (f ⊗∞ ε∞) ≡ f
  ⊗∞-idr = funext λ x → 𝒟.idr

  --------------------------------------------------------------------------------
  -- Algebra

  ⊗∞-is-magma : is-magma _⊗∞_
  ⊗∞-is-magma .has-is-set = Π-is-hlevel 2 (λ _ → 𝒟.has-is-set)

  ⊗∞-is-semigroup : is-semigroup _⊗∞_
  ⊗∞-is-semigroup .has-is-magma = ⊗∞-is-magma
  ⊗∞-is-semigroup .associative = ⊗∞-associative

  ⊗∞-is-monoid : is-monoid ε∞ _⊗∞_
  ⊗∞-is-monoid .has-is-semigroup = ⊗∞-is-semigroup
  ⊗∞-is-monoid .idl = ⊗∞-idl
  ⊗∞-is-monoid .idr = ⊗∞-idr

  --------------------------------------------------------------------------------
  -- Ordering

  _inf≤_ : ∀ (f g : Nat → ⌞ 𝒟 ⌟) → Type r
  f inf≤ g = (n : Nat) → f n 𝒟.≤ g n

  _inf<_ : ∀ (f g : Nat → ⌞ 𝒟 ⌟) → Type (o ⊔ r)
  _inf<_ = strict _inf≤_

  inf≤-thin : ∀ {f g} → is-prop (f inf≤ g)
  inf≤-thin = hlevel 1

  inf≤-refl : ∀ {f : Nat → ⌞ 𝒟 ⌟} → f inf≤ f
  inf≤-refl = λ _ → 𝒟.≤-refl

  inf≤-trans : ∀ {f g h} → f inf≤ g → g inf≤ h → f inf≤ h
  inf≤-trans f≤g g≤h n = 𝒟.≤-trans (f≤g n) (g≤h n)

  inf≤-antisym : ∀ {f g} → f inf≤ g → g inf≤ f → f ≡ g
  inf≤-antisym f≤g g≤f = funext λ n → 𝒟.≤-antisym (f≤g n) (g≤f n)

  ⊗∞-left-invariant : ∀ {f g h : Nat → ⌞ 𝒟 ⌟} → g inf≤ h → (f ⊗∞ g) inf≤ (f ⊗∞ h)
  ⊗∞-left-invariant g≤h n = 𝒟.≤-left-invariant (g≤h n)

  ⊗∞-injr-on-inf≤ : ∀ {f g h : Nat → ⌞ 𝒟 ⌟} → g inf≤ h → (f ⊗∞ g) ≡ (f ⊗∞ h) → g ≡ h
  ⊗∞-injr-on-inf≤ g≤h fg=fh = funext λ n → 𝒟.injr-on-≤ (g≤h n) (happly fg=fh n)

Inf : ∀ {o r} → Displacement-algebra o r → Poset o r
Inf {o = o} {r = r} 𝒟 = to-poset mk where
  open Inf 𝒟
  open make-poset

  mk : make-poset r (Nat → ⌞ 𝒟 ⌟)
  mk ._≤_ = _inf≤_
  mk .≤-refl = inf≤-refl
  mk .≤-trans = inf≤-trans
  mk .≤-thin = inf≤-thin
  mk .≤-antisym = inf≤-antisym

module _ {o r} (𝒟 : Displacement-algebra o r) where
  open Inf 𝒟
  open make-displacement-algebra

  --------------------------------------------------------------------------------
  -- Displacement Algebra

  private module 𝒟 = Displacement-algebra 𝒟

  InfProd : Displacement-algebra o r
  InfProd = to-displacement-algebra mk where
    mk : make-displacement-algebra (Inf 𝒟)
    mk .ε = ε∞
    mk ._⊗_ = _⊗∞_
    mk .idl = ⊗∞-idl
    mk .idr = ⊗∞-idr
    mk .associative = ⊗∞-associative
    mk .≤-left-invariant = ⊗∞-left-invariant
    mk .injr-on-≤ = ⊗∞-injr-on-inf≤

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  private module 𝒟∞ = Displacement-algebra InfProd

  ⊗∞-has-ordered-monoid : has-ordered-monoid 𝒟 → has-ordered-monoid InfProd
  ⊗∞-has-ordered-monoid 𝒟-om =
    right-invariant→has-ordered-monoid
      InfProd
      ⊗∞-right-invariant
    where
      open is-ordered-monoid 𝒟-om

      ⊗∞-right-invariant : ∀ {f g h} → f 𝒟∞.≤ g → (f ⊗∞ h) 𝒟∞.≤ (g ⊗∞ h)
      ⊗∞-right-invariant f≤g n = right-invariant (f≤g n)

  --------------------------------------------------------------------------------
  -- Joins

  ⊗∞-has-joins : has-joins 𝒟 → has-joins InfProd
  ⊗∞-has-joins 𝒟-joins = joins
    where
      open has-joins 𝒟-joins

      joins : has-joins InfProd
      joins .has-joins.join f g n = join (f n) (g n)
      joins .has-joins.joinl = λ _ → joinl
      joins .has-joins.joinr = λ _ → joinr
      joins .has-joins.universal f≤h g≤h = λ n → universal (f≤h n) (g≤h n)

  --------------------------------------------------------------------------------
  -- Bottom

  ⊗∞-has-bottom : has-bottom 𝒟 → has-bottom InfProd
  ⊗∞-has-bottom 𝒟-bottom = bottom
    where
      open has-bottom 𝒟-bottom

      bottom : has-bottom InfProd
      bottom .has-bottom.bot _ = bot
      bottom .has-bottom.is-bottom f = λ n → is-bottom (f n)
