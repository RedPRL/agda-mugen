module Mugen.Algebra.Displacement.IndexedProduct where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Order.Poset
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid

--------------------------------------------------------------------------------
-- Product of Indexed Displacements
--
-- The product of indexed displacement algebras consists
-- of functions '(a : I) → 𝒟 a'. Multiplication is performed pointwise,
-- and ordering is given by 'f ≤ g' if '∀ n. f n ≤ g n'.

module Ind {o o' r} (I : Type o) (𝒟 : I → Displacement-algebra o' r) where
  private
    module 𝒟 {a : I} = Displacement-algebra (𝒟 a)
    open 𝒟 using (ε; _⊗_)

  _fun⊗_ : (∀ a → ⌞ 𝒟 a ⌟) → (∀ a → ⌞ 𝒟 a ⌟) → (∀ a → ⌞ 𝒟 a ⌟)
  f fun⊗ g = λ a → f a ⊗ g a

  funε : (a : I) → ⌞ 𝒟 a ⌟
  funε _ = ε

  fun⊗-associative : ∀ {f g h : (a : I) → ⌞ 𝒟 a ⌟} → (f fun⊗ (g fun⊗ h)) ≡ ((f fun⊗ g) fun⊗ h)
  fun⊗-associative = funext λ x → 𝒟.associative

  fun⊗-idl : ∀ {f : (a : I) → ⌞ 𝒟 a ⌟} → (funε fun⊗ f) ≡ f
  fun⊗-idl = funext λ x → 𝒟.idl

  fun⊗-idr : ∀ {f : (a : I) → ⌞ 𝒟 a ⌟} → (f fun⊗ funε) ≡ f
  fun⊗-idr = funext λ x → 𝒟.idr

  --------------------------------------------------------------------------------
  -- Algebra

  fun⊗-is-magma : is-magma _fun⊗_
  fun⊗-is-magma .has-is-set = Π-is-hlevel 2 (λ _ → 𝒟.has-is-set)

  fun⊗-is-semigroup : is-semigroup _fun⊗_
  fun⊗-is-semigroup .has-is-magma = fun⊗-is-magma
  fun⊗-is-semigroup .associative = fun⊗-associative

  fun⊗-is-monoid : is-monoid funε _fun⊗_
  fun⊗-is-monoid .has-is-semigroup = fun⊗-is-semigroup
  fun⊗-is-monoid .idl = fun⊗-idl
  fun⊗-is-monoid .idr = fun⊗-idr

  --------------------------------------------------------------------------------
  -- Ordering

  _fun≤_ : ∀ (f g : ∀ a → ⌞ 𝒟 a ⌟) → Type (o ⊔ r)
  f fun≤ g = (n : I) → f n 𝒟.≤ g n

  _fun<_ : ∀ (f g : ∀ a → ⌞ 𝒟 a ⌟) → Type (o ⊔ o' ⊔ r)
  _fun<_ = strict _fun≤_

  fun≤-thin : ∀ {f g} → is-prop (f fun≤ g)
  fun≤-thin = hlevel 1

  fun≤-refl : ∀ {f : ∀ a → ⌞ 𝒟 a ⌟} → f fun≤ f
  fun≤-refl = λ _ → 𝒟.≤-refl

  fun≤-trans : ∀ {f g h} → f fun≤ g → g fun≤ h → f fun≤ h
  fun≤-trans f≤g g≤h n = 𝒟.≤-trans (f≤g n) (g≤h n)

  fun≤-antisym : ∀ {f g} → f fun≤ g → g fun≤ f → f ≡ g
  fun≤-antisym f≤g g≤f = funext λ n → 𝒟.≤-antisym (f≤g n) (g≤f n)

  fun⊗-left-invariant : ∀ {f g h} → g fun≤ h → (f fun⊗ g) fun≤ (f fun⊗ h)
  fun⊗-left-invariant g≤h n = 𝒟.≤-left-invariant (g≤h n)

  fun⊗-injr-on-fun≤ : ∀ {f g h} → g fun≤ h → (f fun⊗ g) ≡ (f fun⊗ h) → g ≡ h
  fun⊗-injr-on-fun≤ g≤h fg=fh = funext λ n → 𝒟.injr-on-≤ (g≤h n) (happly fg=fh n)

Ind : ∀ {o o' r} (I : Type o) → (I → Displacement-algebra o' r) → Poset (o ⊔ o') (o ⊔ r)
Ind {o = o} {o' = o'} {r = r} I 𝒟 = to-poset mk where
  open Ind I 𝒟
  open make-poset

  mk : make-poset (o ⊔ r) (∀ a → ⌞ 𝒟 a ⌟)
  mk ._≤_ = _fun≤_
  mk .≤-refl = fun≤-refl
  mk .≤-trans = fun≤-trans
  mk .≤-thin = fun≤-thin
  mk .≤-antisym = fun≤-antisym

module _ {o o' r} (I : Type o) (𝒟 : I → Displacement-algebra o' r) where
  open Ind I 𝒟
  open make-displacement-algebra
  private module 𝒟 {a : I} = Displacement-algebra (𝒟 a)

  --------------------------------------------------------------------------------
  -- Displacement Algebra

  IndProd : Displacement-algebra (o ⊔ o') (o ⊔ r)
  IndProd = to-displacement-algebra mk where
    mk : make-displacement-algebra (Ind I 𝒟)
    mk .ε = funε
    mk ._⊗_ = _fun⊗_
    mk .idl = fun⊗-idl
    mk .idr = fun⊗-idr
    mk .associative = fun⊗-associative
    mk .≤-left-invariant = fun⊗-left-invariant
    mk .injr-on-≤ = fun⊗-injr-on-fun≤

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  private module 𝒟∞ = Displacement-algebra IndProd

  fun⊗-has-ordered-monoid : (∀ a → has-ordered-monoid (𝒟 a))
    → has-ordered-monoid IndProd
  fun⊗-has-ordered-monoid 𝒟-om =
    right-invariant→has-ordered-monoid
      IndProd
      fun⊗-right-invariant
    where
      open module M {a : I} = is-ordered-monoid (𝒟-om a)

      fun⊗-right-invariant : ∀ {f g h} → f 𝒟∞.≤ g → (f fun⊗ h) 𝒟∞.≤ (g fun⊗ h)
      fun⊗-right-invariant f≤g n = right-invariant (f≤g n)

  --------------------------------------------------------------------------------
  -- Joins

  fun⊗-has-joins : ((a : I) → has-joins (𝒟 a))
    → has-joins IndProd
  fun⊗-has-joins 𝒟-joins = joins
    where
      open module J {a : I} = has-joins (𝒟-joins a)

      joins : has-joins IndProd
      joins .has-joins.join f g n = join (f n) (g n)
      joins .has-joins.joinl = λ _ → joinl
      joins .has-joins.joinr = λ _ → joinr
      joins .has-joins.universal f≤h g≤h = λ n → universal (f≤h n) (g≤h n)

  --------------------------------------------------------------------------------
  -- Bottom

  fun⊗-has-bottom : (∀ a → has-bottom (𝒟 a)) → has-bottom IndProd
  fun⊗-has-bottom 𝒟-bottom = bottom
    where
      open module B {a : I} = has-bottom (𝒟-bottom a)

      bottom : has-bottom IndProd
      bottom .has-bottom.bot _ = bot
      bottom .has-bottom.is-bottom f = λ n → is-bottom (f n)
