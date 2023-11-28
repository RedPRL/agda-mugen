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
-- POPL 2023 Section 3.3.5 discussed the special case where I = Nat and 𝒟 is a constant family
--
-- The product of indexed displacement algebras consists
-- of functions '(i : I) → 𝒟 i'. Multiplication is performed pointwise,
-- and ordering is given by 'f ≤ g' if '∀ i. f i ≤ g i'.

module Idx {o o' r} (I : Type o) (𝒟 : I → Displacement-algebra o' r) where
  private
    module 𝒟 {i : I} = Displacement-algebra (𝒟 i)
    open 𝒟 using (ε; _⊗_)

  map₂ : (∀ {i} → ⌞ 𝒟 i ⌟ → ⌞ 𝒟 i ⌟ → ⌞ 𝒟 i ⌟) → (∀ i → ⌞ 𝒟 i ⌟) → (∀ i → ⌞ 𝒟 i ⌟) → (∀ i → ⌞ 𝒟 i ⌟)
  map₂ m f g i = m (f i) (g i)

  _idx⊗_ : (∀ i → ⌞ 𝒟 i ⌟) → (∀ i → ⌞ 𝒟 i ⌟) → (∀ i → ⌞ 𝒟 i ⌟)
  _idx⊗_ = map₂ _⊗_

  idxε : (i : I) → ⌞ 𝒟 i ⌟
  idxε _ = ε

  idx⊗-associative : ∀ {f g h : (i : I) → ⌞ 𝒟 i ⌟} → (f idx⊗ (g idx⊗ h)) ≡ ((f idx⊗ g) idx⊗ h)
  idx⊗-associative = funext λ x → 𝒟.associative

  idx⊗-idl : ∀ {f : (i : I) → ⌞ 𝒟 i ⌟} → (idxε idx⊗ f) ≡ f
  idx⊗-idl = funext λ x → 𝒟.idl

  idx⊗-idr : ∀ {f : (i : I) → ⌞ 𝒟 i ⌟} → (f idx⊗ idxε) ≡ f
  idx⊗-idr = funext λ x → 𝒟.idr

  --------------------------------------------------------------------------------
  -- Algebra

  idx⊗-is-magma : is-magma _idx⊗_
  idx⊗-is-magma .has-is-set = Π-is-hlevel 2 (λ _ → 𝒟.has-is-set)

  idx⊗-is-semigroup : is-semigroup _idx⊗_
  idx⊗-is-semigroup .has-is-magma = idx⊗-is-magma
  idx⊗-is-semigroup .associative = idx⊗-associative

  idx⊗-is-monoid : is-monoid idxε _idx⊗_
  idx⊗-is-monoid .has-is-semigroup = idx⊗-is-semigroup
  idx⊗-is-monoid .idl = idx⊗-idl
  idx⊗-is-monoid .idr = idx⊗-idr

  --------------------------------------------------------------------------------
  -- Ordering

  _idx≤_ : ∀ (f g : ∀ i → ⌞ 𝒟 i ⌟) → Type (o ⊔ r)
  f idx≤ g = (i : I) → f i 𝒟.≤ g i

  idx≤-thin : ∀ {f g} → is-prop (f idx≤ g)
  idx≤-thin = hlevel 1

  idx≤-refl : ∀ {f : ∀ i → ⌞ 𝒟 i ⌟} → f idx≤ f
  idx≤-refl = λ _ → 𝒟.≤-refl

  idx≤-trans : ∀ {f g h} → f idx≤ g → g idx≤ h → f idx≤ h
  idx≤-trans f≤g g≤h i = 𝒟.≤-trans (f≤g i) (g≤h i)

  idx≤-antisym : ∀ {f g} → f idx≤ g → g idx≤ f → f ≡ g
  idx≤-antisym f≤g g≤f = funext λ i → 𝒟.≤-antisym (f≤g i) (g≤f i)

  idx⊗-left-strict-invariant : ∀ {f g h} → g idx≤ h → ((f idx⊗ g) idx≤ (f idx⊗ h)) × ((f idx⊗ g) ≡ (f idx⊗ h) → g ≡ h)
  idx⊗-left-strict-invariant g≤h =
    (𝒟.left-invariant ⊙ g≤h) , λ fg=fh → funext λ i → 𝒟.injr-on-related (g≤h i) (happly fg=fh i)

Idx : ∀ {o o' r} (I : Type o) → (I → Displacement-algebra o' r) → Poset (o ⊔ o') (o ⊔ r)
Idx {o = o} {o' = o'} {r = r} I 𝒟 = to-poset mk where
  open Idx I 𝒟
  open make-poset

  mk : make-poset (o ⊔ r) (∀ i → ⌞ 𝒟 i ⌟)
  mk ._≤_ = _idx≤_
  mk .≤-refl = idx≤-refl
  mk .≤-trans = idx≤-trans
  mk .≤-thin = idx≤-thin
  mk .≤-antisym = idx≤-antisym

module _ {o o' r} (I : Type o) (𝒟 : I → Displacement-algebra o' r) where
  open Idx I 𝒟
  open make-displacement-algebra
  private module 𝒟 {i : I} = Displacement-algebra (𝒟 i)

  --------------------------------------------------------------------------------
  -- Displacement Algebra

  IdxProd : Displacement-algebra (o ⊔ o') (o ⊔ r)
  IdxProd = to-displacement-algebra mk where
    mk : make-displacement-algebra (Idx I 𝒟)
    mk .ε = idxε
    mk ._⊗_ = _idx⊗_
    mk .idl = idx⊗-idl
    mk .idr = idx⊗-idr
    mk .associative = idx⊗-associative
    mk .left-strict-invariant = idx⊗-left-strict-invariant

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  private module 𝒟∞ = Displacement-algebra IdxProd

  idx⊗-has-ordered-monoid : (∀ i → has-ordered-monoid (𝒟 i)) → has-ordered-monoid IdxProd
  idx⊗-has-ordered-monoid 𝒟-om =
    right-invariant→has-ordered-monoid
      IdxProd
      idx⊗-right-invariant
    where
      open module M {a : I} = is-ordered-monoid (𝒟-om a)

      idx⊗-right-invariant : ∀ {f g h} → f 𝒟∞.≤ g → (f idx⊗ h) 𝒟∞.≤ (g idx⊗ h)
      idx⊗-right-invariant f≤g i = right-invariant (f≤g i)

  --------------------------------------------------------------------------------
  -- Joins

  idx⊗-has-joins : (∀ i → has-joins (𝒟 i)) → has-joins IdxProd
  idx⊗-has-joins 𝒟-joins = joins
    where
      open module J {a : I} = has-joins (𝒟-joins a)

      joins : has-joins IdxProd
      joins .has-joins.join = map₂ join
      joins .has-joins.joinl = λ _ → joinl
      joins .has-joins.joinr = λ _ → joinr
      joins .has-joins.universal f≤h g≤h = λ i → universal (f≤h i) (g≤h i)

  --------------------------------------------------------------------------------
  -- Bottom

  idx⊗-has-bottom : (∀ i → has-bottom (𝒟 i)) → has-bottom IdxProd
  idx⊗-has-bottom 𝒟-bottom = bottom
    where
      open module B {a : I} = has-bottom (𝒟-bottom a)

      bottom : has-bottom IdxProd
      bottom .has-bottom.bot _ = bot
      bottom .has-bottom.is-bottom f = λ i → is-bottom (f i)
