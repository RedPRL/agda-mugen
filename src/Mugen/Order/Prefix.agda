module Mugen.Order.Prefix where

open import Data.List

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

data Prefix {ℓ} (A : Type ℓ) : List A → List A → Type ℓ where
  phead : ∀ {x xs} → Prefix A [] (x ∷ xs)
  -- Annoying hack to work around --without-K
  ptail : ∀ {x y xs ys} → x ≡ y → Prefix A xs ys → Prefix A (x ∷ xs) (y ∷ ys)

private variable
  ℓ : Level
  A : Type ℓ

prefix-irrefl : ∀ (xs : List A) → Prefix A xs xs → ⊥
prefix-irrefl (x ∷ xs) (ptail p xs<xs) = prefix-irrefl xs xs<xs

prefix-trans : ∀ (xs ys zs : List A) → Prefix A xs ys → Prefix A ys zs → Prefix A xs zs
prefix-trans [] (y ∷ ys) (z ∷ zs) phead (ptail y≡z ys<zs) = phead
prefix-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (ptail x≡y xs<ys) (ptail y≡z ys<zs) =
  ptail (x≡y ∙ y≡z) (prefix-trans xs ys zs xs<ys ys<zs)

prefix-is-prop : ∀ {xs ys : List A} → is-set A → is-prop (Prefix A xs ys)
prefix-is-prop {xs = []} {ys = y ∷ ys} aset phead phead = refl
prefix-is-prop {xs = x ∷ xs} {ys = y ∷ ys} aset (ptail x≡y xs<ys) (ptail x≡y′ xs<ys′) =
  ap₂ ptail (aset x y x≡y x≡y′) (prefix-is-prop aset xs<ys xs<ys′)

Prefix< : Set ℓ → Strict-order _ _
Prefix< A = to-strict-order order where
  order : make-strict-order _ (List ⌞ A ⌟)
  order .make-strict-order._<_ = Prefix ⌞ A ⌟
  order .make-strict-order.<-irrefl = prefix-irrefl _
  order .make-strict-order.<-trans = prefix-trans _ _ _
  order .make-strict-order.<-thin = prefix-is-prop (A .is-tr)
  order .make-strict-order.has-is-set = hlevel!
