module Mugen.Order.Prefix where

open import Data.List

open import Mugen.Prelude
open import Mugen.Order.Poset

data Prefix[_≤_] {ℓ} {A : Type ℓ} : List A → List A → Type ℓ where
  pre[]  : ∀ {xs} → Prefix[ [] ≤ xs ]
  -- Taking the extra argument of type 'x ≡ y' to work around --without-K
  _pre∷_ : ∀ {x y xs ys} → x ≡ y → Prefix[ xs ≤ ys ] → Prefix[ (x ∷ xs) ≤ (y ∷ ys) ]

private variable
  ℓ : Level
  A : Type ℓ

prefix-refl : ∀ (xs : List A) → Prefix[ xs ≤ xs ]
prefix-refl [] = pre[]
prefix-refl (x ∷ xs) = refl pre∷ prefix-refl xs

prefix-trans : ∀ (xs ys zs : List A) → Prefix[ xs ≤ ys ] → Prefix[ ys ≤ zs ] → Prefix[ xs ≤ zs ]
prefix-trans _ _ _ pre[] _ = pre[]
prefix-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (x≡y pre∷ xs≤ys) (y≡z pre∷ ys≤zs) =
  (x≡y ∙ y≡z) pre∷ (prefix-trans xs ys zs xs≤ys ys≤zs)

prefix-antisym : ∀ (xs ys : List A) → Prefix[ xs ≤ ys ] → Prefix[ ys ≤ xs ] → xs ≡ ys
prefix-antisym _ _ pre[] pre[] = refl
prefix-antisym (x ∷ xs) (y ∷ ys) (x≡y pre∷ xs≤ys) (y≡x pre∷ ys≤xs) =
  ap₂ _∷_ x≡y (prefix-antisym xs ys xs≤ys ys≤xs)

prefix-is-prop : ∀ {xs ys : List A} → is-set A → is-prop (Prefix[ xs ≤ ys ])
prefix-is-prop {xs = []} aset pre[] pre[] = refl
prefix-is-prop {xs = x ∷ xs} {ys = y ∷ ys} aset (x≡y pre∷ xs<ys) (x≡y′ pre∷ xs<ys′) =
  ap₂ _pre∷_ (aset x y x≡y x≡y′) (prefix-is-prop aset xs<ys xs<ys′)

Prefix≤ : Set ℓ → Poset _ _
Prefix≤ A = to-poset order where
  order : make-poset _ (List ⌞ A ⌟)
  order .make-poset._≤_ = Prefix[_≤_]
  order .make-poset.≤-thin = prefix-is-prop (A .is-tr)
  order .make-poset.≤-refl = prefix-refl _
  order .make-poset.≤-trans = prefix-trans _ _ _
  order .make-poset.≤-antisym = prefix-antisym _ _
