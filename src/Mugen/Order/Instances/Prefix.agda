module Mugen.Order.Instances.Prefix where

open import Data.List
open import Mugen.Order.Lattice

open import Mugen.Prelude

private variable
  o : Level
  A : Type o

module _ where

  data Prefix[_≤_] {A : Type o} : List A → List A → Type o where
    pre[] : ∀ {xs} → Prefix[ [] ≤ xs ]
    -- '_pre∷_' is taking the extra argument of type 'x ≡ y' to work around --without-K
    _pre∷_ : ∀ {x y xs ys} → x ≡ y → Prefix[ xs ≤ ys ] → Prefix[ (x ∷ xs) ≤ (y ∷ ys) ]

  private abstract
    prefix-refl : (xs : List A) → Prefix[ xs ≤ xs ]
    prefix-refl [] = pre[]
    prefix-refl (x ∷ xs) = refl pre∷ prefix-refl xs

    prefix-trans : (xs ys zs : List A) → Prefix[ xs ≤ ys ] → Prefix[ ys ≤ zs ] → Prefix[ xs ≤ zs ]
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

  Prefix : Set o → Poset o o
  Prefix A .Poset.Ob = List ⌞ A ⌟
  Prefix A .Poset._≤_ = Prefix[_≤_]
  Prefix A .Poset.≤-thin = prefix-is-prop (A .is-tr)
  Prefix A .Poset.≤-refl = prefix-refl _
  Prefix A .Poset.≤-trans = prefix-trans _ _ _
  Prefix A .Poset.≤-antisym = prefix-antisym _ _

  --------------------------------------------------------------------------------
  -- Bottoms

  Prefix-has-bottom : {A : Set o} → has-bottom (Prefix A)
  Prefix-has-bottom .has-bottom.bot = []
  Prefix-has-bottom .has-bottom.is-bottom = pre[]
