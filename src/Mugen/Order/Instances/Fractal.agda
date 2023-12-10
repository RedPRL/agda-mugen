module Mugen.Order.Instances.Fractal where

open import Mugen.Prelude
open import Mugen.Data.NonEmpty

import Mugen.Order.Reasoning as Reasoning

private variable
  o r : Level

--------------------------------------------------------------------------------
-- Fractal Posets
-- Section 3.3.7

module _ (A : Poset o r) where
  private
    module A = Reasoning A

  -- The first argument of 'fractal[_][_≤_]' (after being re-exported to the top level)
  -- is the poset A.
  data fractal[_][_≤_] : List⁺ ⌞ A ⌟ → List⁺ ⌞ A ⌟ → Type (o ⊔ r) where
    single≤ : ∀ {x y} → x A.≤ y → fractal[_][_≤_] [ x ] [ y ]
    tail≤' : ∀ {x xs y ys} → x A.≤[ fractal[_][_≤_] xs ys ] y → fractal[_][_≤_] (x ∷ xs) (y ∷ ys)
  pattern tail≤ α β = tail≤' (α , β)

  private
    _≤_ : List⁺ ⌞ A ⌟ → List⁺ ⌞ A ⌟ → Type (o ⊔ r)
    x ≤ y = fractal[_][_≤_] x y

    abstract
      ≤-refl : ∀ (xs : List⁺ ⌞ A ⌟) → xs ≤ xs
      ≤-refl [ x ] = single≤ A.≤-refl
      ≤-refl (x ∷ xs) = tail≤ A.≤-refl λ _ → ≤-refl xs

      ≤-trans : ∀ (xs ys zs : List⁺ ⌞ A ⌟) → xs ≤ ys → ys ≤ zs → xs ≤ zs
      ≤-trans [ x ] [ y ] [ z ] (single≤ x≤y) (single≤ y≤z) = single≤ (A.≤-trans x≤y y≤z)
      ≤-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (tail≤ x≤y xs≤ys) (tail≤ y≤z ys≤zs) =
        tail≤ (A.≤-trans x≤y y≤z) λ x=z →
        ≤-trans xs ys zs (xs≤ys (A.≤-antisym'-l x≤y y≤z x=z)) (ys≤zs (A.≤-antisym'-r x≤y y≤z x=z))

      ≤-antisym : ∀ (xs ys : List⁺ ⌞ A ⌟) → xs ≤ ys → ys ≤ xs → xs ≡ ys
      ≤-antisym [ x ] [ y ] (single≤ x≤y) (single≤ y≤x) = ap [_] $ A.≤-antisym x≤y y≤x
      ≤-antisym (x ∷ xs) (y ∷ ys) (tail≤ x≤y xs≤ys) (tail≤ y≤x ys≤xs) =
        let x=y = A.≤-antisym x≤y y≤x in ap₂ _∷_ x=y $ ≤-antisym xs ys (xs≤ys x=y) (ys≤xs (sym x=y))

      ≤-thin : ∀ (xs ys : List⁺ ⌞ A ⌟) → is-prop (xs ≤ ys)
      ≤-thin [ x ] [ y ] (single≤ x≤y) (single≤ x≤y') = ap single≤ (A.≤-thin x≤y x≤y')
      ≤-thin (x ∷ xs) (y ∷ ys) (tail≤ x≤y xs≤ys) (tail≤ x≤y' xs≤ys') = ap₂ tail≤ (A.≤-thin x≤y x≤y') $
        funext λ p → ≤-thin xs ys (xs≤ys p) (xs≤ys' p)

  --------------------------------------------------------------------------------
  -- Poset Bundle

  Fractal : Poset o (o ⊔ r)
  Fractal = poset where
    poset : Poset o (o ⊔ r)
    poset .Poset.Ob = List⁺ ⌞ A ⌟
    poset .Poset._≤_ = _≤_
    poset .Poset.≤-thin = ≤-thin _ _
    poset .Poset.≤-refl = ≤-refl _
    poset .Poset.≤-trans = ≤-trans _ _ _
    poset .Poset.≤-antisym = ≤-antisym _ _
