module Mugen.Algebra.Displacement.Fractal where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Data.NonEmpty
open import Mugen.Order.Poset

--------------------------------------------------------------------------------
-- Fractal Displacements
-- Section 3.3.7

module _
  {o r} (𝒟 : Displacement-algebra o r)
  where
  private
    module 𝒟 = Displacement-algebra 𝒟
    open 𝒟 using (ε; _⊗_)

  --------------------------------------------------------------------------------
  -- Algebra

  _⊗ᶠ_ : List⁺ ⌞ 𝒟 ⌟ → List⁺ ⌞ 𝒟 ⌟ → List⁺ ⌞ 𝒟 ⌟
  [ x ] ⊗ᶠ [ y ] = [ x ⊗ y ]
  [ x ] ⊗ᶠ (y ∷ ys) = (x ⊗ y) ∷ ys
  (x ∷ xs) ⊗ᶠ ys = x ∷ (xs ⊗ᶠ ys)

  εᶠ : List⁺ ⌞ 𝒟 ⌟
  εᶠ = [ ε ]

  ⊗ᶠ-associative : (xs ys zs : List⁺ ⌞ 𝒟 ⌟) → (xs ⊗ᶠ (ys ⊗ᶠ zs)) ≡ ((xs ⊗ᶠ ys) ⊗ᶠ zs)
  ⊗ᶠ-associative [ x ] [ y ] [ z ] = ap [_] 𝒟.associative
  ⊗ᶠ-associative [ x ] [ y ] (z ∷ zs) = ap (_∷ zs) 𝒟.associative
  ⊗ᶠ-associative [ x ] (y ∷ ys) zs = refl
  ⊗ᶠ-associative (x ∷ xs) ys zs = ap (x ∷_) $ ⊗ᶠ-associative xs ys zs

  ⊗ᶠ-idl : ∀ (xs : List⁺ ⌞ 𝒟 ⌟) → (εᶠ ⊗ᶠ xs) ≡ xs
  ⊗ᶠ-idl [ x ] = ap [_] 𝒟.idl
  ⊗ᶠ-idl (x ∷ xs) = ap (_∷ xs) 𝒟.idl

  ⊗ᶠ-idr : ∀ (xs : List⁺ ⌞ 𝒟 ⌟) → (xs ⊗ᶠ εᶠ) ≡ xs
  ⊗ᶠ-idr [ x ] = ap [_] 𝒟.idr
  ⊗ᶠ-idr (x ∷ xs) = ap (x ∷_) $ ⊗ᶠ-idr xs

  --------------------------------------------------------------------------------
  -- Order

  data fractal[_≤_] : List⁺ ⌞ 𝒟 ⌟ → List⁺ ⌞ 𝒟 ⌟ → Type (o ⊔ r) where
    single≤ : ∀ {x y} → x 𝒟.≤ y → fractal[ [ x ] ≤ [ y ] ]
    tail≤   : ∀ {x xs y ys} → x 𝒟.≤ y → (x ≡ y → fractal[ xs ≤ ys ]) → fractal[ x ∷ xs ≤ y ∷ ys ]

  ≤ᶠ-refl : ∀ (xs : List⁺ ⌞ 𝒟 ⌟) → fractal[ xs ≤ xs ]
  ≤ᶠ-refl [ x ] = single≤ 𝒟.≤-refl
  ≤ᶠ-refl (x ∷ xs) = tail≤ 𝒟.≤-refl λ _ → ≤ᶠ-refl xs

  ≤ᶠ-trans : ∀ (xs ys zs : List⁺ ⌞ 𝒟 ⌟) → fractal[ xs ≤ ys ] → fractal[ ys ≤ zs ] → fractal[ xs ≤ zs ]
  ≤ᶠ-trans [ x ] [ y ] [ z ] (single≤ x≤y) (single≤ y≤z) = single≤ (𝒟.≤-trans x≤y y≤z)
  ≤ᶠ-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (tail≤ x≤y xs≤ys) (tail≤ y≤z ys≤zs) =
    tail≤ (𝒟.≤-trans x≤y y≤z) λ x=z →
    ≤ᶠ-trans xs ys zs (xs≤ys (𝒟.≤-antisym'-l x≤y y≤z x=z)) (ys≤zs (𝒟.≤-antisym'-r x≤y y≤z x=z))

  ≤ᶠ-antisym : ∀ (xs ys : List⁺ ⌞ 𝒟 ⌟) → fractal[ xs ≤ ys ] → fractal[ ys ≤ xs ] → xs ≡ ys
  ≤ᶠ-antisym [ x ] [ y ] (single≤ x≤y) (single≤ y≤x) = ap [_] $ 𝒟.≤-antisym x≤y y≤x
  ≤ᶠ-antisym (x ∷ xs) (y ∷ ys) (tail≤ x≤y xs≤ys) (tail≤ y≤x ys≤xs) =
    let x=y = 𝒟.≤-antisym x≤y y≤x in ap₂ _∷_ x=y $ ≤ᶠ-antisym xs ys (xs≤ys x=y) (ys≤xs (sym x=y))

  ≤ᶠ-thin : ∀ (xs ys : List⁺ ⌞ 𝒟 ⌟) → is-prop (fractal[ xs ≤ ys ])
  ≤ᶠ-thin [ x ] [ y ] (single≤ x≤y) (single≤ x≤y') = ap single≤ (𝒟.≤-thin x≤y x≤y')
  ≤ᶠ-thin (x ∷ xs) (y ∷ ys) (tail≤ x≤y xs≤ys) (tail≤ x≤y' xs≤ys') = ap₂ tail≤ (𝒟.≤-thin x≤y x≤y') $
    funext λ p → ≤ᶠ-thin xs ys (xs≤ys p) (xs≤ys' p)

  --------------------------------------------------------------------------------
  -- Left Invariance

  ⊗ᶠ-left-invariant : ∀ (xs ys zs : List⁺ ⌞ 𝒟 ⌟) → fractal[ ys ≤ zs ] → fractal[ xs ⊗ᶠ ys ≤ xs ⊗ᶠ zs ]
  ⊗ᶠ-left-invariant [ x ] [ y ] [ z ] (single≤ y≤z) =
    single≤ (𝒟.left-invariant y≤z)
  ⊗ᶠ-left-invariant [ x ] (y ∷ ys) (z ∷ zs) (tail≤ y≤z ys≤zs) =
    tail≤ (𝒟.left-invariant y≤z) λ xy=xz → ys≤zs (𝒟.injr-on-related y≤z xy=xz)
  ⊗ᶠ-left-invariant (x ∷ xs) ys zs ys≤zs =
    tail≤ 𝒟.≤-refl λ _ → ⊗ᶠ-left-invariant xs ys zs ys≤zs

  ⊗ᶠ-injr-on-≤ : ∀ (xs ys zs : List⁺ ⌞ 𝒟 ⌟) → fractal[ ys ≤ zs ] → xs ⊗ᶠ ys ≡ xs ⊗ᶠ zs → ys ≡ zs
  ⊗ᶠ-injr-on-≤ [ x ] [ y ] [ z ] (single≤ y≤z) p =
    ap [_] $ 𝒟.injr-on-related y≤z $ []-inj p
  ⊗ᶠ-injr-on-≤ [ x ] (y ∷ ys) (z ∷ zs) (tail≤ y≤z _) p =
    ap₂ _∷_ (𝒟.injr-on-related y≤z (∷-head-inj p)) (∷-tail-inj p)
  ⊗ᶠ-injr-on-≤ (x ∷ xs) ys zs ys≤zs p =
    ⊗ᶠ-injr-on-≤ xs ys zs ys≤zs (∷-tail-inj p)

  --------------------------------------------------------------------------------
  -- Displacement Algebra

  Fractal : Displacement-algebra o (o ⊔ r)
  Fractal = to-displacement-algebra mk where
    mk-poset : make-poset (o ⊔ r) (List⁺ ⌞ 𝒟 ⌟)
    mk-poset .make-poset._≤_ = fractal[_≤_]
    mk-poset .make-poset.≤-thin = ≤ᶠ-thin _ _
    mk-poset .make-poset.≤-refl = ≤ᶠ-refl _
    mk-poset .make-poset.≤-trans = ≤ᶠ-trans _ _ _
    mk-poset .make-poset.≤-antisym = ≤ᶠ-antisym _ _

    mk : make-displacement-algebra (to-poset mk-poset)
    mk .make-displacement-algebra.ε = εᶠ
    mk .make-displacement-algebra._⊗_ = _⊗ᶠ_
    mk .make-displacement-algebra.idl = ⊗ᶠ-idl _
    mk .make-displacement-algebra.idr = ⊗ᶠ-idr  _
    mk .make-displacement-algebra.associative = ⊗ᶠ-associative _ _ _
    mk .make-displacement-algebra.left-strict-invariant p =
      ⊗ᶠ-left-invariant _ _ _ p , ⊗ᶠ-injr-on-≤ _ _ _ p
