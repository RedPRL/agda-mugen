module Mugen.Algebra.Displacement.Instances.Fractal where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Data.NonEmpty
open import Mugen.Order.Instances.Fractal

import Mugen.Order.Reasoning as Reasoning

variable
  o r : Level

--------------------------------------------------------------------------------
-- Fractal Displacements
-- Section 3.3.7

module _ {A : Poset o r} (𝒟 : Displacement-on A) where
  private
    module A = Reasoning A
    module F = Reasoning (Fractal A)
    module 𝒟 = Displacement-on 𝒟

    --------------------------------------------------------------------------------
    -- Algebra

    _⊗_ : List⁺ ⌞ A ⌟ → List⁺ ⌞ A ⌟ → List⁺ ⌞ A ⌟
    [ x ] ⊗ [ y ] = [ x 𝒟.⊗ y ]
    [ x ] ⊗ (y ∷ ys) = (x 𝒟.⊗ y) ∷ ys
    (x ∷ xs) ⊗ ys = x ∷ (xs ⊗ ys)

    ε : List⁺ ⌞ A ⌟
    ε = [ 𝒟.ε ]

    abstract
      associative : (xs ys zs : List⁺ ⌞ A ⌟) → (xs ⊗ (ys ⊗ zs)) ≡ ((xs ⊗ ys) ⊗ zs)
      associative [ x ] [ y ] [ z ] = ap [_] 𝒟.associative
      associative [ x ] [ y ] (z ∷ zs) = ap (_∷ zs) 𝒟.associative
      associative [ x ] (y ∷ ys) zs = refl
      associative (x ∷ xs) ys zs = ap (x ∷_) $ associative xs ys zs

      idl : (xs : List⁺ ⌞ A ⌟) → (ε ⊗ xs) ≡ xs
      idl [ x ] = ap [_] 𝒟.idl
      idl (x ∷ xs) = ap (_∷ xs) 𝒟.idl

      idr : (xs : List⁺ ⌞ A ⌟) → (xs ⊗ ε) ≡ xs
      idr [ x ] = ap [_] 𝒟.idr
      idr (x ∷ xs) = ap (x ∷_) $ idr xs

    --------------------------------------------------------------------------------
    -- Left Invariance

    abstract
      left-invariant : (xs ys zs : List⁺ ⌞ A ⌟) → ys F.≤ zs → (xs ⊗ ys) F.≤ (xs ⊗ zs)
      left-invariant [ x ] [ y ] [ z ] (single≤ y≤z) =
        single≤ (𝒟.left-invariant y≤z)
      left-invariant [ x ] (y ∷ ys) (z ∷ zs) (tail≤ y≤z ys≤zs) =
        tail≤ (𝒟.left-invariant y≤z) λ xy=xz → ys≤zs (𝒟.injectiver-on-related y≤z xy=xz)
      left-invariant (x ∷ xs) ys zs ys≤zs =
        tail≤ A.≤-refl λ _ → left-invariant xs ys zs ys≤zs

      injectiver-on-related : (xs ys zs : List⁺ ⌞ A ⌟) → ys F.≤ zs → xs ⊗ ys ≡ xs ⊗ zs → ys ≡ zs
      injectiver-on-related [ x ] [ y ] [ z ] (single≤ y≤z) p =
        ap [_] $ 𝒟.injectiver-on-related y≤z $ []-inj p
      injectiver-on-related [ x ] (y ∷ ys) (z ∷ zs) (tail≤ y≤z _) p =
        ap₂ _∷_ (𝒟.injectiver-on-related y≤z (∷-head-inj p)) (∷-tail-inj p)
      injectiver-on-related (x ∷ xs) ys zs ys≤zs p =
        injectiver-on-related xs ys zs ys≤zs (∷-tail-inj p)

  --------------------------------------------------------------------------------
  -- Displacement Algebra

  Fractal-displacement : Displacement-on (Fractal A)
  Fractal-displacement = to-displacement-on mk where
    mk : make-displacement (Fractal A)
    mk .make-displacement.ε = ε
    mk .make-displacement._⊗_ = _⊗_
    mk .make-displacement.idl = idl _
    mk .make-displacement.idr = idr  _
    mk .make-displacement.associative = associative _ _ _
    mk .make-displacement.left-strict-invariant p =
      left-invariant _ _ _ p , injectiver-on-related _ _ _ p
