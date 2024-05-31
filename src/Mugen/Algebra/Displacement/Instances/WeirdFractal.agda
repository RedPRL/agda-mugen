module Mugen.Algebra.Displacement.Instances.WeirdFractal where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Data.NonEmpty
open import Mugen.Order.Instances.Fractal

import Mugen.Order.Reasoning as Reasoning

variable
  o r : Level

--------------------------------------------------------------------------------
-- Weird Fractal Displacements from our previous incorrect Agda
-- formalization of Section 3.3.7 of the POPL 2023 paper. They come with
-- a different composition operator. Miraculously, it leads to a valid
-- (but different) displacement algebra.
--
-- The correct fractal displacements are available under
--   Mugen.Algebra.Displacement.Instances.Fractal
--
-- This file was created so that we can further study this "wrong" version
-- of fractal displacements. What is the intuitive explanation of the
-- "wrong" composition operator?

module _ {A : Poset o r} (𝒟 : Displacement-on A) where
  private
    module A = Reasoning A
    module F = Reasoning (Fractal A)
    module 𝒟 = Displacement-on 𝒟

    --------------------------------------------------------------------------------
    -- Algebra

    -- This function is defined differently from the one in Fractal.
    -- What is the intuitive explanation of this operator?
    _⊗_ : List⁺ ⌞ A ⌟ → List⁺ ⌞ A ⌟ → List⁺ ⌞ A ⌟
    [ x ] ⊗ [ y ] = [ x 𝒟.⊗ y ]
    [ x ] ⊗ (y ∷ ys) = (x 𝒟.⊗ y) ∷ ys
    (x ∷ xs) ⊗ [ y ] = (x 𝒟.⊗ y) ∷ xs
    (x ∷ xs) ⊗ (y ∷ ys) = (x 𝒟.⊗ y) ∷ (xs ⊗ ys)

    ε : List⁺ ⌞ A ⌟
    ε = [ 𝒟.ε ]

    abstract
      associative : (xs ys zs : List⁺ ⌞ A ⌟) → (xs ⊗ (ys ⊗ zs)) ≡ ((xs ⊗ ys) ⊗ zs)
      associative [ x ] [ y ] [ z ] = ap [_] 𝒟.associative
      associative [ x ] [ y ] (z ∷ zs) = ap (_∷ zs) 𝒟.associative
      associative [ x ] (y ∷ ys) [ z ] = ap (_∷ ys) 𝒟.associative
      associative [ x ] (y ∷ ys) (z ∷ zs) = ap (_∷ (ys ⊗ zs)) 𝒟.associative
      associative (x ∷ xs) [ y ] [ z ] = ap (_∷ xs) 𝒟.associative
      associative (x ∷ xs) [ y ] (z ∷ zs) = ap (_∷ (xs ⊗ zs)) 𝒟.associative
      associative (x ∷ xs) (y ∷ ys) [ z ] = ap (_∷ (xs ⊗ ys)) 𝒟.associative
      associative (x ∷ xs) (y ∷ ys) (z ∷ zs) = ap₂ _∷_ 𝒟.associative (associative xs ys zs)

      idl : (xs : List⁺ ⌞ A ⌟) → (ε ⊗ xs) ≡ xs
      idl [ x ] = ap [_] 𝒟.idl
      idl (x ∷ xs) = ap (_∷ xs) 𝒟.idl

      idr : (xs : List⁺ ⌞ A ⌟) → (xs ⊗ ε) ≡ xs
      idr [ x ] = ap [_] 𝒟.idr
      idr (x ∷ xs) = ap (_∷ xs) 𝒟.idr

    --------------------------------------------------------------------------------
    -- Left Invariance

    abstract
      left-invariant : (xs ys zs : List⁺ ⌞ A ⌟) → ys F.≤ zs → (xs ⊗ ys) F.≤ (xs ⊗ zs)
      left-invariant [ x ] [ y ] [ z ] (single≤ y≤z) =
        single≤ (𝒟.left-invariant y≤z)
      left-invariant [ x ] (y ∷ ys) (z ∷ zs) (tail≤ y≤z ys≤zs) =
        tail≤ (𝒟.left-invariant y≤z) λ xy=xz → ys≤zs (𝒟.injectiver-on-related y≤z xy=xz)
      left-invariant (x ∷ xs) [ y ] [ z ] (single≤ y≤z) =
        tail≤ (𝒟.left-invariant y≤z) λ _ → F.≤-refl
      left-invariant (x ∷ xs) (y ∷ ys) (z ∷ zs) (tail≤ y≤z ys≤zs) =
        tail≤ (𝒟.left-invariant y≤z) λ xy=xz →
        left-invariant xs ys zs $ ys≤zs (𝒟.injectiver-on-related y≤z xy=xz)

      injectiver-on-related : (xs ys zs : List⁺ ⌞ A ⌟) → ys F.≤ zs → xs ⊗ ys ≡ xs ⊗ zs → ys ≡ zs
      injectiver-on-related [ x ] [ y ] [ z ] (single≤ y≤z) p =
        ap [_] $ 𝒟.injectiver-on-related y≤z $ []-inj p
      injectiver-on-related [ x ] (y ∷ ys) (z ∷ zs) (tail≤ y≤z _) p =
        ap₂ _∷_ (𝒟.injectiver-on-related y≤z (∷-head-inj p)) (∷-tail-inj p)
      injectiver-on-related (x ∷ xs) [ y ] [ z ] (single≤ y≤z) p =
        ap [_] $ 𝒟.injectiver-on-related y≤z (∷-head-inj p)
      injectiver-on-related (x ∷ xs) (y ∷ ys) (z ∷ zs) (tail≤ y≤z ys≤zs) p =
        let y=z = 𝒟.injectiver-on-related y≤z (∷-head-inj p) in
        ap₂ _∷_ y=z (injectiver-on-related xs ys zs (ys≤zs y=z) (∷-tail-inj p))

  --------------------------------------------------------------------------------
  -- Displacement Algebra

  IncorrectFractal-displacement : Displacement-on (Fractal A)
  IncorrectFractal-displacement = to-displacement-on mk where
    mk : make-displacement (Fractal A)
    mk .make-displacement.ε = ε
    mk .make-displacement._⊗_ = _⊗_
    mk .make-displacement.idl = idl _
    mk .make-displacement.idr = idr  _
    mk .make-displacement.associative = associative _ _ _
    mk .make-displacement.left-strict-invariant p =
      left-invariant _ _ _ p , injectiver-on-related _ _ _ p
