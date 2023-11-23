module Mugen.Algebra.Displacement.Fractal where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Data.NonEmpty

open import Mugen.Algebra.Displacement
open import Mugen.Order.StrictOrder

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
  (x ∷ xs) ⊗ᶠ [ y ] = (x ⊗ y) ∷ xs
  (x ∷ xs) ⊗ᶠ (y ∷ ys) = (x ⊗ y) ∷ (xs ⊗ᶠ ys)

  εᶠ : List⁺ ⌞ 𝒟 ⌟
  εᶠ = [ ε ]

  ⊗ᶠ-associative : (xs ys zs : List⁺ ⌞ 𝒟 ⌟) → (xs ⊗ᶠ (ys ⊗ᶠ zs)) ≡ ((xs ⊗ᶠ ys) ⊗ᶠ zs)
  ⊗ᶠ-associative [ x ] [ y ] [ z ] = ap [_] 𝒟.associative
  ⊗ᶠ-associative [ x ] [ y ] (z ∷ zs) = ap (_∷ zs) 𝒟.associative
  ⊗ᶠ-associative [ x ] (y ∷ ys) [ z ] = ap (_∷ ys) 𝒟.associative
  ⊗ᶠ-associative [ x ] (y ∷ ys) (z ∷ zs) = ap (_∷ (ys ⊗ᶠ zs)) 𝒟.associative
  ⊗ᶠ-associative (x ∷ xs) [ y ] [ z ] = ap (_∷ xs) 𝒟.associative
  ⊗ᶠ-associative (x ∷ xs) [ y ] (z ∷ zs) = ap (_∷ (xs ⊗ᶠ zs)) 𝒟.associative
  ⊗ᶠ-associative (x ∷ xs) (y ∷ ys) [ z ] = ap (_∷ (xs ⊗ᶠ ys)) 𝒟.associative
  ⊗ᶠ-associative (x ∷ xs) (y ∷ ys) (z ∷ zs) = ap₂ _∷_ 𝒟.associative (⊗ᶠ-associative xs ys zs)

  ⊗ᶠ-idl : ∀ (xs : List⁺ ⌞ 𝒟 ⌟) → (εᶠ ⊗ᶠ xs) ≡ xs
  ⊗ᶠ-idl [ x ] = ap [_] 𝒟.idl
  ⊗ᶠ-idl (x ∷ xs) = ap (_∷ xs) 𝒟.idl

  ⊗ᶠ-idr : ∀ (xs : List⁺ ⌞ 𝒟 ⌟) → (xs ⊗ᶠ εᶠ) ≡ xs
  ⊗ᶠ-idr [ x ] = ap [_] 𝒟.idr
  ⊗ᶠ-idr (x ∷ xs) = ap (_∷ xs) 𝒟.idr

  --------------------------------------------------------------------------------
  -- Order

  data fractal[_<_] : List⁺ ⌞ 𝒟 ⌟ → List⁺ ⌞ 𝒟 ⌟ → Type (o ⊔ r) where
    single< : ∀ {x y} → x 𝒟.< y → fractal[ [ x ] < [ y ] ]
    head<   : ∀ {x xs y ys} → x 𝒟.< y → fractal[ x ∷ xs < y ∷ ys ]
    -- Annoying hack to work around --without-K
    tail<   : ∀ {x xs y ys} → x ≡ y → fractal[ xs < ys ] → fractal[ x ∷ xs < y ∷ ys ]

  <ᶠ-irrefl : ∀ (xs : List⁺ ⌞ 𝒟 ⌟) → fractal[ xs < xs ] → ⊥
  <ᶠ-irrefl [ x ] (single< x<x) = 𝒟.<-irrefl x<x
  <ᶠ-irrefl (x ∷ xs) (head< x<x) = 𝒟.<-irrefl x<x
  <ᶠ-irrefl (x ∷ xs) (tail< p xs<xs) = <ᶠ-irrefl xs xs<xs

  <ᶠ-trans : ∀ (xs ys zs : List⁺ ⌞ 𝒟 ⌟) → fractal[ xs < ys ] → fractal[ ys < zs ] → fractal[ xs < zs ]
  <ᶠ-trans [ x ] [ y ] [ z ] (single< x<y) (single< y<z) = single< (𝒟.<-trans x<y y<z)
  <ᶠ-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (head< x<y) (head< y<z) = head< (𝒟.<-trans x<y y<z)
  <ᶠ-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (head< x<y) (tail< y≡z ys<zs) = head< (𝒟.<+≡→< x<y y≡z)
  <ᶠ-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (tail< x≡y xs<ys) (head< y<z) = head< (𝒟.≡+<→< x≡y y<z)
  <ᶠ-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (tail< x≡y xs<ys) (tail< y≡z ys<zs) = tail< (x≡y ∙ y≡z) (<ᶠ-trans xs ys zs xs<ys ys<zs)

  <ᶠ-is-prop : ∀ (xs ys : List⁺ ⌞ 𝒟 ⌟) → is-prop (fractal[ xs < ys ])
  <ᶠ-is-prop [ x ] [ y ] (single< x<y) (single< x<y') = ap single< (𝒟.<-thin x<y x<y')
  <ᶠ-is-prop (x ∷ xs) (y ∷ ys) (head< x<y) (head< x<y') = ap head< (𝒟.<-thin x<y x<y')
  <ᶠ-is-prop (x ∷ xs) (y ∷ ys) (head< x<y) (tail< x≡y xs<ys) = absurd (𝒟.<-irrefl (𝒟.≡+<→< (sym x≡y) x<y))
  <ᶠ-is-prop (x ∷ xs) (y ∷ ys) (tail< x≡y xs<ys) (head< x<y) = absurd (𝒟.<-irrefl (𝒟.≡+<→< (sym x≡y) x<y))
  <ᶠ-is-prop (x ∷ xs) (y ∷ ys) (tail< x≡y xs<ys) (tail< x≡y' xs<ys') = ap₂ tail< (𝒟.has-is-set x y x≡y x≡y') (<ᶠ-is-prop xs ys xs<ys xs<ys')

  --------------------------------------------------------------------------------
  -- Left Invariance

  ⊗ᶠ-left-invariant : ∀ (xs ys zs : List⁺ ⌞ 𝒟 ⌟) → fractal[ ys < zs ] → fractal[ xs ⊗ᶠ ys < xs ⊗ᶠ zs ]
  ⊗ᶠ-left-invariant [ x ] [ y ] [ z ] (single< y<z) = single< (𝒟.left-invariant y<z)
  ⊗ᶠ-left-invariant [ x ] (y ∷ ys) (z ∷ zs) (head< y<z) = head< (𝒟.left-invariant y<z)
  ⊗ᶠ-left-invariant [ x ] (y ∷ ys) (z ∷ zs) (tail< p ys<zs) = tail< (ap (x ⊗_) p) ys<zs
  ⊗ᶠ-left-invariant (x ∷ xs) [ y ] [ z ] (single< y<z) = head< (𝒟.left-invariant y<z)
  ⊗ᶠ-left-invariant (x ∷ xs) (y ∷ ys) (z ∷ zs) (head< y<z) = head< (𝒟.left-invariant y<z)
  ⊗ᶠ-left-invariant (x ∷ xs) (y ∷ ys) (z ∷ zs) (tail< p ys<zs) = tail< (ap (x ⊗_) p) (⊗ᶠ-left-invariant xs ys zs ys<zs)

  --------------------------------------------------------------------------------
  -- Displacement Algebra

  Fractal : Displacement-algebra o (o ⊔ r)
  Fractal = to-displacement-algebra mk where
    mk-strict : make-strict-order (o ⊔ r) (List⁺ ⌞ 𝒟 ⌟)
    mk-strict .make-strict-order._<_ = fractal[_<_]
    mk-strict .make-strict-order.<-irrefl = <ᶠ-irrefl _
    mk-strict .make-strict-order.<-trans = <ᶠ-trans _ _ _
    mk-strict .make-strict-order.<-thin = <ᶠ-is-prop _ _
    mk-strict .make-strict-order.has-is-set = List⁺-is-hlevel 0 𝒟.has-is-set

    mk : make-displacement-algebra (to-strict-order mk-strict)
    mk .make-displacement-algebra.ε = εᶠ
    mk .make-displacement-algebra._⊗_ = _⊗ᶠ_
    mk .make-displacement-algebra.idl = ⊗ᶠ-idl _
    mk .make-displacement-algebra.idr = ⊗ᶠ-idr  _
    mk .make-displacement-algebra.associative = ⊗ᶠ-associative _ _ _
    mk .make-displacement-algebra.left-invariant = ⊗ᶠ-left-invariant _ _ _
