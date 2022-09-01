module Mugen.Algebra.Displacement.Fractal where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Data.NonEmpty

open import Mugen.Algebra.Displacement
open import Mugen.Order.StrictOrder


data fractal_[_<_] {o r} (𝒟 : DisplacementAlgebra o r) : List⁺ ⌞ 𝒟 ⌟ → List⁺ ⌞ 𝒟 ⌟ → Type (o ⊔ r) where
  single< : ∀ {x y} → 𝒟 [ x < y ]ᵈ → fractal 𝒟 [ [ x ] < [ y ] ]
  head<   : ∀ {x xs y ys} → 𝒟 [ x < y ]ᵈ → fractal 𝒟 [ x ∷ xs < y ∷ ys ]
  -- Annoying hack to work around --without-K
  tail<   : ∀ {x xs y ys} → x ≡ y → fractal 𝒟 [ xs < ys ] → fractal 𝒟 [ x ∷ xs < y ∷ ys ]

module _ {o r} (𝒟 : DisplacementAlgebra o r) where
  private
    module 𝒟 = DisplacementAlgebra-on (structure 𝒟)
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

  ⊗ᶠ-left-invariant : ∀ (xs ys zs : List⁺ ⌞ 𝒟 ⌟) → fractal 𝒟 [ ys < zs ] → fractal 𝒟 [ xs ⊗ᶠ ys < xs ⊗ᶠ zs ]
  ⊗ᶠ-left-invariant [ x ] [ y ] [ z ] (single< y<z) = single< (𝒟.left-invariant y<z)
  ⊗ᶠ-left-invariant [ x ] (y ∷ ys) (z ∷ zs) (head< y<z) = head< (𝒟.left-invariant y<z)
  ⊗ᶠ-left-invariant [ x ] (y ∷ ys) (z ∷ zs) (tail< p ys<zs) = tail< (ap (x ⊗_) p) ys<zs
  ⊗ᶠ-left-invariant (x ∷ xs) [ y ] [ z ] (single< y<z) = head< (𝒟.left-invariant y<z)
  ⊗ᶠ-left-invariant (x ∷ xs) (y ∷ ys) (z ∷ zs) (head< y<z) = head< (𝒟.left-invariant y<z)
  ⊗ᶠ-left-invariant (x ∷ xs) (y ∷ ys) (z ∷ zs) (tail< p ys<zs) = tail< (ap (x ⊗_) p) (⊗ᶠ-left-invariant xs ys zs ys<zs)

  ⊗ᶠ-is-magma : is-magma _⊗ᶠ_
  ⊗ᶠ-is-magma .has-is-set = List⁺-is-hlevel 0 ⌞ 𝒟 ⌟-set

  ⊗ᶠ-is-semigroup : is-semigroup _⊗ᶠ_
  ⊗ᶠ-is-semigroup .has-is-magma = ⊗ᶠ-is-magma
  ⊗ᶠ-is-semigroup .associative {x} {y} {z} = ⊗ᶠ-associative x y z

  ⊗ᶠ-is-monoid : is-monoid εᶠ _⊗ᶠ_
  ⊗ᶠ-is-monoid .has-is-semigroup = ⊗ᶠ-is-semigroup
  ⊗ᶠ-is-monoid .idl {x} = ⊗ᶠ-idl x
  ⊗ᶠ-is-monoid .idr {x} = ⊗ᶠ-idr x

  --------------------------------------------------------------------------------
  -- Order

  <ᶠ-irrefl : ∀ (xs : List⁺ ⌞ 𝒟 ⌟) → fractal 𝒟 [ xs < xs ] → ⊥
  <ᶠ-irrefl [ x ] (single< x<x) = 𝒟.irrefl x<x
  <ᶠ-irrefl (x ∷ xs) (head< x<x) = 𝒟.irrefl x<x
  <ᶠ-irrefl (x ∷ xs) (tail< p xs<xs) = <ᶠ-irrefl xs xs<xs

  <ᶠ-trans : ∀ (xs ys zs : List⁺ ⌞ 𝒟 ⌟) → fractal 𝒟 [ xs < ys ] → fractal 𝒟 [ ys < zs ] → fractal 𝒟 [ xs < zs ]
  <ᶠ-trans [ x ] [ y ] [ z ] (single< x<y) (single< y<z) = single< (𝒟.trans x<y y<z)
  <ᶠ-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (head< x<y) (head< y<z) = head< (𝒟.trans x<y y<z)
  <ᶠ-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (head< x<y) (tail< y≡z ys<zs) = head< (𝒟.≡-transr x<y y≡z)
  <ᶠ-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (tail< x≡y xs<ys) (head< y<z) = head< (𝒟.≡-transl x≡y y<z)
  <ᶠ-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (tail< x≡y xs<ys) (tail< y≡z ys<zs) = tail< (x≡y ∙ y≡z) (<ᶠ-trans xs ys zs xs<ys ys<zs)

  <ᶠ-is-prop : ∀ (xs ys : List⁺ ⌞ 𝒟 ⌟) → is-prop (fractal 𝒟 [ xs < ys ])
  <ᶠ-is-prop [ x ] [ y ] (single< x<y) (single< x<y') = ap single< (𝒟.<-is-prop x<y x<y')
  <ᶠ-is-prop (x ∷ xs) (y ∷ ys) (head< x<y) (head< x<y') = ap head< (𝒟.<-is-prop x<y x<y')
  <ᶠ-is-prop (x ∷ xs) (y ∷ ys) (head< x<y) (tail< x≡y xs<ys) = absurd (𝒟.irrefl (𝒟.≡-transl (sym x≡y) x<y))
  <ᶠ-is-prop (x ∷ xs) (y ∷ ys) (tail< x≡y xs<ys) (head< x<y) = absurd (𝒟.irrefl (𝒟.≡-transl (sym x≡y) x<y))
  <ᶠ-is-prop (x ∷ xs) (y ∷ ys) (tail< x≡y xs<ys) (tail< x≡y' xs<ys') = ap₂ tail< (⌞ 𝒟 ⌟-set x y x≡y x≡y') (<ᶠ-is-prop xs ys xs<ys xs<ys')

  <ᶠ-is-strict-order : is-strict-order fractal 𝒟 [_<_]
  <ᶠ-is-strict-order .is-strict-order.irrefl {x} = <ᶠ-irrefl x
  <ᶠ-is-strict-order .is-strict-order.trans {x} {y} {z} = <ᶠ-trans x y z
  <ᶠ-is-strict-order .is-strict-order.has-prop {x} {y} = <ᶠ-is-prop x y

  --------------------------------------------------------------------------------
  -- Displacement Algebra

  ⊗ᶠ-is-displacement-algebra : is-displacement-algebra (fractal 𝒟 [_<_]) εᶠ _⊗ᶠ_
  ⊗ᶠ-is-displacement-algebra .is-displacement-algebra.has-monoid = ⊗ᶠ-is-monoid
  ⊗ᶠ-is-displacement-algebra .is-displacement-algebra.has-strict-order = <ᶠ-is-strict-order
  ⊗ᶠ-is-displacement-algebra .is-displacement-algebra.left-invariant {x} {y} {z} = ⊗ᶠ-left-invariant x y z
