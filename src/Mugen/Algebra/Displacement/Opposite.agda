module Mugen.Algebra.Displacement.Opposite where

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid

open import Mugen.Order.Opposite
open import Mugen.Order.StrictOrder

module Op {o r} (𝒟 : DisplacementAlgebra o r) where
  open DisplacementAlgebra-on (structure 𝒟)

  _op<_ : ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → Type r
  x op< y = 𝒟 [ y < x ]ᵈ

  _op≤_ : ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → Type (o ⊔ r)
  x op≤ y = 𝒟 [ y ≤ x ]ᵈ

  from-op≤ : ∀ {x y} → x op≤ y → non-strict _op<_ x y
  from-op≤ (inl y≡x) = inl (sym y≡x)
  from-op≤ (inr y<x) = inr y<x

  to-op≤ : ∀ {x y} → non-strict _op<_ x y  → x op≤ y
  to-op≤ (inl x≡y) = inl (sym x≡y)
  to-op≤ (inr y<x) = inr y<x

  op-is-displacement-algebra : is-displacement-algebra _op<_ ε _⊗_
  op-is-displacement-algebra .is-displacement-algebra.has-monoid = has-monoid
  op-is-displacement-algebra .is-displacement-algebra.has-strict-order = op-is-strict-order (DA→SO 𝒟)
  op-is-displacement-algebra .is-displacement-algebra.left-invariant = left-invariant

Op : ∀ {o r} → DisplacementAlgebra o r → DisplacementAlgebra o r
Op {o = o} {r = r} 𝒟 = displacement
  where
    open DisplacementAlgebra 𝒟
    open Op 𝒟

    displacement : DisplacementAlgebra o r
    ⌞ displacement ⌟ =  ⌞ 𝒟 ⌟
    displacement .structure .DisplacementAlgebra-on._<_ = _op<_
    displacement .structure .DisplacementAlgebra-on.ε = ε
    displacement .structure .DisplacementAlgebra-on._⊗_ = _⊗_
    displacement .structure .DisplacementAlgebra-on.has-displacement-algebra = op-is-displacement-algebra
    ⌞ displacement ⌟-set = ⌞ 𝒟 ⌟-set

module OpProperties {o r} {𝒟 : DisplacementAlgebra o r} where
  open DisplacementAlgebra 𝒟
  open Op 𝒟

  op-has-ordered-monoid : has-ordered-monoid 𝒟 → has-ordered-monoid (Op 𝒟)
  op-has-ordered-monoid 𝒟-ordered-monoid = right-invariant→has-ordered-monoid (Op 𝒟) λ y≤x →
    from-op≤ $ right-invariant (to-op≤ y≤x)
    where
      open is-ordered-monoid 𝒟-ordered-monoid
