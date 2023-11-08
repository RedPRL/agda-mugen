module Mugen.Order.Opposite where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

module _ {o r} (A : Strict-order o r) where
  open Strict-order A

  _op<_ : ⌞ A ⌟ → ⌞ A ⌟ → Type r
  x op< y = y < x

  _op≤_ : ⌞ A ⌟ → ⌞ A ⌟ → Type (o ⊔ r)
  x op≤ y = y ≤ x

  from-op≤ : ∀ {x y} → x op≤ y → non-strict _op<_ x y
  from-op≤ (inl y≡x) = inl (sym y≡x)
  from-op≤ (inr y<x) = inr y<x

  to-op≤ : ∀ {x y} → non-strict _op<_ x y  → x op≤ y
  to-op≤ (inl x≡y) = inl (sym x≡y)
  to-op≤ (inr y<x) = inr y<x

  _^opˢ : Strict-order o r
  _^opˢ = to-strict-order order where
    order : make-strict-order _ _
    order .make-strict-order._<_ x y = y < x
    order .make-strict-order.<-irrefl = <-irrefl
    order .make-strict-order.<-trans p q = <-trans q p
    order .make-strict-order.<-thin = <-thin
    order .make-strict-order.has-is-set = has-is-set
