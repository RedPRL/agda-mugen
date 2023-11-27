module Mugen.Order.Opposite where

open import Mugen.Prelude
open import Mugen.Order.Poset

module _ {o r} (A : Poset o r) where
  open Poset A

  _op≤_ : ⌞ A ⌟ → ⌞ A ⌟ → Type r
  x op≤ y = y ≤ x

  _^opˢ : Poset o r
  _^opˢ = to-poset order where
    order : make-poset _ _
    order .make-poset._≤_ x y = y ≤ x
    order .make-poset.≤-refl = ≤-refl
    order .make-poset.≤-trans p q = ≤-trans q p
    order .make-poset.≤-thin = ≤-thin
    order .make-poset.≤-antisym p q = ≤-antisym q p 
