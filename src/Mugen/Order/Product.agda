module Mugen.Order.Product where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

_⊗_[_<_] : ∀ {o r} (A B : StrictOrder o r) → (x y : ⌞ A ⌟ × ⌞ B ⌟) → Type r
A ⊗ B [ a₁ , b₁ < a₂ , b₂ ] = (A [ a₁ < a₂ ]) × (B [ b₁ < b₂ ])

module _ {o r} (A B : StrictOrder o r) where
  module A = StrictOrder-on (structure A)
  module B = StrictOrder-on (structure B)

  ×-irrefl : ∀ (x : ⌞ A ⌟ × ⌞ B ⌟) → A ⊗ B [ x < x ] → ⊥
  ×-irrefl x (a<a , b<b) = A.irrefl a<a

  ×-trans : ∀ (x y z : ⌞ A ⌟ × ⌞ B ⌟) → A ⊗ B [ x < y ] → A ⊗ B [ y < z ] → A ⊗ B [ x < z ]
  ×-trans x y z (a1<a2 , b1<b2) (a2<a3 , b2<b3) = A.trans a1<a2 a2<a3 , B.trans b1<b2 b2<b3

  ×-is-strict-order : is-strict-order (A ⊗ B [_<_])
  ×-is-strict-order .is-strict-order.irrefl {x} = ×-irrefl x
  ×-is-strict-order .is-strict-order.trans {x} {y} {z} = ×-trans x y z
  ×-is-strict-order .is-strict-order.has-prop = ×-is-hlevel 1 A.has-prop B.has-prop
