module Mugen.Order.Opposite where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

op_[_<_] : ∀ {o r} → (A : StrictOrder o r) → ⌞ A ⌟ → ⌞ A ⌟ → Type r
op A [ x < y ] = A [ y < x ]

module _ {o r} (A : StrictOrder o r) where
  open StrictOrder-on (structure A)

  op-irrefl : ∀ (x : ⌞ A ⌟) → op A [ x < x ] → ⊥
  op-irrefl x = irrefl

  op-trans : ∀ (x y z : ⌞ A ⌟) → op A [ x < y ] → op A [ y < z ] → op A [ x < z ]
  op-trans x y z x>y y>z = trans y>z x>y
  
  op-is-strict-order : is-strict-order (op A [_<_])
  op-is-strict-order .is-strict-order.irrefl {x} = op-irrefl x
  op-is-strict-order .is-strict-order.trans {x} {y} {z} = op-trans x y z
  op-is-strict-order .is-strict-order.has-prop = has-prop
