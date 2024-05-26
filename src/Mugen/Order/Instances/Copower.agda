module Mugen.Order.Instances.Copower where

open import Order.Instances.Discrete

open import Mugen.Prelude
open import Mugen.Order.Instances.Product

Copower : ∀ {o o' r'} → Set o → Poset o' r' → Poset (o ⊔ o') (o ⊔ r')
Copower I A = Product (Discᵢ I) A
