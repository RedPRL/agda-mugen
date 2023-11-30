open import Mugen.Order.Poset
open import Mugen.Prelude

module Mugen.Order.Reasoning {o r} (A : Poset o r) where

open Poset A

infixr 2 step-≤ step-≡
infix  3 _≤∎

step-≤ : ∀ x {y z} → y ≤ z → x ≤ y → x ≤ z
step-≤ x y≤z x≤y = ≤-trans x≤y y≤z

step-≡ : ∀ x {y z} → y ≤ z → x ≡ y → x ≤ z
step-≡ x y≤z x=y = =+≤→≤ x=y y≤z

_≤∎ : ∀ x → x ≤ x
_≤∎ x = ≤-refl

syntax step-≤ x q p = x ≤⟨ p ⟩ q
syntax step-≡ x q p = x ≐⟨ p ⟩ q
