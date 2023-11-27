open import Mugen.Order.Poset
open import Mugen.Prelude

module Mugen.Order.Reasoning {o r} (A : Poset o r) where

open Poset A

{-
infix  1 begin-≤_
infixr 2 step-≤ step-≡
infix  3 _≤∎

data _IsRelatedTo_ : ⌞ A ⌟ → ⌞ A ⌟ → Type (o ⊔ r) where
  done : ∀ x → x IsRelatedTo x
  weak : ∀ x y → x ≤ y → x IsRelatedTo y

begin-≤_ : ∀ {x y} → (x≤y : x IsRelatedTo y) → x ≤ y
begin-≤ done x = ≤-refl
begin-≤ weak x y x≤y = x≤y

step-≤ : ∀ x {y z} → y IsRelatedTo z → x ≤ y → x IsRelatedTo z
step-≤ x (done y) x≤y = weak x y x≤y
step-≤ x (weak y z y≤z) x≤y = weak x z (≤-trans x≤y y≤z)

step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≡ x (done y) p = subst (x IsRelatedTo_) p (done x)
step-≡ x (weak y z y≤z) p = weak x z (subst (_≤ z) (sym p) y≤z)

_≤∎ : ∀ x → x IsRelatedTo x
_≤∎ x = done x

syntax step-≤ x q p = x ≤⟨ p ⟩ q
syntax step-≡ x q p = x ≡̇⟨ p ⟩ q
-}

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
