open import Mugen.Order.StrictOrder
open import Mugen.Prelude

module Mugen.Order.StrictOrder.Reasoning {o r} (A : Strict-order o r) where

open Strict-order A public

infix  1 begin-<_ begin-≤_
infixr 2 step-< step-≤ step-≡
infix  3 _<∎

data _IsRelatedTo_ : ⌞ A ⌟ → ⌞ A ⌟ → Type (o ⊔ r) where
  done : ∀ x → x IsRelatedTo x
  strong : ∀ x y → x < y → x IsRelatedTo y
  weak : ∀ x y → x ≤ y → x IsRelatedTo y

Strong : ∀ {x y} → x IsRelatedTo y → Type
Strong (done _) = ⊥
Strong (strong _ _ _) = ⊤
Strong (weak _ _ _) = ⊥

begin-<_ : ∀ {x y} → (x<y : x IsRelatedTo y) → {Strong x<y} → x < y
begin-< (strong _ _ x<y) = x<y

begin-≤_ : ∀ {x y} → (x≤y : x IsRelatedTo y) → x ≤ y
begin-≤ done x = inl refl
begin-≤ strong x y x<y = inr x<y
begin-≤ weak x y x≤y = x≤y

step-< : ∀ x {y z} → y IsRelatedTo z → x < y → x IsRelatedTo z
step-< x (done y) x<y = strong x y x<y
step-< x (strong y z y<z) x<y = strong x z (<-trans x<y y<z)
step-< x (weak y z y≤z) x<y = strong x z (<+≤→< x<y y≤z)

step-≤ : ∀ x {y z} → y IsRelatedTo z → x ≤ y → x IsRelatedTo z
step-≤ x (done y) x≤y = weak x y x≤y
step-≤ x (strong y z y<z) x≤y = strong x z (≤+<→< x≤y y<z)
step-≤ x (weak y z y≤z) x≤y = weak x z (≤-trans x≤y y≤z)

step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≡ x (done y) p = subst (x IsRelatedTo_) p (done x)
step-≡ x (strong y z y<z) p = strong x z (subst (_< z) (sym p) y<z)
step-≡ x (weak y z y≤z) p = weak x z (subst (_≤ z) (sym p) y≤z)

_<∎ : ∀ x → x IsRelatedTo x
_<∎ x = done x

syntax step-< x q p = x <⟨ p ⟩ q
syntax step-≤ x q p = x ≤⟨ p ⟩ q
syntax step-≡ x q p = x ≡̇⟨ p ⟩ q
