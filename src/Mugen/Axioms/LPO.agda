module Mugen.Axioms.LPO where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

--------------------------------------------------------------------------------
-- The Law of Excluded Middle

LEM : ∀ {ℓ} (A : Type ℓ) → Type ℓ
LEM A = ∥ Dec A ∥

--------------------------------------------------------------------------------
-- The Weak Limited Principle of Omniscience

module _ {o r} (A : Strict-order o r) (_≡?_ : Discrete ⌞ A ⌟) where
  open Strict-order A

  WLPO : Type (o ⊔ r)
  WLPO = ∀ {f g : Nat → ⌞ A ⌟} → (∀ n → f n ≤ g n) → Dec (∀ n → f n ≡ g n)

  LEM→WLPO : (∀ (f g : Nat → ⌞ A ⌟) → LEM (∀ n → f n ≡ g n)) → WLPO
  LEM→WLPO lem {f = f} {g = g} _ =
    ∥-∥-proj (Dec-is-hlevel 0 $ Π-is-hlevel 1 λ n → has-is-set (f n) (g n)) (lem f g)
