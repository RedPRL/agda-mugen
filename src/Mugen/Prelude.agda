module Mugen.Prelude where

open import Cat.Prelude hiding (injective) public
open import Order.Base hiding (Monotone; hom; pres-≤) public
open import Data.Sum public
open import Data.Dec public

--------------------------------------------------------------------------------
-- The Mugen Prelude
--
-- This exports a bunch of stuff from the 1lab that we use.
-- There's also some misc. junk that we need everywhere.

--------------------------------------------------------------------------------
-- HLevels

instance
  ⊎-hlevel : ∀ {a b} {A : Type a} {B : Type b} {n}
              → ⦃ H-Level A (2 + n) ⦄ → ⦃ H-Level B (2 + n) ⦄
              → H-Level (A ⊎ B) (2 + n)
  ⊎-hlevel {n = n} = hlevel-instance $ ⊎-is-hlevel n

-- Actions

record
  Right-actionlike {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
    ⦃ au : Underlying A ⦄ ⦃ bu : Underlying B ⦄
    (F : A → B → Type ℓ'') : Typeω where
  field
    ⟦_⟧ʳ : ∀ {A B} → F A B → ⌞ A ⌟ → ⌞ B ⌟ → ⌞ A ⌟
    extʳ : ∀ {A B} {f g : F A B} → (∀ {x y} → ⟦ f ⟧ʳ x y ≡ ⟦ g ⟧ʳ x y) → f ≡ g

open Right-actionlike ⦃...⦄ public
