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
  ⊎-hlevel {n = n} = hlevel-instance $ ⊎-is-hlevel _ (hlevel (2 + n)) (hlevel (2 + n))

--------------------------------------------------------------------------------
-- Decidability

dec-map : ∀ {ℓ ℓ′} {P : Type ℓ} {Q : Type ℓ′} → (P → Q) → (Q → P) → Dec P → Dec Q
dec-map to from (yes p) = yes (to p)
dec-map to from (no ¬p) = no (λ q → ¬p (from q))

--------------------------------------------------------------------------------
-- Actions

record
  Right-actionlike {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
    ⦃ au : Underlying A ⦄ ⦃ bu : Underlying B ⦄
    (F : A → B → Type ℓ'') : Typeω where
  field
    ⟦_⟧ʳ : ∀ {A B} → F A B → ⌞ A ⌟ → ⌞ B ⌟ → ⌞ A ⌟
    extʳ : ∀ {A B} {f g : F A B} → (∀ {x y} → ⟦ f ⟧ʳ x y ≡ ⟦ g ⟧ʳ x y) → f ≡ g

open Right-actionlike ⦃...⦄ public

--------------------------------------------------------------------------------
-- Misc.

infixr -1 _|>_

_|>_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} → (x : A) → ((x : A) → B x) → B x
x |> f = f x
{-# INLINE _|>_ #-}

over : ∀ {ℓ} {A : Type ℓ} {x y : A} {f : A → A} → (∀ x → f x ≡ x) → f x ≡ f y → x ≡ y
over {x = x} {y = y} p q =  sym (p x) ·· q ·· p y

--------------------------------------------------------------------------------
-- This lemma should probably be put into 1lab
identity-system-hlevel
  : ∀ {ℓ ℓ'} {A : Type ℓ} n {R : A → A → Type ℓ'} {r : ∀ x → R x x}
  → is-identity-system R r
  → is-hlevel A (suc n)
  → ∀ {x y : A} → is-hlevel (R x y) n
identity-system-hlevel n ids hl {x} {y} =
  Equiv→is-hlevel n (identity-system-gives-path ids) (Path-is-hlevel' n hl x y)
