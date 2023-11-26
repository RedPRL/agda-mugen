module Mugen.Prelude where

open import Cat.Prelude public
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

record
  Right-actionlike {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
    ⦃ au : Underlying A ⦄ ⦃ bu : Underlying B ⦄
    (F : A → B → Type ℓ'') : Typeω where
  field
    ⟦_⟧ʳ : ∀ {A B} → F A B → ⌞ A ⌟ → ⌞ B ⌟ → ⌞ A ⌟
    extʳ : ∀ {A B} {f g : F A B} → (∀ x y → ⟦ f ⟧ʳ x y ≡ ⟦ g ⟧ʳ x y) → f ≡ g

open Right-actionlike ⦃...⦄ public

--------------------------------------------------------------------------------
-- Misc.

subst₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} (P : A → B → Type ℓ₃) {a1 a2 : A} {b1 b2 : B}
       → a1 ≡ a2 → b1 ≡ b2 → P a1 b1 → P a2 b2
subst₂ P p q x = coe0→1 (λ i → P (p i) (q i)) x

record Reveal_·_is_ {a b} {A : Type a} {B : A → Type b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Type (a ⊔ b) where
  constructor evidence
  field eq : f x ≡ y

remember : ∀ {a b} {A : Type a} {B : A → Type b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
remember f x = evidence refl

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
  is-hlevel≃ n (identity-system-gives-path ids) (Path-is-hlevel' n hl x y)
