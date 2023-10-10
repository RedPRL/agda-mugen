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

--------------------------------------------------------------------------------
-- Misc.

subst₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} (P : A → B → Type ℓ₃) {a1 a2 : A} {b1 b2 : B}
       → a1 ≡ a2 → b1 ≡ b2 → P a1 b1 → P a2 b2
subst₂ P p q x = subst (λ a → P a _) p (subst (λ b → P _ b) q x) 

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
