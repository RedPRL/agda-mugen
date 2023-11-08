module Mugen.Axioms.LPO where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

--------------------------------------------------------------------------------
-- Markov's Principle:
--
-- If a predicate on Nat is decidable, and we have a proof that it's not true
-- everywhere on a sequence, then it must be not true /somewhere/ on a sequence.

Markov : ∀ {p} (P : Nat → Type p) → Type p
Markov P = (∀ n → Dec (P n)) → ((∀ n → P n) → ⊥) → ∃[ n ∈ Nat ] (P n → ⊥)

--------------------------------------------------------------------------------
-- The Law of Excluded Middle

LEM : ∀ {ℓ} (A : Type ℓ) → Type ℓ
LEM A = ∥ Dec A ∥

--------------------------------------------------------------------------------
-- The Limited Principle of Omniscience
--
-- When dealing with infinite sequences of ordered values,
-- it's reasonable to ask for 2 sequences 'f g : Nat → A',
-- if '∀ n. f n ≤ g n', then '∃ n. f n < g n' or 'f ≡ g'.
--
-- This is constructively problematic, as doing so would require
-- looking at an infinite amount of information to determine the
-- two sequences are equal.
--
-- This can be shown to arise from the markov principle for pointwise equality
-- of 'f' and 'g', along with LEM for the statement '∀ n → f n ≡ g n'.

module _ {o r} (A : Strict-order o r) (_≡?_ : Discrete ⌞ A ⌟) where
  open Strict-order A

  LPO : Type (o ⊔ r)
  LPO = ∀ {f g : Nat → ⌞ A ⌟} → (∀ n → f n ≤ g n) → f ≡ g ⊎ ∃[ n ∈ Nat ] (f n < g n)

  Markov+LEM→LPO : (∀ (f g : Nat → ⌞ A ⌟) → Markov (λ n → f n ≡ g n))
                 → (∀ (f g : Nat → ⌞ A ⌟) → LEM (∀ n → f n ≡ g n))
                 → LPO
  Markov+LEM→LPO markov lem {f = f} {g = g} p = ∥-∥-rec (disjoint-⊎-is-prop f≡g-is-prop squash disjoint) (λ x → x) $ do
    all-eq? ← lem f g
    pure $ Dec-elim _
      (λ all-eq → inl (funext all-eq))
      (λ ¬all-eq → inr (∥-∥-map (Σ-map₂ (λ {n} fx≠gx → [ (λ fx≡gx → absurd $ fx≠gx fx≡gx) , (λ fx<gx → fx<gx) ] (p n))) $ markov f g (λ n → f n ≡? g n) ¬all-eq))
      all-eq?
    where
      disjoint : (f ≡ g) × ∃[ n ∈ Nat ] (f n < g n) → ⊥
      disjoint (f≡g , ∃fn<gn) = ∥-∥-rec (hlevel 1) (λ { (n , fn<gn) → <-irrefl (≡-transl (sym (happly f≡g n)) fn<gn) }) ∃fn<gn

      f≡g-is-prop : is-prop (f ≡ g)
      f≡g-is-prop p q = is-set→squarep (λ i j → Π-is-hlevel 2 λ n → has-is-set) (λ j → f) p q (λ j → g)
