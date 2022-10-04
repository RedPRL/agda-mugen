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
-- everywhere on a sequence, then it must be not true /somewhere/ on a sequence

Markov : ∀ {p} (P : Nat → Type p) → Type p
Markov P = (∀ n → Dec (P n)) → ((∀ n → P n) → ⊥) → ∃[ n ∈ Nat ] (P n → ⊥)

LEM : ∀ {ℓ} (A : Type ℓ) → Type ℓ
LEM A = ∥ Dec A ∥

module _ {o r} (A : StrictOrder o r) (_≡?_ : Discrete ⌞ A ⌟) where
  open StrictOrder A

  LPO : Type (o ⊔ r)
  LPO = ∀ {f g : Nat → ⌞ A ⌟} → (∀ n → A [ f n ≤ g n ]) → f ≡ g ⊎ ∃[ n ∈ Nat ] (A [ f n < g n ])

  Markov+LEM→LPO : (∀ (f g : Nat → ⌞ A ⌟) → Markov (λ n → f n ≡ g n))
                 → (∀ (f g : Nat → ⌞ A ⌟) → LEM (∀ n → f n ≡ g n))
                 → LPO
  Markov+LEM→LPO markov lem {f = f} {g = g} p = ∥-∥-rec (disjoint-⊎-is-prop f≡g-is-prop squash disjoint) (λ x → x) $ do
    all-eq? ← lem f g
    pure $ case (λ _ → f ≡ g ⊎ ∃[ n ∈ Nat ] (A [ f n < g n ]))
      (λ all-eq → inl (funext all-eq))
      (λ ¬all-eq → inr (∥-∥-map (Σ-map₂ (λ {n} fx≠gx → [ (λ fx≡gx → absurd $ fx≠gx fx≡gx) , (λ fx<gx → fx<gx) ] (p n))) $ markov f g (λ n → f n ≡? g n) ¬all-eq))
      all-eq?
    where
      disjoint : (f ≡ g) × ∃[ n ∈ Nat ] (A [ f n < g n ]) → ⊥
      disjoint (f≡g , ∃fn<gn) = ∥-∥-rec (hlevel 1) (λ { (n , fn<gn) → irrefl (≡-transl (sym (happly f≡g n)) fn<gn) }) ∃fn<gn

      f≡g-is-prop : is-prop (f ≡ g)
      f≡g-is-prop p q = is-set→squarep (λ i j → Π-is-hlevel 2 λ n → ⌞ A ⌟-set) (λ j → f) p q (λ j → g)
