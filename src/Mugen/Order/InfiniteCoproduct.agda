module Mugen.Order.InfiniteCoproduct where

open import 1Lab.Type.Sigma

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

module InfiniteCoproduct {o r ℓ} {I : Type ℓ} (I-discrete : Discrete I) (Δᵢ : I → StrictOrder o r) where

  open StrictOrder

  -- If we don't have K, this is the best bet... Brutal!
  _⨆<_ : Σ[ ix ∈ I ] ⌞ Δᵢ ix ⌟ → Σ[ ix ∈ I ] ⌞ Δᵢ ix ⌟ → Type r
  (i , x) ⨆< (j , y) with I-discrete i j
  ... | yes i≡j = Δᵢ j [ subst (λ ϕ → ⌞ Δᵢ ϕ ⌟) i≡j x < y ]
  ... | no ¬i≡j = Lift _ ⊥

  -- ⨆<-irrefl : ∀ x → x ⨆< x → ⊥
  -- ⨆<-irrefl (i , x) x<x with I-discrete i i
  -- ... | yes i≡i = Δᵢ i .irrefl (subst (λ ϕ → Δᵢ i [ ϕ < x ]) (transport-refl x) {!x<x!})
  -- -- (subst (λ ϕ → Δᵢ i [ subst (λ ψ → ⌞ Δᵢ ψ ⌟) ϕ x < x ]) (transport-refl i≡i) {!!})
  -- ... | no ¬i≡i = Lift.lower x<x
