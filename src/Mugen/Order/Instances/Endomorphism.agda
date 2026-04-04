module Mugen.Order.Instances.Endomorphism where

open import Cat.Diagram.Monad
open import Cat.Displayed.Total using (∫Hom)
import Cat.Reasoning as Cat

open import Mugen.Prelude

open import Mugen.Order.StrictOrder
open import Mugen.Cat.Monad
open import Mugen.Cat.Instances.StrictOrders

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- Endomorphism Posets
-- Section 3.4
--
-- Given a Monad 'H' on the category of strict orders, we can construct a poset
-- whose carrier set is the set of endomorphisms 'Free H Δ → Free H Δ' between
-- free H-algebras in the Eilenberg-Moore category.
module _ {F : Functor (Strict-orders o r) (Strict-orders o r)} (H : Monad-on F) (Δ : Poset o r) where

  open Monad-on H renaming (M₀ to H₀; M₁ to H₁)
  open Cat (Eilenberg-Moore H)

  private
    module H⟨Δ⟩ = Reasoning (H₀ Δ)

    Fᴴ⟨Δ⟩ : Algebra H
    Fᴴ⟨Δ⟩ = Free-EM {M = H} .Functor.F₀ Δ

    Endomorphism-type : Type (o ⊔ r)
    Endomorphism-type = Hom Fᴴ⟨Δ⟩ Fᴴ⟨Δ⟩

    --------------------------------------------------------------------------------
    -- Order

    endo[_≤_] : ∀ (σ δ : Endomorphism-type) → Type (o ⊔ r)
    endo[ σ ≤ δ ] = (α : ⌞ Δ ⌟) → σ · (unit.η Δ · α) H⟨Δ⟩.≤ δ · (unit.η Δ · α)

    abstract
      endo≤-thin : ∀ σ δ → is-prop endo[ σ ≤ δ ]
      endo≤-thin σ δ = hlevel 1

      endo≤-refl : ∀ σ → endo[ σ ≤ σ ]
      endo≤-refl σ _ = H⟨Δ⟩.≤-refl

      endo≤-trans : ∀ σ δ τ → endo[ σ ≤ δ ] → endo[ δ ≤ τ ] → endo[ σ ≤ τ ]
      endo≤-trans σ δ τ σ≤δ δ≤τ α = H⟨Δ⟩.≤-trans (σ≤δ α) (δ≤τ α)

      endo≤-antisym : ∀ σ δ → endo[ σ ≤ δ ] → endo[ δ ≤ σ ] → σ ≡ δ
      endo≤-antisym σ δ σ≤δ δ≤σ = free-algebra-hom-path H $ ext λ α →
        H⟨Δ⟩.≤-antisym (σ≤δ α) (δ≤σ α)

  Endomorphism : Poset (o ⊔ r) (o ⊔ r)
  Endomorphism .Poset.Ob = Endomorphism-type
  Endomorphism .Poset._≤_ = endo[_≤_]
  Endomorphism .Poset.≤-thin {σ} {δ} = endo≤-thin σ δ
  Endomorphism .Poset.≤-refl {σ} = endo≤-refl σ
  Endomorphism .Poset.≤-trans {σ} {δ} {τ} = endo≤-trans σ δ τ
  Endomorphism .Poset.≤-antisym {σ} {δ} = endo≤-antisym σ δ
