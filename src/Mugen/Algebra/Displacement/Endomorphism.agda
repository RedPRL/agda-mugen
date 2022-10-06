module Mugen.Algebra.Displacement.Endomorphism where

open import Algebra.Magma
open import Algebra.Monoid renaming (idl to ⊗-idl; idr to ⊗-idr)
open import Algebra.Semigroup

open import Cat.Diagram.Monad
import Cat.Reasoning as Cat

open import Mugen.Prelude
open import Mugen.Data.NonEmpty

open import Mugen.Algebra.Displacement
open import Mugen.Cat.StrictOrders
open import Mugen.Order.StrictOrder
open import Mugen.Order.Poset

open import Relation.Order

--------------------------------------------------------------------------------
-- Endomorphism Displacements
-- Section 3.4
--
-- Given a Monad 'H' on the category of strict orders, we can construct a displacement
-- algebra whose carrier set is the set of endomorphisms 'Free H Δ → Free H Δ' between
-- free H-algebras in the Eilenberg-Moore category.

module _ {o r} (H : Monad (StrictOrders o r)) (Δ : StrictOrder o r) where

  open Monad H renaming (M₀ to H₀; M₁ to H₁)
  open Cat (Eilenberg-Moore (StrictOrders o r) H)
  module H⟨Δ⟩ = StrictOrder (H₀ Δ)
  open Algebra-hom

  private
    Fᴴ⟨Δ⟩ : Algebra (StrictOrders o r) H
    Fᴴ⟨Δ⟩ = Functor.F₀ (Free (StrictOrders o r) H) Δ
    {-# INLINE Fᴴ⟨Δ⟩ #-}

    Endomorphism : Type (lsuc o ⊔ lsuc r)
    Endomorphism = Hom Fᴴ⟨Δ⟩ Fᴴ⟨Δ⟩
    {-# INLINE Endomorphism #-}

  --------------------------------------------------------------------------------
  -- Algebra

  _⊗_ : Endomorphism → Endomorphism → Endomorphism
  _⊗_ = _∘_

  endo-is-magma : is-magma _⊗_
  endo-is-magma .has-is-set = Hom-set Fᴴ⟨Δ⟩ Fᴴ⟨Δ⟩

  endo-is-semigroup : is-semigroup _⊗_
  endo-is-semigroup .has-is-magma = endo-is-magma
  endo-is-semigroup .associative {f} {g} {h} = assoc f g h

  endo-is-monoid : is-monoid id _⊗_
  endo-is-monoid .has-is-semigroup = endo-is-semigroup
  endo-is-monoid .⊗-idl {f} = idl f
  endo-is-monoid .⊗-idr {f} = idr f

  --------------------------------------------------------------------------------
  -- Order

  -- HACK: We could make this live in a lower universe level, but then we can't construct a hierarchy theory from it without an annoying lift.
  record endo[_<_] (σ δ : Endomorphism) : Type (lsuc o ⊔ lsuc r) where
    constructor mk-endo-<
    field
      endo-≤ : ∀ (α : ⌞ Δ ⌟) → H₀ Δ [ σ .morphism ⟨$⟩ unit.η Δ ⟨$⟩ α ≤ δ .morphism ⟨$⟩ unit.η Δ ⟨$⟩ α  ]
      endo-< : ∃[ α ∈ ⌞ Δ ⌟ ] (H₀ Δ [ σ .morphism ⟨$⟩ unit.η Δ ⟨$⟩ α < δ .morphism ⟨$⟩ unit.η Δ ⟨$⟩ α  ])

  open endo[_<_]

  endo-<-irrefl : ∀ {σ} → endo[ σ < σ ] → ⊥
  endo-<-irrefl σ<σ = ∥-∥-elim (λ _ → hlevel 1) (λ lt → H⟨Δ⟩.irrefl (snd lt)) (σ<σ .endo-<)

  endo-<-trans : ∀ {σ δ τ} → endo[ σ < δ ] → endo[ δ < τ ] → endo[ σ < τ ]
  endo-<-trans σ<δ δ<τ .endo-≤ α = H⟨Δ⟩.≤-trans (σ<δ .endo-≤ α) (δ<τ .endo-≤ α)
  endo-<-trans σ<δ δ<τ .endo-< = ∥-∥-map₂ (λ lt₁ lt₂ → fst lt₂ , H⟨Δ⟩.≤-transl (σ<δ .endo-≤ (fst lt₂)) (snd lt₂)) (σ<δ .endo-<) (δ<τ .endo-<)

  private unquoteDecl eqv = declare-record-iso eqv (quote endo[_<_])

  instance
    endo-<-hlevel : ∀ {σ δ} {n} → H-Level endo[ σ < δ ] (suc n)
    endo-<-hlevel = prop-instance λ f →
      let instance
        H⟨Δ⟩-≤-hlevel : ∀ {x y} {n} → H-Level (H₀ Δ [ x ≤ y ]) (suc n)
        H⟨Δ⟩-≤-hlevel = prop-instance H⟨Δ⟩.≤-is-prop
      in is-hlevel≃ 1 (Iso→Equiv eqv e⁻¹) (hlevel 1) f

  endo-<-is-strict-order : is-strict-order endo[_<_]
  endo-<-is-strict-order .is-strict-order.irrefl = endo-<-irrefl
  endo-<-is-strict-order .is-strict-order.trans = endo-<-trans
  endo-<-is-strict-order .is-strict-order.has-prop = hlevel 1

  --------------------------------------------------------------------------------
  -- Left Invariance

  ∘-left-invariant : ∀ (σ δ τ : Endomorphism) → endo[ δ < τ ] → endo[ σ ∘ δ < σ ∘ τ ]
  ∘-left-invariant σ δ τ δ<τ .endo[_<_].endo-≤ α = strictly-mono→mono (σ .morphism) (δ<τ .endo-≤ α)
  ∘-left-invariant σ δ τ δ<τ .endo[_<_].endo-< = ∥-∥-map (λ { (α , δ⟨α⟩<τ⟨α⟩) → α , σ .morphism .homo δ⟨α⟩<τ⟨α⟩ }) (δ<τ .endo-<)

  endo-is-displacement-algebra : is-displacement-algebra endo[_<_] id _∘_
  endo-is-displacement-algebra .is-displacement-algebra.has-monoid = endo-is-monoid
  endo-is-displacement-algebra .is-displacement-algebra.has-strict-order = endo-<-is-strict-order
  endo-is-displacement-algebra .is-displacement-algebra.left-invariant {σ} {δ} {τ} = ∘-left-invariant σ δ τ

  Endo : DisplacementAlgebra (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)
  ⌞ Endo ⌟ = Endomorphism
  Endo .structure .DisplacementAlgebra-on._<_ = endo[_<_]
  Endo .structure .DisplacementAlgebra-on.ε = id
  Endo .structure .DisplacementAlgebra-on._⊗_ = _∘_
  Endo .structure .DisplacementAlgebra-on.has-displacement-algebra = endo-is-displacement-algebra
  ⌞ Endo ⌟-set = Hom-set _ _
