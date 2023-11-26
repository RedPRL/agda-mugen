module Mugen.Algebra.Displacement.Endomorphism where

open import Algebra.Magma
open import Algebra.Monoid renaming (idl to ⊗-idl; idr to ⊗-idr)
open import Algebra.Semigroup

open import Cat.Diagram.Monad
import Cat.Reasoning as Cat

open import Mugen.Prelude
open import Mugen.Data.NonEmpty

open import Mugen.Algebra.Displacement
open import Mugen.Order.Poset
open import Mugen.Cat.StrictOrders
open import Mugen.Cat.HierarchyTheory

--------------------------------------------------------------------------------
-- Endomorphism Displacements
-- Section 3.4
--
-- Given a Monad 'H' on the category of strict orders, we can construct a displacement
-- algebra whose carrier set is the set of endomorphisms 'Free H Δ → Free H Δ' between
-- free H-algebras in the Eilenberg-Moore category.
open Algebra-hom

instance
  Funlike-algebra-hom
    : ∀ {o ℓ} {C : Precategory o ℓ}
    → {M : Monad C}
    → (let module C = Precategory C)
    → ⦃ fl : Funlike C.Hom ⦄
    → Funlike (Algebra-hom C M)
  Funlike-algebra-hom ⦃ fl ⦄ .Funlike.au = Underlying-Σ ⦃ ua = Funlike.au fl ⦄
  Funlike-algebra-hom ⦃ fl ⦄ .Funlike.bu = Underlying-Σ ⦃ ua = Funlike.bu fl ⦄
  Funlike-algebra-hom ⦃ fl ⦄ .Funlike._#_ f x = f .morphism # x

module _ {o r} (H : Monad (Strict-orders o r)) (Δ : Poset o r) where

  open Monad H renaming (M₀ to H₀; M₁ to H₁)
  open Cat (Eilenberg-Moore (Strict-orders o r) H)

  private
    module H⟨Δ⟩ = Poset (H₀ Δ)
    Fᴴ⟨Δ⟩ : Algebra (Strict-orders o r) H
    Fᴴ⟨Δ⟩ = Functor.F₀ (Free (Strict-orders o r) H) Δ
    {-# INLINE Fᴴ⟨Δ⟩ #-}

    Endomorphism : Type (lsuc o ⊔ lsuc r)
    Endomorphism = Hom Fᴴ⟨Δ⟩ Fᴴ⟨Δ⟩
    {-# INLINE Endomorphism #-}


  --------------------------------------------------------------------------------
  -- Algebra

  endo-is-magma : is-magma _∘_
  endo-is-magma .has-is-set = Hom-set Fᴴ⟨Δ⟩ Fᴴ⟨Δ⟩

  endo-is-semigroup : is-semigroup _∘_
  endo-is-semigroup .has-is-magma = endo-is-magma
  endo-is-semigroup .associative {f} {g} {h} = assoc f g h

  endo-is-monoid : is-monoid id _∘_
  endo-is-monoid .has-is-semigroup = endo-is-semigroup
  endo-is-monoid .⊗-idl {f} = idl f
  endo-is-monoid .⊗-idr {f} = idr f

  --------------------------------------------------------------------------------
  -- Order

  -- Favonia: the following "HACK" note was left when we were using records
  -- to define 'endo[_≤_]'. The accuracy of the note should be checked again.
  -- > HACK: We could make this live in a lower universe level,
  -- > but then we can't construct a hierarchy theory from it without an annoying lift.
  endo[_≤_] : ∀ (σ δ : Endomorphism) → Type (lsuc o ⊔ lsuc r)
  endo[_≤_] σ δ = Lift _ ((α : ⌞ Δ ⌟) → σ # (unit.η Δ # α) H⟨Δ⟩.≤ δ # (unit.η Δ # α))

  endo[_<_] : ∀ (σ δ : Endomorphism) → Type (lsuc o ⊔ lsuc r)
  endo[_<_] = strict endo[_≤_]

  endo≤-thin : ∀ σ δ → is-prop endo[ σ ≤ δ ]
  endo≤-thin σ δ = hlevel!

  endo≤-refl : ∀ σ → endo[ σ ≤ σ ]
  endo≤-refl σ = lift λ _ → H⟨Δ⟩.≤-refl

  endo≤-trans : ∀ σ δ τ → endo[ σ ≤ δ ] → endo[ δ ≤ τ ] → endo[ σ ≤ τ ]
  endo≤-trans σ δ τ (lift σ≤δ) (lift δ≤τ) = lift λ α → H⟨Δ⟩.≤-trans (σ≤δ α) (δ≤τ α)

  endo≤-antisym : ∀ σ δ → endo[ σ ≤ δ ] → endo[ δ ≤ σ ] → σ ≡ δ
  endo≤-antisym σ δ (lift σ≤δ) (lift δ≤σ) = free-algebra-hom-path $ ext λ α →
    H⟨Δ⟩.≤-antisym (σ≤δ α) (δ≤σ α)

  --------------------------------------------------------------------------------
  -- Left Invariance

  ∘-left-invariant : ∀ (σ δ τ : Endomorphism) → endo[ δ ≤ τ ] → endo[ σ ∘ δ ≤ σ ∘ τ ]
  ∘-left-invariant σ δ τ δ≤τ = lift λ α → σ .morphism .Strictly-monotone.mono (δ≤τ .Lift.lower α)

  ∘-injr-on-≤ : ∀ (σ δ τ : Endomorphism) → endo[ δ ≤ τ ] → σ ∘ δ ≡ σ ∘ τ → δ ≡ τ
  ∘-injr-on-≤ σ δ τ (lift δ≤τ) p = free-algebra-hom-path $ ext λ α →
    σ .morphism .Strictly-monotone.inj-on-related (δ≤τ α) (ap (_# (unit.η Δ # α)) p)

  --------------------------------------------------------------------------------
  -- Bundles
  --
  -- We do this with copatterns for performance reasons.

  Endo≤ : Poset (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)
  Endo≤ .Poset.Ob = Endomorphism
  Endo≤ .Poset.poset-on .Poset-on._≤_ = endo[_≤_]
  Endo≤ .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-thin {σ} {δ} = endo≤-thin σ δ
  Endo≤ .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-refl {σ} = endo≤-refl σ
  Endo≤ .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-trans {σ} {δ} {τ} = endo≤-trans σ δ τ
  Endo≤ .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-antisym {σ} {δ} = endo≤-antisym σ δ

  Endo∘ : Displacement-algebra (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)
  Endo∘ .Displacement-algebra.poset = Endo≤
  Endo∘ .Displacement-algebra.displacement-algebra-on .Displacement-algebra-on.ε = id
  Endo∘ .Displacement-algebra.displacement-algebra-on .Displacement-algebra-on._⊗_ = _∘_
  Endo∘ .Displacement-algebra.displacement-algebra-on .Displacement-algebra-on.has-is-displacement-algebra .is-displacement-algebra.has-is-monoid .has-is-semigroup .has-is-magma .has-is-set = hlevel!
  Endo∘ .Displacement-algebra.displacement-algebra-on .Displacement-algebra-on.has-is-displacement-algebra .is-displacement-algebra.has-is-monoid .has-is-semigroup .associative = assoc _ _ _
  Endo∘ .Displacement-algebra.displacement-algebra-on .Displacement-algebra-on.has-is-displacement-algebra .is-displacement-algebra.has-is-monoid .⊗-idl = idl _
  Endo∘ .Displacement-algebra.displacement-algebra-on .Displacement-algebra-on.has-is-displacement-algebra .is-displacement-algebra.has-is-monoid .⊗-idr = idr _
  Endo∘ .Displacement-algebra.displacement-algebra-on .Displacement-algebra-on.has-is-displacement-algebra .is-displacement-algebra.≤-left-invariant {σ} {δ} {τ} = ∘-left-invariant σ δ τ
  Endo∘ .Displacement-algebra.displacement-algebra-on .Displacement-algebra-on.has-is-displacement-algebra .is-displacement-algebra.injr-on-≤ = ∘-injr-on-≤ _ _ _
