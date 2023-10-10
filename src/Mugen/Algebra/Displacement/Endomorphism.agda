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

--------------------------------------------------------------------------------
-- Endomorphism Displacements
-- Section 3.4
--
-- Given a Monad 'H' on the category of strict orders, we can construct a displacement
-- algebra whose carrier set is the set of endomorphisms 'Free H Δ → Free H Δ' between
-- free H-algebras in the Eilenberg-Moore category.

module _ {o r} (H : Monad (Strict-orders o r)) (Δ : Strict-order o r) where

  open Monad H renaming (M₀ to H₀; M₁ to H₁)
  open Cat (Eilenberg-Moore (Strict-orders o r) H)
  module H⟨Δ⟩ = Strict-order (H₀ Δ)
  open Algebra-hom

  private
    Fᴴ⟨Δ⟩ : Algebra (Strict-orders o r) H
    Fᴴ⟨Δ⟩ = Functor.F₀ (Free (Strict-orders o r) H) Δ
    {-# INLINE Fᴴ⟨Δ⟩ #-}

    Endomorphism : Type (lsuc o ⊔ lsuc r)
    Endomorphism = Hom Fᴴ⟨Δ⟩ Fᴴ⟨Δ⟩
    {-# INLINE Endomorphism #-}

  instance
    Funlike-algebra-hom
      : Funlike Hom
    Funlike-algebra-hom .Funlike._#_ f x = f .morphism # x
    Funlike-algebra-hom .Funlike.ext p = Algebra-hom-path (Strict-orders o r) (ext p)

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
      endo-≤ : ∀ (α : ⌞ Δ ⌟) → σ # (unit.η Δ # α) H⟨Δ⟩.≤ δ # (unit.η Δ # α)
      endo-< : ∃[ α ∈ ⌞ Δ ⌟ ] (σ # (unit.η Δ # α) H⟨Δ⟩.< (δ # (unit.η Δ # α)))

  open endo[_<_]

  endo-<-irrefl : ∀ {σ} → endo[ σ < σ ] → ⊥
  endo-<-irrefl σ<σ =
    ∥-∥-elim (λ _ → hlevel 1)
      (λ lt → H⟨Δ⟩.<-irrefl (snd lt))
      (σ<σ .endo-<)

  endo-<-trans : ∀ {σ δ τ} → endo[ σ < δ ] → endo[ δ < τ ] → endo[ σ < τ ]
  endo-<-trans σ<δ δ<τ .endo-≤ α = H⟨Δ⟩.≤-trans (σ<δ .endo-≤ α) (δ<τ .endo-≤ α)
  endo-<-trans σ<δ δ<τ .endo-< =
    ∥-∥-map₂ (λ lt₁ lt₂ → fst lt₂ , H⟨Δ⟩.≤-transl (σ<δ .endo-≤ (fst lt₂)) (snd lt₂))
      (σ<δ .endo-<)
      (δ<τ .endo-<)

  private unquoteDecl eqv = declare-record-iso eqv (quote endo[_<_])

  instance
    endo-<-hlevel : ∀ {σ δ} {n} → H-Level endo[ σ < δ ] (suc n)
    endo-<-hlevel = prop-instance λ f →
      let instance
        H⟨Δ⟩-≤-hlevel : ∀ {x y} {n} → H-Level (x H⟨Δ⟩.≤ y) (suc n)
        H⟨Δ⟩-≤-hlevel = prop-instance H⟨Δ⟩.≤-thin
      in Iso→is-hlevel 1 eqv (hlevel 1) f

  --------------------------------------------------------------------------------
  -- Left Invariance

  ∘-left-invariant : ∀ (σ δ τ : Endomorphism) → endo[ δ < τ ] → endo[ σ ∘ δ < σ ∘ τ ]
  ∘-left-invariant σ δ τ δ<τ = ∘-lt
    where
      module σ = Strictly-monotone (σ .morphism)

      ∘-lt : endo[ σ ∘ δ < σ ∘ τ ]
      ∘-lt .endo-≤ α = σ.mono (δ<τ .endo-≤ α)
      ∘-lt .endo-< = ∥-∥-map (λ lt → lt .fst , σ.strict-mono (lt .snd)) (δ<τ .endo-<)

  --------------------------------------------------------------------------------
  -- Bundles

  Endos : Strict-order (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)
  Endos = to-strict-order mk where
    mk : make-strict-order (lsuc o ⊔ lsuc r) Endomorphism
    mk .make-strict-order._<_ = endo[_<_]
    mk .make-strict-order.<-irrefl = endo-<-irrefl
    mk .make-strict-order.<-trans = endo-<-trans
    mk .make-strict-order.<-thin = hlevel 1
    mk .make-strict-order.has-is-set = Hom-set _ _

  Endos-displacement : Displacement-algebra (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)
  Endos-displacement = to-displacement-algebra mk where
    mk : make-displacement-algebra Endos
    mk .make-displacement-algebra.ε = id
    mk .make-displacement-algebra._⊗_ = _∘_
    mk .make-displacement-algebra.idl = idl _
    mk .make-displacement-algebra.idr = idr _
    mk .make-displacement-algebra.associative = assoc _ _ _
    mk .make-displacement-algebra.left-invariant = ∘-left-invariant _ _ _
