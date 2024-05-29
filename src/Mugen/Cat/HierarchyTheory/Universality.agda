-- vim: nowrap
open import Order.Instances.Discrete
open import Order.Instances.Coproduct

open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Compose
open import Cat.Functor.Properties
open import Cat.Diagram.Monad

import Cat.Reasoning as Cat
import Cat.Functor.Reasoning as FR

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Instances.Endomorphism

open import Mugen.Cat.Endomorphisms
open import Mugen.Cat.Indexed
open import Mugen.Cat.StrictOrders
open import Mugen.Cat.Monad
open import Mugen.Cat.HierarchyTheory
open import Mugen.Cat.HierarchyTheory.McBride

open import Mugen.Order.StrictOrder
open import Mugen.Order.Instances.Endomorphism renaming (Endomorphism to Endomorphism-poset)
open import Mugen.Order.Instances.LeftInvariantRightCentered
open import Mugen.Order.Instances.Lift
open import Mugen.Order.Instances.Singleton

import Mugen.Order.Reasoning as Reasoning

--------------------------------------------------------------------------------
-- The Universal Embedding Theorem
-- Section 3.4, Theorem 3.10

module Mugen.Cat.HierarchyTheory.Universality {o o' r}
  (H : Hierarchy-theory (o ⊔ o') (r ⊔ o')) {I : Type o'} ⦃ Discrete-I : Discrete I ⦄
  (Δ₋ : ⌞ I ⌟ → Poset (o ⊔ o') (r ⊔ o')) (Ψ : Set (lsuc (o ⊔ r ⊔ o'))) where

  private
    import Mugen.Cat.HierarchyTheory.Universality.SubcategoryEmbedding as SubcategoryEmbedding
    module SE = SubcategoryEmbedding {o = o} {r = r} H Δ₋

    import Mugen.Cat.HierarchyTheory.Universality.EndomorphismEmbedding as EndomorphismEmbedding
    module EE = EndomorphismEmbedding H SE.Δ Ψ

    import Mugen.Cat.HierarchyTheory.Universality.EndomorphismEmbeddingNaturality as EndomorphismEmbeddingNaturality
    module EEN = EndomorphismEmbeddingNaturality H SE.Δ Ψ

  --------------------------------------------------------------------------------
  -- Notation

  private
    open Strictly-monotone
    open Algebra-hom
    module H = Monad H

    SOrd : Precategory (lsuc (o ⊔ r ⊔ o')) (o ⊔ r ⊔ o')
    SOrd = Strict-orders (o ⊔ o') (r ⊔ o')
    open Cat SOrd

    SOrdᴴ : Precategory (lsuc (o ⊔ r ⊔ o')) (lsuc (o ⊔ r ⊔ o'))
    SOrdᴴ = Eilenberg-Moore SOrd H
    module SOrdᴴ = Cat SOrdᴴ

    -- '↑' for lifting
    SOrd↑ : Precategory (lsuc (lsuc (o ⊔ r ⊔ o'))) (lsuc (o ⊔ r ⊔ o'))
    SOrd↑ = Strict-orders (lsuc (o ⊔ r ⊔ o')) (lsuc (o ⊔ r ⊔ o'))
    module SOrd↑ = Cat SOrd↑

    SOrdᴹᴰ : Precategory (lsuc (lsuc (o ⊔ r ⊔ o'))) (lsuc (lsuc (o ⊔ r ⊔ o')))
    SOrdᴹᴰ = Eilenberg-Moore SOrd↑ (McBride (Endomorphism H EE.Δ⁺))
    module SOrdᴹᴰ = Cat SOrdᴹᴰ

    Uᴴ : Functor SOrdᴴ SOrd
    Uᴴ = Forget SOrd H

    Fᴴ : Functor SOrd SOrdᴴ
    Fᴴ = Free SOrd H

    Fᴴ₀ : Poset (o ⊔ o') (r ⊔ o') → Algebra SOrd H
    Fᴴ₀ = Fᴴ .Functor.F₀

    Fᴴ₁ : {X Y : Poset (o ⊔ o') (r ⊔ o')} → Hom X Y → SOrdᴴ.Hom (Fᴴ₀ X) (Fᴴ₀ Y)
    Fᴴ₁ = Fᴴ .Functor.F₁

    Fᴹᴰ : Functor SOrd↑ SOrdᴹᴰ
    Fᴹᴰ = Free SOrd↑ (McBride (Endomorphism H EE.Δ⁺))

    Fᴹᴰ₀ : Poset (lsuc (o ⊔ r ⊔ o')) (lsuc (o ⊔ r ⊔ o')) → Algebra SOrd↑ (McBride (Endomorphism H EE.Δ⁺))
    Fᴹᴰ₀ = Fᴹᴰ .Functor.F₀

    Uᴹᴰ : Functor SOrdᴹᴰ SOrd↑
    Uᴹᴰ = Forget SOrd↑ (McBride (Endomorphism H EE.Δ⁺))

  --------------------------------------------------------------------------------
  -- Constructing the natural transformation T
  -- Section 3.4, Theorem 3.10

  T : Functor (Indexed SOrdᴴ λ i → Fᴴ₀ (Δ₋ i)) (Endos SOrdᴹᴰ (Fᴹᴰ₀ (Disc Ψ)))
  T = EE.T F∘ SE.T

  --------------------------------------------------------------------------------
  -- Constructing the natural transformation ν
  -- Section 3.4, Theorem 3.10

  ν : ∣ Ψ ∣
    →  liftᶠ-strict-orders F∘ Uᴴ F∘ Indexed-include
    => Uᴹᴰ F∘ Endos-include F∘ T
  ν pt = lemma-assoc₂
    ∘nt  (EEN.ν pt ◂ SE.T)
    ∘nt  lemma-assoc₁
    ∘nt  (liftᶠ-strict-orders ▸ SE.ν)
    where
      lemma-assoc₁
        :  liftᶠ-strict-orders F∘ Uᴴ F∘ Endos-include F∘ SE.T
        => (liftᶠ-strict-orders F∘ Uᴴ F∘ Endos-include) F∘ SE.T
      lemma-assoc₁ ._=>_.η _              = SOrd↑.id
      lemma-assoc₁ ._=>_.is-natural _ _ _ = SOrd↑.id-comm-sym

      lemma-assoc₂
        :  (Uᴹᴰ F∘ Endos-include F∘ EE.T) F∘ SE.T
        => Uᴹᴰ F∘ Endos-include F∘ EE.T F∘ SE.T
      lemma-assoc₂ ._=>_.η _              = SOrd↑.id
      lemma-assoc₂ ._=>_.is-natural _ _ _ = SOrd↑.id-comm-sym

  --------------------------------------------------------------------------------
  -- Faithfulness of T
  -- Section 3.4, Lemma 3.9

  abstract
    T-faithful : ∣ Ψ ∣ → preserves-monos H → is-faithful T
    T-faithful pt H-preserves-monos eq =
      SE.T-faithful H-preserves-monos $
      EE.T-faithful pt H-preserves-monos eq
