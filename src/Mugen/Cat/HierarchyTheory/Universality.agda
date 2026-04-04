-- vim: nowrap
open import Order.Instances.Discrete
open import Order.Instances.Coproduct

open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Compose
open import Cat.Functor.Morphism
open import Cat.Functor.Properties
open import Cat.Diagram.Monad
open import Cat.Displayed.Total

import Cat.Reasoning as Cat
import Cat.Functor.Reasoning as FR

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Instances.Endomorphism

open import Mugen.Cat.Instances.Endomorphisms
open import Mugen.Cat.Instances.Indexed
open import Mugen.Cat.Instances.StrictOrders
open import Mugen.Cat.Monad
open import Mugen.Cat.HierarchyTheory
open import Mugen.Cat.HierarchyTheory.McBride

import Mugen.Order.Reasoning as Reasoning

--------------------------------------------------------------------------------
-- The Universal Embedding Theorem
-- Section 3.4, Theorem 3.10

module Mugen.Cat.HierarchyTheory.Universality {o o' r}
  {F : Functor (Strict-orders (o ⊔ o') (r ⊔ o')) (Strict-orders (o ⊔ o') (r ⊔ o'))}
  (H : Hierarchy-theory-on F) {I : Type o'} ⦃ Discrete-I : Discrete I ⦄
  (Δ₋ : ⌞ I ⌟ → Poset (o ⊔ o') (r ⊔ o')) (Ψ : Set (o ⊔ r ⊔ o')) where

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
    open ∫Hom
    module H = Monad-on H

    SOrd : Precategory (lsuc (o ⊔ r ⊔ o')) (o ⊔ r ⊔ o')
    SOrd = Strict-orders (o ⊔ o') (r ⊔ o')
    open Cat SOrd

    SOrdᴴ : Precategory (lsuc (o ⊔ r ⊔ o')) (o ⊔ r ⊔ o')
    SOrdᴴ = Eilenberg-Moore {C = SOrd} H
    module SOrdᴴ = Cat SOrdᴴ

    -- '↑' for lifting
    SOrd↑ : Precategory (lsuc (o ⊔ r ⊔ o')) (o ⊔ r ⊔ o')
    SOrd↑ = Strict-orders (o ⊔ r ⊔ o') (o ⊔ r ⊔ o')
    module SOrd↑ = Cat SOrd↑

    SOrdᴹᴰ : Precategory (lsuc (o ⊔ r ⊔ o')) (o ⊔ r ⊔ o')
    SOrdᴹᴰ = Eilenberg-Moore {C = SOrd↑} (McBride (Endomorphism H EE.Δ⁺))
    module SOrdᴹᴰ = Cat SOrdᴹᴰ

    Liftᶠ : Functor SOrd SOrd↑
    Liftᶠ = liftᶠ-strict-orders {o' = r ⊔ o'} {r' = o ⊔ o'}

  --------------------------------------------------------------------------------
  -- Constructing the natural transformation T
  -- Section 3.4, Theorem 3.10

  T : Functor (Indexed SOrdᴴ λ i → Free-EM .Functor.F₀ (Δ₋ i)) (Endos SOrdᴹᴰ (Free-EM .Functor.F₀ (Disc Ψ)))
  T = EE.T F∘ SE.T

  --------------------------------------------------------------------------------
  -- Constructing the natural transformation ν
  -- Section 3.4, Theorem 3.10

  ν : ∣ Ψ ∣
    →  Liftᶠ F∘ Forget-EM F∘ Indexed-include
    => Forget-EM F∘ Endos-include F∘ T
  ν pt = lemma-assoc₂
    ∘nt  (EEN.ν pt ◂ SE.T)
    ∘nt  lemma-assoc₁
    ∘nt  (Liftᶠ ▸ (Forget-EM ▸ SE.ν))
    where
      lemma-assoc₁
        :  Liftᶠ F∘ Forget-EM F∘ Endos-include F∘ SE.T
        => (Liftᶠ F∘ Forget-EM F∘ Endos-include) F∘ SE.T
      lemma-assoc₁ ._=>_.η _              = SOrd↑.id
      lemma-assoc₁ ._=>_.is-natural _ _ _ = SOrd↑.id-comm-sym

      lemma-assoc₂
        :  (Forget-EM F∘ Endos-include F∘ EE.T) F∘ SE.T
        => Forget-EM F∘ Endos-include F∘ EE.T F∘ SE.T
      lemma-assoc₂ ._=>_.η _              = SOrd↑.id
      lemma-assoc₂ ._=>_.is-natural _ _ _ = SOrd↑.id-comm-sym

  --------------------------------------------------------------------------------
  -- Faithfulness of T
  -- Section 3.4, Lemma 3.9

  abstract
    T-faithful : ∣ Ψ ∣ → preserves-monos F → is-faithful T
    T-faithful pt H-preserves-monos eq =
      SE.T-faithful H-preserves-monos $
      EE.T-faithful pt H-preserves-monos eq
