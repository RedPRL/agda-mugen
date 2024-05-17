-- vim: nowrap
open import Order.Instances.Discrete

open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Properties
open import Cat.Diagram.Monad

import Cat.Reasoning as Cat
import Cat.Functor.Reasoning as FR

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Instances.Endomorphism

open import Mugen.Cat.Endomorphisms
open import Mugen.Cat.StrictOrders
open import Mugen.Cat.Monad
open import Mugen.Cat.HierarchyTheory
open import Mugen.Cat.HierarchyTheory.McBride

open import Mugen.Order.StrictOrder
open import Mugen.Order.Instances.Endomorphism renaming (Endomorphism to Endomorphism-poset)
open import Mugen.Order.Instances.Coproduct
open import Mugen.Order.Instances.LeftInvariantRightCentered
open import Mugen.Order.Instances.Singleton

import Mugen.Order.Reasoning as Reasoning

--------------------------------------------------------------------------------
-- The Universal Embedding Theorem
-- Section 3.4, Lemma 3.8
--
-- Given a hierarchy theory 'H', a strict order Δ, and a set Ψ, we can
-- construct a faithful functor 'T : Endos (Fᴴ Δ) → Endos Fᴹᴰ Ψ', where
-- 'Fᴴ' denotes the free H-algebra on Δ, and 'Fᴹᴰ Ψ' denotes the free McBride
-- Hierarchy theory over the endomorphism displacement algebra on 'H (◆ ⊕ Δ ⊕ Δ)'.
--
-- This file covers the naturality

module Mugen.Cat.HierarchyTheory.Universality.EndomorphismEmbeddingNaturality
  {o r} (H : Hierarchy-theory o r) (Δ : Poset o r) (Ψ : Set (lsuc o ⊔ lsuc r)) where

  open import Mugen.Cat.HierarchyTheory.Universality.EndomorphismEmbedding H Δ Ψ

  --------------------------------------------------------------------------------
  -- Notation
  --
  -- We begin by defining some useful notation.

  private
    open Strictly-monotone
    open Algebra-hom
    open Cat (Strict-orders o r)
    module Δ = Poset Δ
    module H = Monad H

    Δ⁺ : Poset o r
    Δ⁺ = Coproduct ◆ (Coproduct Δ Δ)

    H⟨Δ⟩ : Poset o r
    H⟨Δ⟩ = H.M₀ Δ
    module H⟨Δ⟩ = Poset H⟨Δ⟩

    H⟨Δ⁺⟩ : Poset o r
    H⟨Δ⁺⟩ = H.M₀ Δ⁺
    module H⟨Δ⁺⟩ = Poset H⟨Δ⁺⟩

    H⟨Δ⁺⟩→-poset : Poset (lsuc (o ⊔ r)) (o ⊔ r)
    H⟨Δ⁺⟩→-poset = Endomorphism-poset H Δ⁺
    module H⟨Δ⁺⟩→-poset = Reasoning H⟨Δ⁺⟩→-poset

    H⟨Δ⁺⟩→ : Displacement-on H⟨Δ⁺⟩→-poset
    H⟨Δ⁺⟩→ = Endomorphism H Δ⁺
    module H⟨Δ⁺⟩→ = Displacement-on H⟨Δ⁺⟩→

    SOrd : Precategory (lsuc (o ⊔ r)) (o ⊔ r)
    SOrd = Strict-orders o r
    module SOrd = Cat SOrd

    SOrdᴴ : Precategory (lsuc (o ⊔ r)) (lsuc (o ⊔ r))
    SOrdᴴ = Eilenberg-Moore SOrd H
    module SOrdᴴ = Cat SOrdᴴ

    -- '↑' for lifting
    SOrd↑ : Precategory (lsuc (lsuc (o ⊔ r))) (lsuc (o ⊔ r))
    SOrd↑ = Strict-orders (lsuc (o ⊔ r)) (lsuc (o ⊔ r))

    SOrdᴹᴰ : Precategory (lsuc (lsuc (o ⊔ r))) (lsuc (lsuc (o ⊔ r)))
    SOrdᴹᴰ = Eilenberg-Moore SOrd↑ (McBride H⟨Δ⁺⟩→)
    module SOrdᴹᴰ = Cat SOrdᴹᴰ

    Fᴴ⟨_⟩ : Poset o r → Algebra SOrd H
    Fᴴ⟨_⟩ = Functor.F₀ (Free SOrd H)

  --------------------------------------------------------------------------------
  -- NOTE: Forgetful Functors + Levels
  --
  -- To avoid dealing with an annoying level shifting functor, we bake in the
  -- required lifts into Uᴴ instead.

  Uᴴ : ∀ {X} → Functor (Endos SOrdᴴ X) SOrd↑
  Uᴴ {X} .Functor.F₀ _ = Lift≤ _ _ (X .fst)
  Uᴴ .Functor.F₁ σ .hom (lift α) = lift (σ # α)
  Uᴴ .Functor.F₁ σ .pres-≤[]-equal (lift α≤β) =
    let σα≤σβ , inj = σ .morphism .pres-≤[]-equal α≤β in
    lift σα≤σβ , λ p → ap lift $ inj $ lift-inj p
  Uᴴ .Functor.F-id = ext λ _ → refl
  Uᴴ .Functor.F-∘ _ _ = ext λ _ → refl

  Uᴹᴰ : ∀ {X} → Functor (Endos SOrdᴹᴰ X) SOrd↑
  Uᴹᴰ {X} .Functor.F₀ _ = X .fst
  Uᴹᴰ .Functor.F₁ σ = σ .morphism
  Uᴹᴰ .Functor.F-id = refl
  Uᴹᴰ .Functor.F-∘ _ _ = refl

  --------------------------------------------------------------------------------
  -- Constructing the natural transformation ν
  -- Section 3.4, Lemma 3.8

  ν : (pt : ∣ Ψ ∣) → Uᴴ => Uᴹᴰ F∘ T
  ν pt = nt
    where
      ℓ̅ : ⌞ H.M₀ Δ ⌟ → Hom Δ⁺ (H.M₀ Δ⁺)
      ℓ̅ ℓ .hom (ι₀ _) = H.M₁ ι₁-hom # ℓ
      ℓ̅ ℓ .hom (ι₁ α) = H.unit.η _ # ι₂ α
      ℓ̅ ℓ .hom (ι₂ α) = H.unit.η _ # ι₂ α
      ℓ̅ ℓ .pres-≤[]-equal {ι₀ ⋆} {ι₀ ⋆} _ = H⟨Δ⁺⟩.≤-refl , λ _ → refl
      ℓ̅ ℓ .pres-≤[]-equal {ι₁ α} {ι₁ β} α≤β = Σ-map₂ ((ap ι₁ ⊙ ι₂-inj) ⊙_) $ H.unit.η _ .pres-≤[]-equal α≤β
      ℓ̅ ℓ .pres-≤[]-equal {ι₂ α} {ι₂ β} α≤β = H.unit.η _ .pres-≤[]-equal α≤β

      abstract
        ℓ̅-pres-≤ : ∀ {ℓ ℓ′}
          → ℓ′ H⟨Δ⟩.≤ ℓ
          → ∀ (α :  ⌞ Δ⁺ ⌟) → ℓ̅ ℓ′ # α H⟨Δ⁺⟩.≤ ℓ̅ ℓ # α
        ℓ̅-pres-≤ ℓ′≤ℓ (ι₀ _) = pres-≤ (H.M₁ ι₁-hom) ℓ′≤ℓ
        ℓ̅-pres-≤ ℓ′≤ℓ (ι₁ _) = H⟨Δ⁺⟩.≤-refl
        ℓ̅-pres-≤ ℓ′≤ℓ (ι₂ _) = H⟨Δ⁺⟩.≤-refl

      ν′ : ⌞ H.M₀ Δ ⌟ → Algebra-hom SOrd H Fᴴ⟨ Δ⁺ ⟩ Fᴴ⟨ Δ⁺ ⟩
      ν′ ℓ .morphism = H.mult.η Δ⁺ ∘ H.M₁ (ℓ̅ ℓ)
      ν′ ℓ .commutes = ext λ α →
        H.mult.η Δ⁺ # (H.M₁ (ℓ̅ ℓ) # (H.mult.η Δ⁺ # α))               ≡˘⟨ ap# (H.mult.η _) (H.mult.is-natural _ _ (ℓ̅ ℓ) #ₚ α) ⟩
        H.mult.η Δ⁺ # (H.mult.η (H.M₀ Δ⁺) # (H.M₁ (H.M₁ (ℓ̅ ℓ)) # α)) ≡˘⟨ H.mult-assoc #ₚ _ ⟩
        H.mult.η Δ⁺ # (H.M₁ (H.mult.η Δ⁺) # (H.M₁ (H.M₁ (ℓ̅ ℓ)) # α)) ≡˘⟨ ap# (H.mult.η _) (H.M-∘ _ _ #ₚ α) ⟩
        H.mult.η Δ⁺ # (H.M₁ (H.mult.η Δ⁺ ∘ H.M₁ (ℓ̅ ℓ)) # α)          ∎

      abstract
        ν′-mono : ∀ {ℓ′ ℓ : ⌞ H.M₀ Δ ⌟} → ℓ′ H⟨Δ⟩.≤ ℓ → ν′ ℓ′ H⟨Δ⁺⟩→-poset.≤ ν′ ℓ
        ν′-mono {ℓ′} {ℓ} ℓ′≤ℓ α = begin-≤
          H.mult.η Δ⁺ # (H.M₁ (ℓ̅ ℓ′) # (H.unit.η Δ⁺ # α)) ≐⟨ ap# (H.mult.η _) (sym $ H.unit.is-natural _ _ (ℓ̅ ℓ′) #ₚ α) ⟩
          H.mult.η Δ⁺ # (H.unit.η (H.M₀ Δ⁺) # (ℓ̅ ℓ′ # α)) ≤⟨ pres-≤ (H.mult.η _ ∘ H.unit.η _) (ℓ̅-pres-≤ ℓ′≤ℓ α) ⟩
          H.mult.η Δ⁺ # (H.unit.η (H.M₀ Δ⁺) # (ℓ̅ ℓ # α))  ≐⟨ ap# (H.mult.η _) (H.unit.is-natural _ _ (ℓ̅ ℓ) #ₚ α) ⟩
          H.mult.η Δ⁺ # (H.M₁ (ℓ̅ ℓ) # (H.unit.η Δ⁺ # α))  ≤∎
          where
            open Reasoning (H.M₀ Δ⁺)

      abstract
        ν′-injective-on-related : ∀ {ℓ′ ℓ : ⌞ H.M₀ Δ ⌟} → ℓ′ H⟨Δ⟩.≤ ℓ → ν′ ℓ′ ≡ ν′ ℓ → ℓ′ ≡ ℓ
        ν′-injective-on-related {ℓ′} {ℓ} ℓ′≤ℓ p = injective-on-related (H.mult.η _ ∘ H.unit.η _ ∘ H.M₁ ι₁-hom) ℓ′≤ℓ $
          H.mult.η Δ⁺ # (H.unit.η (H.M₀ Δ⁺) # (H.M₁ ι₁-hom # ℓ′)) ≡⟨ ap# (H.mult.η _) (H.unit.is-natural _ _ (ℓ̅ ℓ′) #ₚ _) ⟩
          H.mult.η Δ⁺ # (H.M₁ (ℓ̅ ℓ′) # (H.unit.η Δ⁺ # ι₀ ⋆))      ≡⟨ p #ₚ (H.unit.η _ # ι₀ ⋆) ⟩
          H.mult.η Δ⁺ # (H.M₁ (ℓ̅ ℓ) # (H.unit.η Δ⁺ # ι₀ ⋆))       ≡˘⟨ ap# (H.mult.η _) (H.unit.is-natural _ _ (ℓ̅ ℓ) #ₚ _) ⟩
          H.mult.η Δ⁺ # (H.unit.η (H.M₀ Δ⁺) # (H.M₁ ι₁-hom # ℓ))  ∎

      abstract
        ℓ̅-σ̅ : ∀ {ℓ : ⌞ Fᴴ⟨ Δ ⟩ ⌟} (σ : Algebra-hom _ _ Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩) → ℓ̅ (σ # ℓ) ≡ H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ ℓ̅ ℓ
        ℓ̅-σ̅ {ℓ} σ = ext λ where
          (ι₀ ⋆) →
            H.M₁ ι₁-hom # (σ # ℓ)                                                              ≡˘⟨ ap (λ e → H.M₁ ι₁-hom # (σ # e)) (H.left-ident #ₚ ℓ) ⟩
            H.M₁ ι₁-hom # (σ # (H.mult.η _ # (H.M₁ (H.unit.η _) # ℓ)))                         ≡⟨ ap# (H.M₁ ι₁-hom) (σ .commutes #ₚ _) ⟩
            H.M₁ ι₁-hom # (H.mult.η _ # (H.M₁ (σ .morphism) # (H.M₁ (H.unit.η _) # ℓ)))        ≡˘⟨ H.mult.is-natural _ _ ι₁-hom #ₚ _ ⟩
            H.mult.η _ # (H.M₁ (H.M₁ ι₁-hom) # (H.M₁ (σ .morphism) # (H.M₁ (H.unit.η Δ) # ℓ))) ≡⟨ ap# (H.mult.η _) (σ̅-ι σ ℓ) ⟩
            H.mult.η _ # (H.M₁ (σ̅ σ) # (H.M₁ ι₁-hom # ℓ))                                      ∎
          (ι₁ α) →
            H.unit.η _ # ι₂ α                               ≡˘⟨ H.right-ident #ₚ _ ⟩
            H.mult.η _ # (H.unit.η _ # (H.unit.η _ # ι₂ α)) ≡⟨ ap# (H.mult.η _) (H.unit.is-natural _ _ (σ̅ σ) #ₚ (ι₂ α)) ⟩
            H.mult.η _ # (H.M₁ (σ̅ σ) # (H.unit.η _ # ι₂ α)) ∎
          (ι₂ α) →
            H.unit.η _ # ι₂ α                               ≡˘⟨ H.right-ident #ₚ _ ⟩
            H.mult.η _ # (H.unit.η _ # (H.unit.η _ # ι₂ α)) ≡⟨ ap# (H.mult.η _) (H.unit.is-natural _ _ (σ̅ σ) #ₚ (ι₂ α)) ⟩
            H.mult.η _ # (H.M₁ (σ̅ σ) # (H.unit.η _ # ι₂ α)) ∎

      nt : Uᴴ => Uᴹᴰ F∘ T
      nt ._=>_.η _ .hom (lift ℓ) = pt , ν′ ℓ
      nt ._=>_.η _ .pres-≤[]-equal (lift ℓ≤ℓ′) =
        inc (biased refl (ν′-mono ℓ≤ℓ′)) , λ p → ap lift $ ν′-injective-on-related ℓ≤ℓ′ (ap snd p)
      nt ._=>_.is-natural _ _ σ = ext λ ℓ →
        refl , λ α →
          H.mult.η _ # (H.M₁ (ℓ̅ (σ # ℓ)) # α)                                       ≡⟨ ap (λ e → (H.mult.η _ ∘ H.M₁ e) # α) (ℓ̅-σ̅ σ) ⟩
          H.mult.η _ # (H.M₁ (H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ ℓ̅ ℓ) # α)                   ≡⟨ ap# (H.mult.η _) (H.M-∘ _ _ #ₚ α) ⟩
          H.mult.η _ # ((H.M₁ (H.mult.η _) ∘ H.M₁ (H.M₁ (σ̅ σ) ∘ ℓ̅ ℓ)) # α)          ≡⟨ ap (λ e → H.mult.η _ # ((H.M₁ (H.mult.η _) ∘ e) # α)) (H.M-∘ (H.M₁ (σ̅ σ)) (ℓ̅ ℓ)) ⟩
          H.mult.η _ # (H.M₁ (H.mult.η _) # (H.M₁ (H.M₁ (σ̅ σ)) # (H.M₁ (ℓ̅ ℓ) # α))) ≡⟨ H.mult-assoc #ₚ _ ⟩
          H.mult.η _ # (H.mult.η _ # (H.M₁ (H.M₁ (σ̅ σ)) # (H.M₁ (ℓ̅ ℓ) # α)))        ≡⟨ ap# (H.mult.η _) (H.mult.is-natural _ _ (σ̅ σ) #ₚ _) ⟩
          H.mult.η _ # (H.M₁ (σ̅ σ) # (H.mult.η _ # (H.M₁ (ℓ̅ ℓ) # α)))               ∎
