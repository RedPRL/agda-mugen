-- vim: nowrap
open import Order.Instances.Discrete
open import Order.Instances.Coproduct

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
open import Mugen.Order.Instances.LeftInvariantRightCentered
open import Mugen.Order.Instances.Lift
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
    Δ⁺ = ◆ {o = o} {r = r} ⊎ᵖ (Δ ⊎ᵖ Δ)

    H⟨Δ⟩ : Poset o r
    H⟨Δ⟩ = H.M₀ Δ
    module H⟨Δ⟩ = Poset H⟨Δ⟩

    H⟨Δ⁺⟩ : Poset o r
    H⟨Δ⁺⟩ = H.M₀ Δ⁺
    module H⟨Δ⁺⟩ = Reasoning H⟨Δ⁺⟩

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

    Uᴴ : Functor SOrdᴴ SOrd
    Uᴴ = Forget SOrd H

    Fᴴ : Functor SOrd SOrdᴴ
    Fᴴ = Free SOrd H

    Fᴴ₀ : Poset o r → Algebra SOrd H
    Fᴴ₀ = Fᴴ .Functor.F₀

    Fᴴ₁ : {X Y : Poset o r} → Hom X Y → SOrdᴴ.Hom (Fᴴ₀ X) (Fᴴ₀ Y)
    Fᴴ₁ = Fᴴ .Functor.F₁

    Uᴹᴰ : Functor SOrdᴹᴰ SOrd↑
    Uᴹᴰ = Forget SOrd↑ (McBride H⟨Δ⁺⟩→)

  --------------------------------------------------------------------------------
  -- Constructing the natural transformation ν
  -- Section 3.4, Lemma 3.8

  ν : (pt : ∣ Ψ ∣)
    →  liftᶠ-strict-orders F∘ Uᴴ F∘ Endos-include
    => Uᴹᴰ F∘ Endos-include F∘ T
  ν pt = nt
    where
      ℓ̅ : ⌞ H.M₀ Δ ⌟ → Hom Δ⁺ (H.M₀ Δ⁺)
      ℓ̅ ℓ .hom (ι₀ _) = H.M₁ ι₁-hom # ℓ
      ℓ̅ ℓ .hom (ι₁ α) = H.η _ # ι₂ α
      ℓ̅ ℓ .hom (ι₂ α) = H.η _ # ι₂ α
      ℓ̅ ℓ .pres-≤[]-equal {ι₀ ⋆} {ι₀ ⋆} _ = H⟨Δ⁺⟩.≤-refl , λ _ → refl
      ℓ̅ ℓ .pres-≤[]-equal {ι₁ α} {ι₁ β} α≤β = H⟨Δ⁺⟩.≤[]-map (ap ι₁ ⊙ ι₂-inj) $ H.η _ .pres-≤[]-equal α≤β
      ℓ̅ ℓ .pres-≤[]-equal {ι₂ α} {ι₂ β} α≤β = H.η _ .pres-≤[]-equal α≤β

      abstract
        ℓ̅-pres-≤ : ∀ {ℓ ℓ′}
          → ℓ′ H⟨Δ⟩.≤ ℓ
          → ∀ (α :  ⌞ Δ⁺ ⌟) → ℓ̅ ℓ′ # α H⟨Δ⁺⟩.≤ ℓ̅ ℓ # α
        ℓ̅-pres-≤ ℓ′≤ℓ (ι₀ _) = pres-≤ (H.M₁ ι₁-hom) ℓ′≤ℓ
        ℓ̅-pres-≤ ℓ′≤ℓ (ι₁ _) = H⟨Δ⁺⟩.≤-refl
        ℓ̅-pres-≤ ℓ′≤ℓ (ι₂ _) = H⟨Δ⁺⟩.≤-refl

      ν′ : ⌞ H.M₀ Δ ⌟ → SOrdᴴ.Hom (Fᴴ₀ Δ⁺) (Fᴴ₀ Δ⁺)
      ν′ ℓ .morphism = H.μ Δ⁺ ∘ H.M₁ (ℓ̅ ℓ)
      ν′ ℓ .commutes = ext λ α →
        H.μ Δ⁺ # (H.M₁ (ℓ̅ ℓ) # (H.μ Δ⁺ # α))               ≡˘⟨ ap# (H.μ _) (H.mult.is-natural _ _ (ℓ̅ ℓ) #ₚ α) ⟩
        H.μ Δ⁺ # (H.μ (H.M₀ Δ⁺) # (H.M₁ (H.M₁ (ℓ̅ ℓ)) # α)) ≡˘⟨ μ-M-∘-μ H (H.M₁ (ℓ̅ ℓ)) #ₚ α ⟩
        H.μ Δ⁺ # (H.M₁ (H.μ Δ⁺ ∘ H.M₁ (ℓ̅ ℓ)) # α)          ∎

      abstract
        ν′-mono : ∀ {ℓ′ ℓ : ⌞ H.M₀ Δ ⌟} → ℓ′ H⟨Δ⟩.≤ ℓ → ν′ ℓ′ H⟨Δ⁺⟩→-poset.≤ ν′ ℓ
        ν′-mono {ℓ′} {ℓ} ℓ′≤ℓ α = begin-≤
          H.μ Δ⁺ # (H.M₁ (ℓ̅ ℓ′) # (H.η Δ⁺ # α)) ≐⟨ μ-η H (ℓ̅ ℓ′) #ₚ α ⟩
          ℓ̅ ℓ′ # α                              ≤⟨ ℓ̅-pres-≤ ℓ′≤ℓ α ⟩
          ℓ̅ ℓ # α                               ≐⟨ sym $ μ-η H (ℓ̅ ℓ) #ₚ α ⟩
          H.μ Δ⁺ # (H.M₁ (ℓ̅ ℓ) # (H.η Δ⁺ # α))  ≤∎
          where
            open Reasoning (H.M₀ Δ⁺)

      abstract
        ν′-injective-on-related : ∀ {ℓ′ ℓ : ⌞ H.M₀ Δ ⌟} → ℓ′ H⟨Δ⟩.≤ ℓ → ν′ ℓ′ ≡ ν′ ℓ → ℓ′ ≡ ℓ
        ν′-injective-on-related {ℓ′} {ℓ} ℓ′≤ℓ p = injective-on-related (H.M₁ ι₁-hom) ℓ′≤ℓ $
          H.M₁ ι₁-hom # ℓ′                         ≡˘⟨ μ-η H (ℓ̅ ℓ′) #ₚ _ ⟩
          H.μ Δ⁺ # (H.M₁ (ℓ̅ ℓ′) # (H.η Δ⁺ # ι₀ ⋆)) ≡⟨ p #ₚ (H.η _ # ι₀ ⋆) ⟩
          H.μ Δ⁺ # (H.M₁ (ℓ̅ ℓ) # (H.η Δ⁺ # ι₀ ⋆))  ≡⟨ μ-η H (ℓ̅ ℓ) #ₚ _ ⟩
          H.M₁ ι₁-hom # ℓ                          ∎

      abstract
        ℓ̅-σ̅ : ∀ {ℓ : ⌞ Fᴴ₀ Δ ⌟} (σ : SOrdᴴ.Hom (Fᴴ₀ Δ) (Fᴴ₀ Δ)) → ℓ̅ (σ # ℓ) ≡ H.μ _ ∘ H.M₁ (σ̅ σ) ∘ ℓ̅ ℓ
        ℓ̅-σ̅ {ℓ} σ = ext λ where
          (ι₀ ⋆) →
            H.M₁ ι₁-hom # (σ # ℓ)                                    ≡˘⟨ ap# (H.M₁ ι₁-hom ∘ σ .morphism) $ H.left-ident #ₚ ℓ ⟩
            H.M₁ ι₁-hom # (σ # (H.μ _ # (H.M₁ (H.η _) # ℓ)))         ≡˘⟨ ap# (H.M₁ ι₁-hom) $ μ-M-∘-Algebraic H σ (H.η Δ) #ₚ _ ⟩
            H.M₁ ι₁-hom # (H.μ _ # (H.M₁ (σ .morphism ∘ H.η _) # ℓ)) ≡˘⟨ μ-M-∘-M H ι₁-hom (σ .morphism ∘ H.η Δ) #ₚ _ ⟩
            H.μ _ # (H.M₁ (H.M₁ ι₁-hom ∘ σ .morphism ∘ H.η Δ) # ℓ)   ≡⟨ ap# (H.μ _) (σ̅-ι σ ℓ) ⟩
            H.μ _ # (H.M₁ (σ̅ σ) # (H.M₁ ι₁-hom # ℓ))                 ∎
          (ι₁ α) →
            H.η _ # ι₂ α                          ≡˘⟨ μ-η H (σ̅ σ) #ₚ _ ⟩
            H.μ _ # (H.M₁ (σ̅ σ) # (H.η _ # ι₂ α)) ∎
          (ι₂ α) →
            H.η _ # ι₂ α                          ≡˘⟨ μ-η H (σ̅ σ) #ₚ _ ⟩
            H.μ _ # (H.M₁ (σ̅ σ) # (H.η _ # ι₂ α)) ∎

      nt : liftᶠ-strict-orders F∘ Uᴴ F∘ Endos-include
        => Uᴹᴰ F∘ Endos-include F∘ T
      nt ._=>_.η _ .hom (lift ℓ) = pt , ν′ ℓ
      nt ._=>_.η _ .pres-≤[]-equal (lift ℓ≤ℓ′) =
        inc (biased refl (ν′-mono ℓ≤ℓ′)) , λ p → ap lift $ ν′-injective-on-related ℓ≤ℓ′ (ap snd p)
      nt ._=>_.is-natural _ _ σ = ext λ ℓ →
        refl , λ α →
          H.μ _ # (H.M₁ (ℓ̅ (σ # ℓ)) # α)                    ≡⟨ ap (λ m → (H.μ _ ∘ H.M₁ m) # α) (ℓ̅-σ̅ σ) ⟩
          H.μ _ # (H.M₁ (H.μ _ ∘ H.M₁ (σ̅ σ) ∘ ℓ̅ ℓ) # α)     ≡⟨ μ-M-∘-μ H (H.M₁ (σ̅ σ) ∘ ℓ̅ ℓ) #ₚ α ⟩
          H.μ _ # (H.μ _ # (H.M₁ (H.M₁ (σ̅ σ) ∘ (ℓ̅ ℓ)) # α)) ≡⟨ ap# (H.μ _) $ μ-M-∘-M H (σ̅ σ) (ℓ̅ ℓ) #ₚ α ⟩
          H.μ _ # (H.M₁ (σ̅ σ) # (H.μ _ # (H.M₁ (ℓ̅ ℓ) # α))) ∎
