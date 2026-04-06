-- vim: nowrap
open import Order.Instances.Discrete
open import Order.Instances.Coproduct

open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Morphism
open import Cat.Functor.Properties
open import Cat.Diagram.Monad
open import Cat.Displayed.Total

import Cat.Reasoning as Cat

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Instances.Endomorphism

open import Mugen.Cat.Instances.Endomorphisms
open import Mugen.Cat.Instances.StrictOrders
open import Mugen.Cat.Monad
open import Mugen.Cat.HierarchyTheory
open import Mugen.Cat.HierarchyTheory.McBride

open import Mugen.Order.StrictOrder
open import Mugen.Order.Instances.Endomorphism renaming (Endomorphism to Endomorphism-poset)
import Mugen.Order.Instances.LeftInvariantRightCentred as LeftInvariantRightCentred

import Mugen.Order.Reasoning as Reasoning

--------------------------------------------------------------------------------
-- The Universal Embedding Theorem
-- Section 3.4, Lemma 3.8
--
-- Given a hierarchy theory 'H', a poset Δ, and a set Ψ, we can
-- construct a faithful functor 'T : Endos (Fᴴ Δ) → Endos Fᴹᴰ Ψ', where
-- 'Fᴴ' denotes the free H-algebra on Δ, and 'Fᴹᴰ Ψ' denotes the free McBride
-- Hierarchy theory over the endomorphism displacement algebra on 'H (◆ ⊕ Δ ⊕ Δ)'.
--
-- Naturality is in a different file

module Mugen.Cat.HierarchyTheory.Universality.EndomorphismEmbedding
  {o r} {F : Functor (Strict-orders o r) (Strict-orders o r)}
  (H : Hierarchy-theory-on F) (Δ : Poset o r) (Ψ : Set (o ⊔ r)) where

  --------------------------------------------------------------------------------
  -- Notation
  --
  -- We begin by defining some useful notation.

  private
    open Strictly-monotone
    open ∫Hom
    open Cat (Strict-orders o r)
    module Δ = Poset Δ
    module H = Monad-on H

  -- made public for the naturality proof in a different file
  Δ⁺ : Poset o r
  Δ⁺ = 𝟙ᵖ {o = o} {ℓ = r} ⊎ᵖ (Δ ⊎ᵖ Δ)

  private
    H⟨Δ⁺⟩ : Poset o r
    H⟨Δ⁺⟩ = H.M₀ Δ⁺
    module H⟨Δ⁺⟩ = Reasoning H⟨Δ⁺⟩

    H⟨Δ⁺⟩→ : Poset (o ⊔ r) (o ⊔ r)
    H⟨Δ⁺⟩→ = Endomorphism-poset H Δ⁺
    module H⟨Δ⁺⟩→ = Reasoning H⟨Δ⁺⟩→

  𝒟 : Displacement-on H⟨Δ⁺⟩→
  𝒟 = Endomorphism H Δ⁺
  module 𝒟 = Displacement-on 𝒟

  private
    SOrd : Precategory (lsuc (o ⊔ r)) (o ⊔ r)
    SOrd = Strict-orders o r
    module SOrd = Cat SOrd

    SOrdᴴ : Precategory (lsuc (o ⊔ r)) (o ⊔ r)
    SOrdᴴ = Eilenberg-Moore {C = SOrd} H
    module SOrdᴴ = Cat SOrdᴴ

    -- '↑' for lifting
    SOrd↑ : Precategory (lsuc (o ⊔ r)) (o ⊔ r)
    SOrd↑ = Strict-orders (o ⊔ r) (o ⊔ r)

    SOrdᴹᴰ : Precategory (lsuc (o ⊔ r)) (o ⊔ r)
    SOrdᴹᴰ = Eilenberg-Moore {C = SOrd↑} (McBride 𝒟)
    module SOrdᴹᴰ = Cat SOrdᴹᴰ

    Fᴴ₀ : Poset o r → Algebra H
    Fᴴ₀ = Free-EM .Functor.F₀

    Fᴹᴰ₀ : Poset (o ⊔ r) (o ⊔ r) → Algebra (McBride 𝒟)
    Fᴹᴰ₀ = Free-EM .Functor.F₀

  -- These patterns and definitions are exported for the naturality proof
  -- in another file.

  pattern ⋆ = lift tt

  pattern ι₀ α = inl α

  ι₀-hom : Hom 𝟙ᵖ Δ⁺
  ι₀-hom .hom = ι₀
  ι₀-hom .pres-≤[]-equal α≤β = lift α≤β , λ _ → refl

  pattern ι₁ α = inr (inl α)

  ι₁-inj : ∀ {x y : ⌞ Δ ⌟} → _≡_ {A =  ⌞ Δ⁺ ⌟} (ι₁ x) (ι₁ y) → x ≡ y
  ι₁-inj = inl-inj ⊙ inr-inj

  ι₁-hom : Hom Δ Δ⁺
  ι₁-hom .hom = ι₁
  ι₁-hom .pres-≤[]-equal α≤β = lift (lift α≤β) , ι₁-inj

  ι₁-monic : SOrd.is-monic ι₁-hom
  ι₁-monic g h p = ext λ α → ι₁-inj (p ·ₚ α)

  pattern ι₂ α = inr (inr α)

  ι₂-inj : ∀ {x y : ⌞ Δ ⌟} → _≡_ {A =  ⌞ Δ⁺ ⌟} (ι₂ x) (ι₂ y) → x ≡ y
  ι₂-inj = inr-inj ⊙ inr-inj


  --------------------------------------------------------------------------------
  -- Construction of the functor T
  -- Section 3.4, Lemma 3.8

  σ̅ : SOrdᴴ.Hom (Fᴴ₀ Δ) (Fᴴ₀ Δ) → Hom Δ⁺ H⟨Δ⁺⟩
  σ̅ σ .hom (ι₀ ⋆) = H.η Δ⁺ · ι₀ ⋆
  σ̅ σ .hom (ι₁ α) = H.M₁ ι₁-hom · (σ · (H.η Δ · α))
  σ̅ σ .hom (ι₂ α) = H.η Δ⁺ · ι₂ α
  σ̅ σ .pres-≤[]-equal {ι₀ ⋆} {ι₀ ⋆} _ = H⟨Δ⁺⟩.≤-refl , λ _ → refl
  σ̅ σ .pres-≤[]-equal {ι₁ α} {ι₁ β} (lift (lift α≤β)) =
    H⟨Δ⁺⟩.≤[]-map (ap ι₁) $ (H.M₁ ι₁-hom ∘ σ .fst ∘ H.η Δ) .pres-≤[]-equal α≤β
  σ̅ σ .pres-≤[]-equal {ι₂ α} {ι₂ β} α≤β = H.η Δ⁺ .pres-≤[]-equal α≤β

  abstract
    σ̅-id : σ̅ SOrdᴴ.id ≡ H.η Δ⁺
    σ̅-id = ext λ where
      (ι₀ α) → refl
      (ι₁ α) → sym (H.unit.is-natural Δ Δ⁺ ι₁-hom) ·ₚ α
      (ι₂ α) → refl

  abstract
    σ̅-ι
      : ∀ (σ : SOrdᴴ.Hom (Fᴴ₀ Δ) (Fᴴ₀ Δ))
      → (α : ⌞ H.M₀ Δ ⌟)
      → H.M₁ (H.M₁ ι₁-hom ∘ σ .fst ∘ H.η Δ) · α
      ≡ H.M₁ (σ̅ σ) · (H.M₁ ι₁-hom · α)
    σ̅-ι σ α =
      H.M₁ (H.M₁ ι₁-hom ∘ σ .fst ∘ H.η Δ) · α ≡⟨ ap (λ m → H.M₁ m · α) $ ext (λ _ → refl) ⟩
      H.M₁ (σ̅ σ ∘ ι₁-hom) · α                 ≡⟨ H.M-∘ _ _ ·ₚ α ⟩
      H.M₁ (σ̅ σ) · (H.M₁ ι₁-hom · α)          ∎

  abstract
    σ̅-∘ : ∀ (σ δ : SOrdᴴ.Hom (Fᴴ₀ Δ) (Fᴴ₀ Δ)) → σ̅ (σ SOrdᴴ.∘ δ) ≡ H.μ Δ⁺ ∘ H.M₁ (σ̅ σ) ∘ σ̅ δ
    σ̅-∘ σ δ = ext λ where
      (ι₀ α) →
        H.η Δ⁺ · ι₀ α                           ≡˘⟨ μ-η H (σ̅ σ) ·ₚ ι₀ α ⟩
        H.μ Δ⁺ · (H.M₁ (σ̅ σ) · (H.η Δ⁺ · ι₀ α)) ∎
      (ι₁ α) →
        H.M₁ ι₁-hom · (σ · (δ · (H.η Δ · α)))                               ≡˘⟨ ap· (H.M₁ ι₁-hom ∘ σ .fst) $ H.μ-unitr ·ₚ _ ⟩
        H.M₁ ι₁-hom · (σ · (H.μ Δ · (H.M₁ (H.η Δ) · (δ · (H.η Δ · α)))))    ≡˘⟨ ap· (H.M₁ ι₁-hom) $ μ-M-∘-Algebraic H σ (H.η Δ) ·ₚ _ ⟩
        H.M₁ ι₁-hom · (H.μ _ · (H.M₁ (σ .fst ∘ H.η Δ) · (δ · (H.η Δ · α)))) ≡˘⟨ μ-M-∘-M H ι₁-hom (σ .fst ∘ H.η Δ) ·ₚ _ ⟩
        H.μ _ · (H.M₁ (H.M₁ ι₁-hom ∘ σ .fst ∘ H.η Δ) · (δ · (H.η Δ · α)))   ≡⟨ ap· (H.μ _) $ σ̅-ι σ (δ · (H.η _ · α)) ⟩
        H.μ _ · (H.M₁ (σ̅ σ) · (H.M₁ ι₁-hom · (δ · (H.η Δ · α))))            ∎
      (ι₂ α) →
        H.η Δ⁺ · ι₂ α                           ≡˘⟨ μ-η H (σ̅ σ) ·ₚ ι₂ α ⟩
        H.μ Δ⁺ · (H.M₁ (σ̅ σ) · (H.η Δ⁺ · ι₂ α)) ∎

  T′ : (σ : SOrdᴴ.Hom (Fᴴ₀ Δ) (Fᴴ₀ Δ)) → SOrdᴴ.Hom (Fᴴ₀ Δ⁺) (Fᴴ₀ Δ⁺)
  T′ σ .fst = H.μ Δ⁺ ∘ H.M₁ (σ̅ σ)
  T′ σ .snd = ext λ α →
    H.μ Δ⁺ · (H.M₁ (σ̅ σ) · (H.μ Δ⁺ · α))               ≡˘⟨ ap· (H.μ _) $ H.mult.is-natural _ _ (σ̅ σ) ·ₚ α ⟩
    H.μ Δ⁺ · (H.μ (H.M₀ Δ⁺) · (H.M₁ (H.M₁ (σ̅ σ)) · α)) ≡˘⟨ μ-M-∘-μ H (H.M₁ (σ̅ σ)) ·ₚ α ⟩
    H.μ Δ⁺ · (H.M₁ (H.μ Δ⁺ ∘ H.M₁ (σ̅ σ)) · α)          ∎

  T : Functor (Endos SOrdᴴ (Fᴴ₀ Δ)) (Endos SOrdᴹᴰ (Fᴹᴰ₀ (Disc Ψ)))
  T .Functor.F₀ _ = tt
  T .Functor.F₁ σ .fst .hom (α , d) = α , (T′ σ SOrdᴴ.∘ d)
  T .Functor.F₁ σ .fst .pres-≤[]-equal {α1 , d1} {α2 , d2} p =
    let module ⋉ = LeftInvariantRightCentred (Disc Ψ) H⟨Δ⁺⟩→ 𝒟.ε in
    let d1≤d2 , injr = 𝒟.left-strict-invariant {T′ σ} {d1} {d2} (⋉.≤-snd-invariant p) in
    inc (⋉.biased (⋉.≤-fst-invariant p) d1≤d2) , λ q i → q i .fst , injr (ap snd q) i
  T .Functor.F₁ σ .snd = ext λ α d₁ d₂ →
    Σ-path refl (transport-refl _ ∙ SOrdᴴ.assoc (T′ σ) d₁ d₂)
  T .Functor.F-id = ext λ α d →
    Σ-path refl (transport-refl _ ∙ ext λ β →
      H.μ _ · (H.M₁ (σ̅ SOrdᴴ.id) · (d · β)) ≡⟨ ap (λ m → H.μ _ · (H.M₁ m · (d · β))) σ̅-id ⟩
      H.μ _ · (H.M₁ (H.η _) · (d · β))      ≡⟨ H.μ-unitr ·ₚ _ ⟩
      d · β                                 ∎)
  T .Functor.F-∘ σ δ = ext λ α d →
    Σ-path refl (transport-refl _ ∙ ext λ β →
      H.μ _ · (H.M₁ (σ̅ (σ SOrdᴴ.∘ δ)) · (d · β))              ≡⟨ ap (λ m → H.μ _ · (H.M₁ m · (d · β))) (σ̅-∘ σ δ) ⟩
      H.μ _ · (H.M₁ (H.μ _ ∘ H.M₁ (σ̅ σ) ∘ σ̅ δ) · (d · β))     ≡⟨ μ-M-∘-μ H (H.M₁ (σ̅ σ) ∘ σ̅ δ) ·ₚ (d · β) ⟩
      H.μ _ · (H.μ _ · (H.M₁ (H.M₁ (σ̅ σ) ∘ σ̅ δ) · (d · β)))   ≡⟨ ap· (H.μ _) $ μ-M-∘-M H (σ̅ σ) (σ̅ δ) ·ₚ (d · β) ⟩
      H.μ _ · (H.M₁ (σ̅ σ) · (H.μ _ · (H.M₁ (σ̅ δ) · (d · β)))) ∎)

  --------------------------------------------------------------------------------
  -- Faithfulness of T
  -- Section 3.4, Lemma 3.8

  abstract
    T-faithful : ∣ Ψ ∣ → preserves-monos F → is-faithful T
    T-faithful pt H-preserves-monos {x} {y} {σ} {δ} eq =
      free-algebra-hom-path H $ H-preserves-monos ι₁-monic _ _ $ ext λ α →
      σ̅ σ · ι₁ α                            ≡˘⟨ μ-η H (σ̅ σ) ·ₚ ι₁ α ⟩
      H.μ _ · (H.M₁ (σ̅ σ) · (H.η _ · ι₁ α)) ≡⟨ ap snd (eq ·ₚ (pt , SOrdᴴ.id)) ·ₚ (H.η _ · ι₁ α) ⟩
      H.μ _ · (H.M₁ (σ̅ δ) · (H.η _ · ι₁ α)) ≡⟨ μ-η H (σ̅ δ) ·ₚ ι₁ α ⟩
      σ̅ δ · ι₁ α                            ∎
