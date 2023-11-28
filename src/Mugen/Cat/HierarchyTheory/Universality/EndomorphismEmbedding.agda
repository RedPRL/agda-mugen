-- vim: nowrap
module Mugen.Cat.HierarchyTheory.Universality.EndomorphismEmbedding where

open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Properties
open import Cat.Diagram.Monad

import Cat.Reasoning as Cat
import Cat.Functor.Reasoning as FR

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Endomorphism

open import Mugen.Cat.Endomorphisms
open import Mugen.Cat.StrictOrders
open import Mugen.Cat.Monad
open import Mugen.Cat.HierarchyTheory
open import Mugen.Cat.McBrideMonad

open import Mugen.Order.Coproduct
open import Mugen.Order.LeftInvariantRightCentered
open import Mugen.Order.Poset
open import Mugen.Order.Singleton
open import Mugen.Order.Discrete

import Mugen.Order.Reasoning

--------------------------------------------------------------------------------
-- The Universal Embedding Theorem
-- Section 3.4, Lemma 3.8
--
-- Given a hierarchy theory 'H', a strict order Δ, and a set Ψ, we can
-- construct a faithful functor 'T : Endos (Fᴴ Δ) → Endos Fᴹᴰ Ψ', where
-- 'Fᴴ' denotes the free H-algebra on Δ, and 'Fᴹᴰ Ψ' denotes the free McBride
-- Hierarchy theory over the endomorphism displacement algebra on 'H (◆ ⊕ Δ ⊕ Δ)'.

module _ {o r} (H : Hierarchy-theory o r) (Δ : Poset o r) (Ψ : Set (lsuc o ⊔ lsuc r)) where
  open Strictly-monotone
  open Algebra-hom
  open Cat (Strict-orders o r)

  --------------------------------------------------------------------------------
  -- Notation
  --
  -- We begin by defining some useful notation.

  private
    Δ⁺ : Poset o r
    Δ⁺ = ◆ ⊕ (Δ ⊕ Δ)

    𝒟 : Displacement-algebra (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)
    𝒟 = Endo∘ H Δ⁺

    SOrd : Precategory (lsuc o ⊔ lsuc r) (o ⊔ r)
    SOrd = Strict-orders o r

    SOrdᴴ : Precategory (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)
    SOrdᴴ = Eilenberg-Moore SOrd H

    -- Favonia: TODO: check why so many lsuc's
    --
    SOrd′ : Precategory (lsuc (lsuc o) ⊔ lsuc (lsuc r)) (lsuc o ⊔ lsuc r)
    SOrd′ = Strict-orders (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)

    SOrdᴹᴰ : Precategory (lsuc (lsuc o) ⊔ lsuc (lsuc r)) (lsuc (lsuc o) ⊔ lsuc (lsuc r))
    SOrdᴹᴰ = Eilenberg-Moore SOrd′ (ℳ 𝒟)

    Fᴴ⟨_⟩ : Poset o r → Algebra SOrd H
    Fᴴ⟨_⟩ = Functor.F₀ (Free SOrd H)

    Endoᴴ⟨Δ⟩ : Type (o ⊔ r)
    Endoᴴ⟨Δ⟩ = Hom (fst Fᴴ⟨ Δ ⟩) (fst Fᴴ⟨ Δ ⟩)

    Fᴹᴰ⟨_⟩ : Poset (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r) → Algebra (Strict-orders (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)) (ℳ 𝒟)
    Fᴹᴰ⟨_⟩ = Functor.F₀ (Free (Strict-orders (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)) (ℳ 𝒟))

    module Δ = Poset Δ

    module 𝒟 = Displacement-algebra 𝒟
    module H = Monad H
    module HR = FR H.M
    module ℳᴰ = Monad (ℳ 𝒟)
    module H⟨Δ⁺⟩ = Poset (H.M₀ Δ⁺)
    module H⟨Δ⟩ = Poset (H.M₀ Δ)
    module Fᴹᴰ⟨Δ⁺⟩ = Poset (fst Fᴹᴰ⟨ Lift≤ (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r) Δ⁺ ⟩)
    module Fᴹᴰ⟨Ψ⟩ = Poset (fst Fᴹᴰ⟨ Disc Ψ ⟩)
    module H⟨Δ⁺⟩→ = Displacement-algebra (Endo∘ H Δ⁺)
    module SOrd {o} {r} = Cat (Strict-orders o r)
    module SOrdᴴ = Cat (SOrdᴴ)
    module SOrdᴹᴰ = Cat (SOrdᴹᴰ)

    pattern ⋆ = lift tt
    pattern ι₀ α = inl α
    pattern ι₁ α = inr (inl α)
    pattern ι₂ α = inr (inr α)

    ι₀-inj : ∀ {x y : ⌞ ◆ {o = o} {r = r} ⌟} → _≡_ {A =  ⌞ Δ⁺ ⌟} (ι₀ x) (ι₀ y) → x ≡ y
    ι₀-inj _ = refl

    ι₁-inj : ∀ {x y : ⌞ Δ ⌟} → _≡_ {A =  ⌞ Δ⁺ ⌟} (ι₁ x) (ι₁ y) → x ≡ y
    ι₁-inj = inl-inj ⊙ inr-inj

    ι₂-inj : ∀ {x y : ⌞ Δ ⌟} → _≡_ {A =  ⌞ Δ⁺ ⌟} (ι₂ x) (ι₂ y) → x ≡ y
    ι₂-inj = inr-inj ⊙ inr-inj

    ι₁-hom : Hom Δ Δ⁺
    ι₁-hom .hom = ι₁
    ι₁-hom .mono α≤β = α≤β
    ι₁-hom .inj-on-related _ = ι₁-inj

    ι₁-monic : SOrd.is-monic ι₁-hom
    ι₁-monic g h p = ext λ α → ι₁-inj (p #ₚ α)


  --------------------------------------------------------------------------------
  -- Construction of the functor T
  -- Section 3.4, Lemma 3.8

  σ̅ : Algebra-hom SOrd H Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩ → Hom Δ⁺ (H.M₀ Δ⁺)
  σ̅ σ .hom (ι₀ α) = H.unit.η _ # ι₀ α
  σ̅ σ .hom (ι₁ α) = H.M₁ ι₁-hom # (σ # (H.unit.η Δ # α))
  σ̅ σ .hom (ι₂ α) = H.unit.η _ # ι₂ α
  σ̅ σ .mono {ι₀ ⋆} {ι₀ ⋆} _ = H⟨Δ⁺⟩.≤-refl
  σ̅ σ .mono {ι₁ α} {ι₁ β} α≤β = (H.M₁ ι₁-hom ∘ σ .morphism ∘ H.unit.η Δ) .mono α≤β
  σ̅ σ .mono {ι₂ α} {ι₂ β} α≤β = H.unit.η Δ⁺ .mono α≤β
  σ̅ σ .inj-on-related {ι₀ ⋆} {ι₀ ⋆} _ _ = refl
  σ̅ σ .inj-on-related {ι₁ α} {ι₁ β} α≤β p = ap ι₁ $ (H.M₁ ι₁-hom ∘ σ .morphism ∘ H.unit.η Δ) .inj-on-related α≤β p
  σ̅ σ .inj-on-related {ι₂ α} {ι₂ β} α≤β p = H.unit.η Δ⁺ .inj-on-related α≤β p

  module _ where abstract
    σ̅-id : σ̅ SOrdᴴ.id ≡ H.unit.η _
    σ̅-id = ext λ where
      (ι₀ α) → refl
      (ι₁ α) → sym (H.unit.is-natural _ _ ι₁-hom) #ₚ α
      (ι₂ α) → refl

  module _ where abstract
    σ̅-ι
      : ∀ (σ : Algebra-hom _ H Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩)
      → (α : ⌞ H.M₀ Δ ⌟)
      → H.M₁ (H.M₁ ι₁-hom) # (H.M₁ (σ .morphism) # (H.M₁ (H.unit.η Δ) # α))
      ≡ H.M₁ (σ̅ σ) # (H.M₁ ι₁-hom # α)
    σ̅-ι σ α =
      (H.M₁ (H.M₁ ι₁-hom) ∘ H.M₁ (σ .morphism) ∘ H.M₁ (H.unit.η Δ)) # α ≡˘⟨ ap (H.M₁ (H.M₁ ι₁-hom) ∘_) (H.M-∘ _ _) #ₚ α ⟩
      (H.M₁ (H.M₁ ι₁-hom) ∘ H.M₁ (σ .morphism ∘ H.unit.η Δ)) # α        ≡˘⟨ H.M-∘ _ _ #ₚ α ⟩
      H.M₁ (H.M₁ ι₁-hom ∘ σ .morphism ∘ H.unit.η Δ) # α                 ≡⟨ ap H.M₁ lemma #ₚ α ⟩
      H.M₁ (σ̅ σ ∘ ι₁-hom) # α                                           ≡⟨ H.M-∘ _ _ #ₚ α ⟩
      H.M₁ (σ̅ σ) # (H.M₁ ι₁-hom # α)                                    ∎
      where
        lemma : H.M₁ ι₁-hom ∘ σ .morphism ∘ H.unit.η _ ≡ σ̅ σ ∘ ι₁-hom
        lemma = ext λ _ → refl

  module _ where abstract
    σ̅-∘ : ∀ (σ δ : Algebra-hom _ H Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩) → σ̅ (σ SOrdᴴ.∘ δ) ≡ H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ σ̅ δ
    σ̅-∘ σ δ = ext λ where
      (ι₀ α) →
        H.unit.η Δ⁺ # ι₀ α                                        ≡˘⟨ H.right-ident #ₚ _ ⟩
        H.mult.η Δ⁺ # (H.unit.η (H.M₀ Δ⁺) # (H.unit.η Δ⁺ # ι₀ α)) ≡⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (σ̅ σ) #ₚ ι₀ α) ⟩
        H.mult.η Δ⁺ # (H.M₁ (σ̅ σ) # (H.unit.η Δ⁺ # ι₀ α))         ∎
      (ι₁ α) →
        H.M₁ ι₁-hom # (σ # (δ # (H.unit.η Δ # α)))                                                              ≡˘⟨ ap (λ e → H.M₁ ι₁-hom # (σ # e)) (H.left-ident #ₚ _) ⟩
        H.M₁ ι₁-hom # (σ # (H.mult.η _ # (H.M₁ (H.unit.η _) # (δ # (H.unit.η Δ # α)))))                         ≡⟨ ap (H.M₁ ι₁-hom #_) (σ .commutes #ₚ _) ⟩
        H.M₁ ι₁-hom # (H.mult.η _ # (H.M₁ (σ .morphism) # (H.M₁ (H.unit.η _) # (δ # (H.unit.η _ # α)))))        ≡˘⟨ H.mult.is-natural _ _ ι₁-hom #ₚ _ ⟩
        H.mult.η _ # (H.M₁ (H.M₁ ι₁-hom) # (H.M₁ (σ .morphism) # (H.M₁ (H.unit.η _) # (δ # (H.unit.η _ # α))))) ≡⟨ ap (H.mult.η _ #_) (σ̅-ι σ (δ # (H.unit.η _ # α))) ⟩
        H.mult.η _ # (H.M₁ (σ̅ σ) # (H.M₁ ι₁-hom # (δ # (H.unit.η _ # α))) ) ∎
      (ι₂ α) →
        H.unit.η _ # ι₂ α                               ≡˘⟨ H.right-ident #ₚ _ ⟩
        H.mult.η _ # (H.unit.η _ # (H.unit.η _ # ι₂ α)) ≡⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (σ̅ σ) #ₚ (ι₂ α)) ⟩
        H.mult.η _ # (H.M₁ (σ̅ σ) # (H.unit.η _ # ι₂ α)) ∎


  T′ : (σ : Algebra-hom (Strict-orders o r) H Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩) → Algebra-hom (Strict-orders o r) H Fᴴ⟨ Δ⁺ ⟩ Fᴴ⟨ Δ⁺ ⟩
  T′ σ .morphism = H.mult.η Δ⁺ ∘ H.M₁ (σ̅ σ)
  T′ σ .commutes = ext λ α →
    H.mult.η Δ⁺ # (H.M₁ (σ̅ σ) # (H.mult.η _ # α))              ≡˘⟨ ap (H.mult.η _ #_) (H.mult.is-natural _ _ (σ̅ σ) #ₚ α) ⟩
    H.mult.η _ # (H.mult.η _ # (H.M₁ (H.M₁ (σ̅ σ)) # α))        ≡˘⟨ H.mult-assoc #ₚ ((H.M₁ (H.M₁ (σ̅ σ))) # α) ⟩
    H.mult.η _ # (H.M₁ (H.mult.η _) # (H.M₁ (H.M₁ (σ̅ σ)) # α)) ≡˘⟨ ap (H.mult.η _ #_) (H.M-∘ (H.mult.η _) (H.M₁ (σ̅ σ)) #ₚ α) ⟩
    H.mult.η _ # (H.M₁ (H.mult.η _ ∘ H.M₁ (σ̅ σ)) # α)          ∎


  T : Functor (Endos SOrdᴴ Fᴴ⟨ Δ ⟩) (Endos SOrdᴹᴰ Fᴹᴰ⟨ Disc Ψ ⟩)
  T = functor
    where
      functor : Functor (Endos SOrdᴴ Fᴴ⟨ Δ ⟩) (Endos SOrdᴹᴰ Fᴹᴰ⟨ Disc Ψ ⟩)
      functor .Functor.F₀ _ = tt
      functor .Functor.F₁ σ .morphism .hom (α , d) = α , (T′ σ SOrdᴴ.∘ d)
      functor .Functor.F₁ σ .morphism .mono {α , d1} {β , d2} p =
        inc (biased (⋉-fst-invariant p) (𝒟.≤-left-invariant {T′ σ} {d1} {d2} (⋉-snd-invariant p)))
      functor .Functor.F₁ σ .morphism .inj-on-related {α , d1} {β , d2} p q i =
        fst (q i) , 𝒟.injr-on-≤ (⋉-snd-invariant p) (ap snd q) i
      functor .Functor.F₁ σ .commutes = trivial!
      functor .Functor.F-id = ext λ (α , d) →
        refl , λ β →
          H.mult.η _ # (H.M₁ (σ̅ SOrdᴴ.id) # (d # β)) ≡⟨ ap (λ e → H.mult.η _ # (H.M₁ e # (d # β))) σ̅-id ⟩
          H.mult.η _ # (H.M₁ (H.unit.η _) # (d # β)) ≡⟨ (H.left-ident #ₚ _) ⟩
          d # β ∎
      functor .Functor.F-∘ σ δ = ext λ (α , d) →
        refl , λ β →
          H.mult.η _ # (H.M₁ (σ̅ (σ SOrdᴴ.∘ δ)) # (d # β))                                 ≡⟨ ap (λ e → H.mult.η _ # (H.M₁ e # (d # β))) (σ̅-∘ σ δ) ⟩
          H.mult.η _ # (H.M₁ (H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ σ̅ δ) # (d # β))                   ≡⟨ ap (λ e → H.mult.η _ # (e # (d # β))) (H.M-∘ _ _ ∙ ap (H.M₁ (H.mult.η _) ∘_) (H.M-∘ _ _)) ⟩
          H.mult.η _ # (H.M₁ (H.mult.η _) # (H.M₁ (H.M₁ (σ̅ σ)) # (H.M₁ (σ̅ δ) # (d # β)))) ≡⟨ H.mult-assoc #ₚ _ ⟩
          H.mult.η _ # (H.mult.η _ # (H.M₁ (H.M₁ (σ̅ σ)) # (H.M₁ (σ̅ δ) # (d # β))))        ≡⟨ ap (H.mult.η _ #_) (H.mult.is-natural _ _ (σ̅ σ) #ₚ _) ⟩
          H.mult.η _ # (H.M₁ (σ̅ σ) # (H.mult.η _ # (H.M₁ (σ̅ δ) # (d # β))))               ∎

  --------------------------------------------------------------------------------
  -- NOTE: Forgetful Functors + Levels
  --
  -- To avoid dealing with an annoying level shifting functor, we bake in the
  -- required lifts into Uᴴ instead.

  Uᴴ : ∀ {X} → Functor (Endos SOrdᴴ X) (Strict-orders (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r))
  Uᴴ {X} .Functor.F₀ _ = Lift≤ _ _ (fst X)
  Uᴴ .Functor.F₁ σ .hom (lift α) = lift (σ # α)
  Uᴴ .Functor.F₁ σ .mono (lift α≤β) = lift (σ .morphism .mono α≤β)
  Uᴴ .Functor.F₁ σ .inj-on-related (lift α≤β) p = ap lift (σ .morphism .inj-on-related α≤β (lift-inj p))
  Uᴴ .Functor.F-id = ext λ _ → refl
  Uᴴ .Functor.F-∘ _ _ = ext λ _ → refl

  Uᴹᴰ : ∀ {X} → Functor (Endos SOrdᴹᴰ X) (Strict-orders (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r))
  Uᴹᴰ {X} .Functor.F₀ _ = fst X
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
      ℓ̅ ℓ .mono {ι₀ ⋆} {ι₀ ⋆} _ = H⟨Δ⁺⟩.≤-refl
      ℓ̅ ℓ .mono {ι₁ α} {ι₁ β} α≤β = H.unit.η _ .mono α≤β
      ℓ̅ ℓ .mono {ι₂ α} {ι₂ β} α≤β = H.unit.η _ .mono α≤β
      ℓ̅ ℓ .inj-on-related {ι₀ ⋆} {ι₀ ⋆} α≤β _ = refl
      ℓ̅ ℓ .inj-on-related {ι₁ α} {ι₁ β} α≤β p = ap ι₁ $ ι₂-inj $ H.unit.η _ .inj-on-related α≤β p
      ℓ̅ ℓ .inj-on-related {ι₂ α} {ι₂ β} α≤β p = H.unit.η _ .inj-on-related α≤β p

      module _ where abstract
        ℓ̅-mono : ∀ {ℓ ℓ′} → ℓ′ H⟨Δ⟩.≤ ℓ → ∀ (α :  ⌞ Δ⁺ ⌟) → ℓ̅ ℓ′ # α H⟨Δ⁺⟩.≤ ℓ̅ ℓ # α
        ℓ̅-mono ℓ′≤ℓ (ι₀ _) = (H.M₁ ι₁-hom .mono ℓ′≤ℓ)
        ℓ̅-mono ℓ′≤ℓ (ι₁ _) = H⟨Δ⁺⟩.≤-refl
        ℓ̅-mono ℓ′≤ℓ (ι₂ _) = H⟨Δ⁺⟩.≤-refl

      ν′ : ⌞ H.M₀ Δ ⌟ → Algebra-hom _ H Fᴴ⟨ Δ⁺ ⟩ Fᴴ⟨ Δ⁺ ⟩
      ν′ ℓ .morphism = H.mult.η _ ∘ H.M₁ (ℓ̅ ℓ)
      ν′ ℓ .commutes = ext λ α →
        H.mult.η _ # (H.M₁ (ℓ̅ ℓ) # (H.mult.η _ # α))               ≡˘⟨ ap (H.mult.η _ #_) (H.mult.is-natural _ _ (ℓ̅ ℓ) #ₚ α) ⟩
        H.mult.η _ # (H.mult.η _ # (H.M₁ (H.M₁ (ℓ̅ ℓ)) # α))        ≡˘⟨ H.mult-assoc #ₚ _ ⟩
        H.mult.η _ # (H.M₁ (H.mult.η _) # (H.M₁ (H.M₁ (ℓ̅ ℓ)) # α)) ≡˘⟨ ap (H.mult.η _ #_) (H.M-∘ _ _ #ₚ α) ⟩
        H.mult.η _ # (H.M₁ (H.mult.η _ ∘ H.M₁ (ℓ̅ ℓ)) # α)          ∎

      module _ where abstract
        ν′-mono : ∀ {ℓ′ ℓ : ⌞ H.M₀ Δ ⌟} → ℓ′ H⟨Δ⟩.≤ ℓ → ν′ ℓ′ H⟨Δ⁺⟩→.≤ ν′ ℓ
        ν′-mono {ℓ′} {ℓ} ℓ′≤ℓ .Lift.lower α =
          H.mult.η _ # (H.M₁ (ℓ̅ ℓ′) # (H.unit.η _ # α)) ≐⟨ ap (H.mult.η _ #_) (sym $ H.unit.is-natural _ _ (ℓ̅ ℓ′) #ₚ α) ⟩
          H.mult.η _ # (H.unit.η _ # (ℓ̅ ℓ′ # α))        ≤⟨ mono (H.mult.η _ ∘ H.unit.η _) (ℓ̅-mono ℓ′≤ℓ α) ⟩
          H.mult.η _ # (H.unit.η _ # (ℓ̅ ℓ # α))         ≐⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (ℓ̅ ℓ) #ₚ α) ⟩
          H.mult.η _ # (H.M₁ (ℓ̅ ℓ) # (H.unit.η _ # α))  ≤∎
          where
            open Mugen.Order.Reasoning (H.M₀ Δ⁺)

      module _ where abstract
        ν′-inj-on-≤ : ∀ {ℓ′ ℓ : ⌞ H.M₀ Δ ⌟} → ℓ′ H⟨Δ⟩.≤ ℓ → ν′ ℓ′ ≡ ν′ ℓ → ℓ′ ≡ ℓ
        ν′-inj-on-≤ {ℓ′} {ℓ} ℓ′≤ℓ p = (H.mult.η _ ∘ H.unit.η _ ∘ H.M₁ ι₁-hom) .inj-on-related ℓ′≤ℓ $
          H.mult.η _ # (H.unit.η _ # (H.M₁ ι₁-hom # ℓ′))   ≡⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (ℓ̅ ℓ′) #ₚ _) ⟩
          H.mult.η _ # (H.M₁ (ℓ̅ ℓ′) # (H.unit.η _ # ι₀ ⋆)) ≡⟨ ap (_# (H.unit.η _ # ι₀ ⋆)) p ⟩
          H.mult.η _ # (H.M₁ (ℓ̅ ℓ) # (H.unit.η _ # ι₀ ⋆))  ≡˘⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (ℓ̅ ℓ) #ₚ _) ⟩
          H.mult.η _ # (H.unit.η _ # (H.M₁ ι₁-hom # ℓ))    ∎

      module _ where abstract
        ℓ̅-σ̅ : ∀ {ℓ : ⌞ fst Fᴴ⟨ Δ ⟩ ⌟} (σ : Algebra-hom _ _ Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩) → ℓ̅ (σ # ℓ) ≡ H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ ℓ̅ ℓ
        ℓ̅-σ̅ {ℓ} σ = ext λ where
          (ι₀ ⋆) →
            H.M₁ ι₁-hom # (σ # ℓ)                                                              ≡˘⟨ ap (λ e → H.M₁ ι₁-hom # (σ # e)) (H.left-ident #ₚ ℓ) ⟩
            H.M₁ ι₁-hom # (σ # (H.mult.η _ # (H.M₁ (H.unit.η _) # ℓ)))                         ≡⟨ ap (H.M₁ ι₁-hom #_) (σ .commutes #ₚ _) ⟩
            H.M₁ ι₁-hom # (H.mult.η _ # (H.M₁ (σ .morphism) # (H.M₁ (H.unit.η _) # ℓ)))        ≡˘⟨ H.mult.is-natural _ _ ι₁-hom #ₚ _ ⟩
            H.mult.η _ # (H.M₁ (H.M₁ ι₁-hom) # (H.M₁ (σ .morphism) # (H.M₁ (H.unit.η _) # ℓ))) ≡⟨ ap (H.mult.η _ #_) (σ̅-ι σ ℓ) ⟩
            H.mult.η _ # (H.M₁ (σ̅ σ) # (H.M₁ ι₁-hom # ℓ))                                      ∎
          (ι₁ α) →
            H.unit.η _ # ι₂ α                               ≡˘⟨ H.right-ident #ₚ _ ⟩
            H.mult.η _ # (H.unit.η _ # (H.unit.η _ # ι₂ α)) ≡⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (σ̅ σ) #ₚ (ι₂ α)) ⟩
            H.mult.η _ # (H.M₁ (σ̅ σ) # (H.unit.η _ # ι₂ α)) ∎
          (ι₂ α) →
            H.unit.η _ # ι₂ α                               ≡˘⟨ H.right-ident #ₚ _ ⟩
            H.mult.η _ # (H.unit.η _ # (H.unit.η _ # ι₂ α)) ≡⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (σ̅ σ) #ₚ (ι₂ α)) ⟩
            H.mult.η _ # (H.M₁ (σ̅ σ) # (H.unit.η _ # ι₂ α)) ∎

      nt : Uᴴ => Uᴹᴰ F∘ T
      nt ._=>_.η _ .hom (lift ℓ) = pt , ν′ ℓ
      nt ._=>_.η _ .mono (lift ℓ≤ℓ′) = inc (biased refl (ν′-mono ℓ≤ℓ′))
      nt ._=>_.η _ .inj-on-related (lift ℓ≤ℓ′) p = ap lift $ ν′-inj-on-≤ ℓ≤ℓ′ (ap snd p)
      nt ._=>_.is-natural _ _ σ = ext λ ℓ →
        refl , λ α →
          H.mult.η _ # (H.M₁ (ℓ̅ (σ # ℓ .Lift.lower)) # α)                                         ≡⟨ ap (λ e → (H.mult.η _ ∘ H.M₁ e) # α) (ℓ̅-σ̅ σ) ⟩
          H.mult.η _ # (H.M₁ (H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ ℓ̅ (ℓ .Lift.lower)) # α)                   ≡⟨ ap (H.mult.η _ #_) ((H.M-∘ _ _  ∙ ((refl⟩∘⟨ H.M-∘ _ _))) #ₚ α) ⟩
          H.mult.η _ # (H.M₁ (H.mult.η _) # (H.M₁ (H.M₁ (σ̅ σ)) # (H.M₁ (ℓ̅ (ℓ .Lift.lower)) # α))) ≡⟨ H.mult-assoc #ₚ _ ⟩
          H.mult.η _ # (H.mult.η _ # (H.M₁ (H.M₁ (σ̅ σ)) # (H.M₁ (ℓ̅ (ℓ .Lift.lower)) # α)))        ≡⟨ ap (H.mult.η _ #_) (H.mult.is-natural _ _ (σ̅ σ) #ₚ _) ⟩
          H.mult.η _ # (H.M₁ (σ̅ σ) # (H.mult.η _ # (H.M₁ (ℓ̅ (ℓ .Lift.lower)) # α))) ∎

  --------------------------------------------------------------------------------
  -- Faithfulness of T
  -- Section 3.4, Lemma 3.8

  module _ where abstract
    T-faithful : ∣ Ψ ∣ → preserves-monos H → is-faithful T
    T-faithful pt H-preserves-monos {x} {y} {σ} {δ} p =
      free-algebra-hom-path H $ H-preserves-monos ι₁-hom ι₁-monic _ _ $
      ext λ α →
      σ̅ σ # (ι₁ α)                                    ≡˘⟨ H.right-ident #ₚ _ ⟩
      H.mult.η _ # (H.unit.η _ # (σ̅ σ #  (ι₁ α)))     ≡⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (σ̅ σ) #ₚ _) ⟩
      H.mult.η _ # (H.M₁ (σ̅ σ) # (H.unit.η _ # ι₁ α)) ≡⟨ (ap snd (p #ₚ (pt , SOrdᴴ.id)) #ₚ _) ⟩
      H.mult.η _ # (H.M₁ (σ̅ δ) # (H.unit.η _ # ι₁ α)) ≡˘⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (σ̅ δ) #ₚ _) ⟩
      H.mult.η _ # (H.unit.η _ # (σ̅ δ #  (ι₁ α)))     ≡⟨ H.right-ident #ₚ _ ⟩
      σ̅ δ # (ι₁ α)                                    ∎
