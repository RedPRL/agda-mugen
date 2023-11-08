module Mugen.Cat.HierarchyTheory.Properties where

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
open import Mugen.Cat.HierarchyTheory
open import Mugen.Cat.StrictOrders

open import Mugen.Order.Coproduct
open import Mugen.Order.LeftInvariantRightCentered
open import Mugen.Order.StrictOrder
open import Mugen.Order.Singleton
open import Mugen.Order.Discrete

import Mugen.Order.StrictOrder.Reasoning

--------------------------------------------------------------------------------
-- The Universal Embedding Theorem
-- Section 3.4, Lemma 3.8
--
-- Given a heirarchy theory 'H', a strict order Δ, and a set Ψ, we can
-- construct a faithful functor 'T : Endos (Fᴴ Δ) → Endos Fᴹᴰ Ψ', where
-- 'Fᴴ' denotes the free H-algebra on Δ, and 'Fᴹᴰ Ψ' denotes the free McBride
-- Heirarchy theory over the endomorphism displacement algebra on 'H (◆ ⊕ Δ ⊕ Δ)'.

module _ {o r} (H : Hierarchy-theory o r) (Δ : Strict-order o r) (Ψ : Set (lsuc o ⊔ lsuc r)) where
  open Strictly-monotone
  open Algebra-hom
  open Cat (Strict-orders o r)

  --------------------------------------------------------------------------------
  -- Notation
  --
  -- We begin by defining some useful notation.

  private
    Δ⁺ : Strict-order o r
    Δ⁺ = ◆ ⊕ (Δ ⊕ Δ)

    𝒟 : Displacement-algebra (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)
    𝒟 = Endo∘ H Δ⁺

    SOrdᴴ : Precategory (o ⊔ r ⊔ (lsuc o ⊔ lsuc r)) (o ⊔ r ⊔ (lsuc o ⊔ lsuc r))
    SOrdᴴ = Eilenberg-Moore _ H

    SOrdᴹᴰ : Precategory _ _
    SOrdᴹᴰ = Eilenberg-Moore _ (ℳ 𝒟)

    Fᴴ⟨_⟩ : Strict-order o r → Algebra (Strict-orders o r) H
    Fᴴ⟨_⟩ = Functor.F₀ (Free (Strict-orders o r) H)

    Fᴹᴰ⟨_⟩ : Strict-order (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r) → Algebra (Strict-orders (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)) (ℳ 𝒟)
    Fᴹᴰ⟨_⟩ = Functor.F₀ (Free (Strict-orders (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)) (ℳ 𝒟))

    module Δ = Strict-order Δ

    module 𝒟 = Displacement-algebra 𝒟
    module H = Monad H
    module HR = FR H.M
    module ℳᴰ = Monad (ℳ 𝒟)
    module H⟨Δ⁺⟩ = Strict-order (H.M₀ Δ⁺)
    module H⟨Δ⟩ = Strict-order (H.M₀ Δ)
    module Fᴹᴰ⟨Δ⁺⟩ = Strict-order (fst (Fᴹᴰ⟨ Lift< (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r) Δ⁺ ⟩))
    module Fᴹᴰ⟨Ψ⟩ = Strict-order (fst (Fᴹᴰ⟨ Disc Ψ ⟩))
    module H⟨Δ⁺⟩→ = Displacement-algebra (Endo∘ H Δ⁺)
    module SOrd {o} {r} = Cat (Strict-orders o r)
    module SOrdᴴ = Cat (SOrdᴴ)
    module SOrdᴹᴰ = Cat (SOrdᴹᴰ)

    pattern ⋆  = lift tt
    pattern ι₀ α = inl α
    pattern ι₁ α = inr (inl α)
    pattern ι₂ α = inr (inr α)

    ι₁-hom : Precategory.Hom (Strict-orders o r) Δ Δ⁺
    ι₁-hom .hom = ι₁
    ι₁-hom .strict-mono α<β = α<β

    ι₁-monic : SOrd.is-monic ι₁-hom
    ι₁-monic g h p = ext λ α →
      inl-inj (inr-inj (p #ₚ α))

  
  --------------------------------------------------------------------------------
  -- Construction of the functor T
  -- Section 3.4, Lemma 3.8

  σ̅ : (σ : Algebra-hom _ H Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩) → Hom Δ⁺ (H.M₀ Δ⁺)
  σ̅ σ .hom (ι₀ α) = H.unit.η _ # ι₀ α
  σ̅ σ .hom (ι₁ α) = H.M₁ ι₁-hom # (σ # (H.unit.η _ # α))
  σ̅ σ .hom (ι₂ α) = H.unit.η _ # ι₂ α
  σ̅ σ .strict-mono {ι₀ ⋆} {ι₀ ⋆} (lift ff) = absurd ff
  σ̅ σ .strict-mono {ι₁ α} {ι₁ β} α<β =  (H.M₁ ι₁-hom SOrd.∘ σ .morphism SOrd.∘ H.unit.η Δ) .strict-mono α<β
  σ̅ σ .strict-mono {ι₂ α} {ι₂ β} α<β = H.unit.η Δ⁺ .strict-mono α<β

  σ̅-id : σ̅ SOrdᴴ.id ≡ H.unit.η _
  σ̅-id = ext λ where
    (ι₀ α) → refl
    (ι₁ α) →  (sym (H.unit.is-natural _ _ ι₁-hom)) #ₚ α
    (ι₂ α) → refl

  σ̅-ι
    : ∀ (σ : Algebra-hom _ H Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩)
    → (α : ⌞ H.M₀ Δ ⌟)
    → H.M₁ (H.M₁ ι₁-hom) # (H.M₁ (σ .morphism) # (H.M₁ (H.unit.η _) # α))
    ≡ H.M₁ (σ̅ σ) # (H.M₁ ι₁-hom # α)
  σ̅-ι σ α =
    (H.M₁ (H.M₁ ι₁-hom) ∘ H.M₁ (σ .morphism) ∘ H.M₁ (H.unit.η _)) # α ≡˘⟨ (H.M-∘ _ _ ∙ ap (H.M₁ (H.M₁ ι₁-hom) ∘_) (H.M-∘ _ _)) #ₚ α ⟩
    H.M₁ (H.M₁ ι₁-hom ∘ σ .morphism ∘ H.unit.η _) # α                 ≡⟨ ap (λ e → H.M₁ e # α) lemma ⟩
    H.M₁ (σ̅ σ ∘ ι₁-hom) # α                                           ≡⟨ (H.M-∘ _ _ #ₚ α) ⟩
    H.M₁ (σ̅ σ) # (H.M₁ ι₁-hom # α)                                    ∎
    where
      lemma : H.M₁ ι₁-hom ∘ σ .morphism ∘ H.unit.η _ ≡ σ̅ σ ∘ ι₁-hom
      lemma = ext λ _ → refl

  σ̅-∘ : ∀ (σ δ : Algebra-hom _ H Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩) → σ̅ (σ SOrdᴴ.∘ δ) ≡ H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ σ̅ δ
  σ̅-∘ σ δ = ext λ where
      (ι₀ α) →
        H.unit.η _ # (ι₀ α)                               ≡˘⟨ H.right-ident #ₚ _ ⟩
        H.mult.η _ # (H.unit.η _ # (H.unit.η _ # ι₀ α))   ≡⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (σ̅ σ) #ₚ ι₀ α) ⟩
        H.mult.η _ # (H.M₁ (σ̅ σ) # (H.unit.η _ # (ι₀ α))) ∎
      (ι₁ α) →
        H.M₁ ι₁-hom # (σ # (δ # (H.unit.η _ # α)))                                                              ≡˘⟨ ap (λ e → H.M₁ ι₁-hom # (σ # e)) (H.left-ident #ₚ _) ⟩
        H.M₁ ι₁-hom # (σ # (H.mult.η _ # (H.M₁ (H.unit.η _) # (δ # (H.unit.η _ # α)))))                         ≡⟨ ap (H.M₁ ι₁-hom #_) (σ .commutes #ₚ _) ⟩
        H.M₁ ι₁-hom # (H.mult.η _ # (H.M₁ (σ .morphism) # (H.M₁ (H.unit.η _) # (δ # (H.unit.η _ # α)))))        ≡˘⟨ H.mult.is-natural _ _ ι₁-hom #ₚ _ ⟩
        H.mult.η _ # (H.M₁ (H.M₁ ι₁-hom) # (H.M₁ (σ .morphism) # (H.M₁ (H.unit.η _) # (δ # (H.unit.η _ # α))))) ≡⟨ ap (H.mult.η _ #_) (σ̅-ι σ (δ # (H.unit.η _ # α))) ⟩
        H.mult.η _ # (H.M₁ (σ̅ σ) # (H.M₁ ι₁-hom # (δ # (H.unit.η _ # α))) ) ∎
      (ι₂ α) →
        H.unit.η _ # ι₂ α                               ≡˘⟨ H.right-ident #ₚ _ ⟩
        H.mult.η _ # (H.unit.η _ # (H.unit.η _ # ι₂ α)) ≡⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (σ̅ σ) #ₚ (ι₂ α)) ⟩
        H.mult.η _ # (H.M₁ (σ̅ σ) # (H.unit.η _ # ι₂ α)) ∎

  T′ : (σ : Algebra-hom _ H Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩) → Algebra-hom _ H Fᴴ⟨ Δ⁺ ⟩ Fᴴ⟨ Δ⁺ ⟩
  T′ σ .morphism = H.mult.η _ ∘ H.M₁ (σ̅ σ)
  T′ σ .commutes = ext λ α →
    H.mult.η _ # (H.M₁ (σ̅ σ) # (H.mult.η _ # α))               ≡˘⟨ ap (H.mult.η _ #_) (H.mult.is-natural _ _ (σ̅ σ) #ₚ α) ⟩
    H.mult.η _ # (H.mult.η _ # (H.M₁ (H.M₁ (σ̅ σ)) # α))        ≡˘⟨ H.mult-assoc #ₚ ((H.M₁ (H.M₁ (σ̅ σ))) # α) ⟩
    H.mult.η _ # (H.M₁ (H.mult.η _) # (H.M₁ (H.M₁ (σ̅ σ)) # α)) ≡˘⟨ ap (H.mult.η _ #_) (H.M-∘ (H.mult.η _) (H.M₁ (σ̅ σ)) #ₚ α) ⟩
    H.mult.η _ # (H.M₁ (H.mult.η _ ∘ H.M₁ (σ̅ σ)) # α)          ∎

  T : Functor (Endos SOrdᴴ Fᴴ⟨ Δ ⟩) (Endos SOrdᴹᴰ Fᴹᴰ⟨ Disc Ψ ⟩)
  T = functor
    where
      functor : Functor (Endos SOrdᴴ Fᴴ⟨ Δ ⟩) (Endos SOrdᴹᴰ Fᴹᴰ⟨ Disc Ψ ⟩)
      functor .Functor.F₀ _ = tt
      functor .Functor.F₁ σ .morphism .hom (α , d) = α , (T′ σ SOrdᴴ.∘ d)
      functor .Functor.F₁ σ .morphism .strict-mono {α , d1} {β , d2} =
        ⋉-elim (λ α≡β d1<d2 → biased α≡β (𝒟.left-invariant d1<d2))
               (λ α<β d1≤id id≤d2 → absurd (Lift.lower α<β))
               (λ _ → Fᴹᴰ⟨Ψ⟩.<-thin)
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
  Uᴴ {X} .Functor.F₀ _ = Lift< _ _ (fst X)
  Uᴴ .Functor.F₁ σ .hom (lift α) = lift (σ # α)
  Uᴴ .Functor.F₁ σ .strict-mono (lift α<β) = lift (σ .morphism .strict-mono α<β)
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
      ℓ̅ ℓ .strict-mono {ι₀ α} {ι₀ β} (lift ff) = absurd ff
      ℓ̅ ℓ .strict-mono {ι₁ α} {ι₁ β} α<β = H.unit.η _ .strict-mono α<β
      ℓ̅ ℓ .strict-mono {ι₂ α} {ι₂ β} α<β = H.unit.η _ .strict-mono α<β

      ℓ̅-mono : ∀ {ℓ ℓ′} → ℓ′ H⟨Δ⟩.< ℓ → ∀ (α :  ⌞ Δ⁺ ⌟) → ℓ̅ ℓ′ # α H⟨Δ⁺⟩.≤ ℓ̅ ℓ # α
      ℓ̅-mono ℓ′<ℓ (ι₀ _) = inr (H.M₁ ι₁-hom .strict-mono ℓ′<ℓ)
      ℓ̅-mono ℓ′<ℓ (ι₁ _) = inl refl
      ℓ̅-mono ℓ′<ℓ (ι₂ _) = inl refl

      ν′ : ⌞ H.M₀ Δ ⌟ → Algebra-hom _ H Fᴴ⟨ Δ⁺ ⟩ Fᴴ⟨ Δ⁺ ⟩
      ν′ ℓ .morphism = H.mult.η _ ∘ H.M₁ (ℓ̅ ℓ)
      ν′ ℓ .commutes = ext λ α →
        H.mult.η _ # (H.M₁ (ℓ̅ ℓ) # (H.mult.η _ # α))               ≡˘⟨ ap (H.mult.η _ #_) (H.mult.is-natural _ _ (ℓ̅ ℓ) #ₚ α) ⟩
        H.mult.η _ # (H.mult.η _ # (H.M₁ (H.M₁ (ℓ̅ ℓ)) # α))        ≡˘⟨ H.mult-assoc #ₚ _ ⟩
        H.mult.η _ # (H.M₁ (H.mult.η _) # (H.M₁ (H.M₁ (ℓ̅ ℓ)) # α)) ≡˘⟨ ap (H.mult.η _ #_) (H.M-∘ _ _ #ₚ α) ⟩
        H.mult.η _ # (H.M₁ (H.mult.η _ ∘ H.M₁ (ℓ̅ ℓ)) # α)          ∎

      ν′-strictly-mono : ∀ {ℓ′ ℓ : ⌞ H.M₀ Δ ⌟} → ℓ′ H⟨Δ⟩.< ℓ → ν′ ℓ′ H⟨Δ⁺⟩→.< ν′ ℓ
      ν′-strictly-mono {ℓ′} {ℓ} ℓ′<ℓ .endo[_<_].endo-≤ α = begin-≤
        H.mult.η _ # (H.M₁ (ℓ̅ ℓ′) # (H.unit.η _ # α)) ≡̇⟨ ap (H.mult.η _ #_) (sym $ H.unit.is-natural _ _ (ℓ̅ ℓ′) #ₚ α) ⟩
        H.mult.η _ # (H.unit.η _ # (ℓ̅ ℓ′ # α))        ≤⟨ mono (H.mult.η _ ∘ H.unit.η _) (ℓ̅-mono ℓ′<ℓ α) ⟩
        H.mult.η _ # (H.unit.η _ # (ℓ̅ ℓ # α))         ≡̇⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (ℓ̅ ℓ) #ₚ α) ⟩
        H.mult.η _ # (H.M₁ (ℓ̅ ℓ) # (H.unit.η _ # α))  <∎
        where
          open Mugen.Order.StrictOrder.Reasoning (H.M₀ Δ⁺)
      ν′-strictly-mono {ℓ′} {ℓ} ℓ′<ℓ .endo[_<_].endo-< =
        inc (ι₀ ⋆ , ν′⟨ℓ′⟩⟨⋆⟩<ν′⟨ℓ⟩⟨⋆⟩)
        where
          open Mugen.Order.StrictOrder.Reasoning (H.M₀ Δ⁺)

          ν′⟨ℓ′⟩⟨⋆⟩<ν′⟨ℓ⟩⟨⋆⟩ : H.mult.η _ # (H.M₁ (ℓ̅ ℓ′) # (H.unit.η _ # (ι₀ ⋆))) H⟨Δ⁺⟩.< H.mult.η _ # (H.M₁ (ℓ̅ ℓ) # (H.unit.η _ # (ι₀ ⋆)))
          ν′⟨ℓ′⟩⟨⋆⟩<ν′⟨ℓ⟩⟨⋆⟩ = begin-<
            H.mult.η _ # (H.M₁ (ℓ̅ ℓ′) # (H.unit.η _ # ι₀ ⋆)) ≡̇⟨ ap (H.mult.η _ #_) (sym $ H.unit.is-natural _ _ (ℓ̅ ℓ′) #ₚ _) ⟩
            H.mult.η _ # (H.unit.η _ # (H.M₁ ι₁-hom # ℓ′))   <⟨  (H.mult.η _ ∘ H.unit.η _ ∘ H.M₁ ι₁-hom) .strict-mono ℓ′<ℓ ⟩
            H.mult.η _ # (H.unit.η _ # (H.M₁ ι₁-hom # ℓ))    ≡̇⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (ℓ̅ ℓ) #ₚ _) ⟩
            H.mult.η _ # (H.M₁ (ℓ̅ ℓ) # (H.unit.η _ # ι₀ ⋆))  <∎

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
      nt ._=>_.η _ .strict-mono (lift ℓ<ℓ′) = biased refl (ν′-strictly-mono ℓ<ℓ′)
      nt ._=>_.is-natural _ _ σ =  ext λ ℓ →
        refl , λ α →
          H.mult.η _ # (H.M₁ (ℓ̅ (σ # ℓ .Lift.lower)) # α)                                         ≡⟨ ap (λ e → (H.mult.η _ ∘ H.M₁ e) # α) (ℓ̅-σ̅ σ) ⟩
          H.mult.η _ # (H.M₁ (H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ ℓ̅ (ℓ .Lift.lower)) # α)                   ≡⟨ ap (H.mult.η _ #_) ((H.M-∘ _ _  ∙ ((refl⟩∘⟨ H.M-∘ _ _))) #ₚ α) ⟩
          H.mult.η _ # (H.M₁ (H.mult.η _) # (H.M₁ (H.M₁ (σ̅ σ)) # (H.M₁ (ℓ̅ (ℓ .Lift.lower)) # α))) ≡⟨ H.mult-assoc #ₚ _ ⟩
          H.mult.η _ # (H.mult.η _ # (H.M₁ (H.M₁ (σ̅ σ)) # (H.M₁ (ℓ̅ (ℓ .Lift.lower)) # α)))        ≡⟨ ap (H.mult.η _ #_) (H.mult.is-natural _ _ (σ̅ σ) #ₚ _) ⟩
          H.mult.η _ # (H.M₁ (σ̅ σ) # (H.mult.η _ # (H.M₁ (ℓ̅ (ℓ .Lift.lower)) # α))) ∎

  --------------------------------------------------------------------------------
  -- Faithfulness of T
  -- Section 3.4, Lemma 3.8

  T-faithful : ∣ Ψ ∣ → preserves-monos H → is-faithful T
  T-faithful pt H-preserves-monos {x} {y} {σ} {δ} p =
    free-algebra-path $ H-preserves-monos ι₁-hom ι₁-monic _ _ $
    ext λ α →
    σ̅ σ # (ι₁ α)                                    ≡˘⟨ H.right-ident #ₚ _ ⟩
    H.mult.η _ # (H.unit.η _ # (σ̅ σ #  (ι₁ α)))     ≡⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (σ̅ σ) #ₚ _) ⟩
    H.mult.η _ # (H.M₁ (σ̅ σ) # (H.unit.η _ # ι₁ α)) ≡⟨ (ap snd (p #ₚ (pt , SOrdᴴ.id)) #ₚ _) ⟩
    H.mult.η _ # (H.M₁ (σ̅ δ) # (H.unit.η _ # ι₁ α)) ≡˘⟨ ap (H.mult.η _ #_) (H.unit.is-natural _ _ (σ̅ δ) #ₚ _) ⟩
    H.mult.η _ # (H.unit.η _ # (σ̅ δ #  (ι₁ α)))     ≡⟨ H.right-ident #ₚ _ ⟩
    σ̅ δ # (ι₁ α)                                    ∎
