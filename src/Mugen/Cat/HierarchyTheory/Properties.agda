{-# OPTIONS --experimental-lossy-unification #-}
module Mugen.Cat.HierarchyTheory.Properties where

open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Diagram.Monad

import Cat.Reasoning as Cat
import Cat.Functor.Reasoning as FR

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Endo

open import Mugen.Cat.Endomorphisms
open import Mugen.Cat.HierarchyTheory
open import Mugen.Cat.StrictOrders

open import Mugen.Order.Coproduct
open import Mugen.Order.LeftInvariantRightCentered
open import Mugen.Order.StrictOrder
open import Mugen.Order.Singleton
open import Mugen.Order.Discrete


module _ {o r} (H : HierarchyTheory o r) (Δ : StrictOrder o r) (Ψ : Set (lsuc o ⊔ lsuc r)) where
  open Algebra-hom

  private

    Δ⁺ : StrictOrder o r
    Δ⁺ = ◆ ⊕ (Δ ⊕ Δ)

    𝒟 : DisplacementAlgebra (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)
    𝒟 = Endo H Δ⁺

    SOrdᴴ : Precategory (o ⊔ r ⊔ (lsuc o ⊔ lsuc r)) (o ⊔ r ⊔ (lsuc o ⊔ lsuc r))
    SOrdᴴ = Eilenberg-Moore _ H

    SOrdᴹᴰ : Precategory _ _
    SOrdᴹᴰ = Eilenberg-Moore _ (ℳ 𝒟)

    Fᴴ⟨_⟩ : StrictOrder o r → Algebra (StrictOrders o r) H
    Fᴴ⟨_⟩ = Functor.F₀ (Free (StrictOrders o r) H)

    Fᴹᴰ⟨_⟩ : StrictOrder (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r) → Algebra (StrictOrders (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)) (ℳ 𝒟)
    Fᴹᴰ⟨_⟩ = Functor.F₀ (Free (StrictOrders (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r)) (ℳ 𝒟))

    module Δ = StrictOrder Δ

    module 𝒟 = DisplacementAlgebra 𝒟
    module H = Monad H
    module HR = FR H.M
    module ℳᴰ = Monad (ℳ 𝒟)
    module H⟨Δ⁺⟩ = StrictOrder (H.M₀ Δ⁺)
    module Fᴹᴰ⟨Δ⁺⟩ = StrictOrder (fst (Fᴹᴰ⟨ Lift< (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r) Δ⁺ ⟩))
    module Fᴹᴰ⟨Ψ⟩ = StrictOrder (fst (Fᴹᴰ⟨ Disc Ψ ⟩))
    module SOrd {o} {r} = Cat (StrictOrders o r)
    module SOrdᴴ = Cat (SOrdᴴ)
    module SOrdᴹᴰ = Cat (SOrdᴹᴰ)

    pattern ⋆  = lift tt
    pattern ι₀ α = inl α
    pattern ι₁ α = inr (inl α)
    pattern ι₂ α = inr (inr α)

    ι₁-hom : Precategory.Hom (StrictOrders o r) Δ Δ⁺
    ι₁-hom ._⟨$⟩_ = ι₁
    ι₁-hom .homo α<β = α<β

    ι₁-monic : SOrd.is-monic ι₁-hom
    ι₁-monic g h p = strict-order-path λ α →
      inl-inj (inr-inj (strict-order-happly p α ))


  module _ (σ : Algebra-hom _ H Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩) where
    open Cat (StrictOrders o r)

    σ̅ : Hom Δ⁺ (H.M₀ Δ⁺)
    σ̅ ⟨$⟩ ι₀ α = H.unit.η _ ⟨$⟩ ι₀ α
    σ̅ ⟨$⟩ ι₁ α = H.M₁ ι₁-hom ⟨$⟩ σ .morphism ⟨$⟩ H.unit.η _ ⟨$⟩ α
    σ̅ ⟨$⟩ ι₂ α = H.unit.η _ ⟨$⟩ ι₂ α
    σ̅ .homo {ι₀ ⋆} {ι₀ ⋆} (lift ff) = absurd ff
    σ̅ .homo {ι₁ α} {ι₁ β} α<β =  (H.M₁ ι₁-hom SOrd.∘ σ .morphism SOrd.∘ H.unit.η Δ) .homo α<β
    σ̅ .homo {ι₂ α} {ι₂ β} α<β = H.unit.η Δ⁺ .homo α<β

    T′ : Algebra-hom _ H Fᴴ⟨ Δ⁺ ⟩ Fᴴ⟨ Δ⁺ ⟩
    T′ .morphism = H.mult.η _ ∘ H.M₁ σ̅
    T′ .commutes = strict-order-path λ α →
      H.mult.η _ ⟨$⟩ H.M₁ σ̅ ⟨$⟩ H.mult.η _ ⟨$⟩ α               ≡˘⟨ ap (H.mult.η _ ⟨$⟩_) (strict-order-happly (H.mult.is-natural _ _ σ̅) α) ⟩
      H.mult.η _ ⟨$⟩ H.mult.η _ ⟨$⟩ H.M₁ (H.M₁ σ̅) ⟨$⟩ α        ≡˘⟨ strict-order-happly H.mult-assoc (H.M₁ (H.M₁ σ̅) ⟨$⟩ α) ⟩
      H.mult.η _ ⟨$⟩ H.M₁ (H.mult.η _) ⟨$⟩ H.M₁ (H.M₁ σ̅) ⟨$⟩ α ≡˘⟨ ap (H.mult.η _ ⟨$⟩_) (strict-order-happly (H.M-∘ (H.mult.η _) (H.M₁ σ̅)) α) ⟩
      H.mult.η _ ⟨$⟩ H.M₁ (H.mult.η _ ∘ H.M₁ σ̅) ⟨$⟩ α          ∎

  T : Functor (Endos SOrdᴴ Fᴴ⟨ Δ ⟩) (Endos SOrdᴹᴰ Fᴹᴰ⟨ Disc Ψ ⟩)
  T = functor
    where
      open Cat (StrictOrders o r)

      σ̅-id : σ̅ SOrdᴴ.id ≡ H.unit.η _
      σ̅-id = strict-order-path λ where
        (ι₀ α) → refl
        (ι₁ α) → strict-order-happly (sym (H.unit.is-natural _ _ ι₁-hom)) α
        (ι₂ α) → refl

      σ̅-∘ : ∀ (σ δ : Algebra-hom _ H Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩) → σ̅ (σ SOrdᴴ.∘ δ) ≡ H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ σ̅ δ
      σ̅-∘ σ δ = strict-order-path λ where
        (ι₀ α) →
          H.unit.η _ ⟨$⟩ ι₀ α                               ≡˘⟨ strict-order-happly H.right-ident (H.unit.η _ ⟨$⟩ ι₀ α) ⟩
          H.mult.η _ ⟨$⟩ H.unit.η _ ⟨$⟩ H.unit.η _ ⟨$⟩ ι₀ α ≡⟨ ap (H.mult.η _ ⟨$⟩_) (strict-order-happly (H.unit.is-natural _ _ (σ̅ σ)) (ι₀ α)) ⟩
          H.mult.η _ ⟨$⟩ H.M₁ (σ̅ σ) ∘ H.unit.η _ ⟨$⟩ ι₀ α   ∎
        (ι₁ α) →
          H.M₁ ι₁-hom ⟨$⟩ σ .morphism ⟨$⟩ δ .morphism  ⟨$⟩ H.unit.η _ ⟨$⟩ α
            ≡˘⟨ ap (λ ϕ →  H.M₁ ι₁-hom ⟨$⟩ σ .morphism ⟨$⟩ ϕ) (strict-order-happly H.left-ident _) ⟩
          H.M₁ ι₁-hom ⟨$⟩ σ .morphism ⟨$⟩ H.mult.η _ ⟨$⟩ H.M₁ (H.unit.η _) ⟨$⟩ δ .morphism ⟨$⟩ H.unit.η _ ⟨$⟩ α
            ≡⟨ ap ( H.M₁ ι₁-hom ⟨$⟩_) (strict-order-happly (σ .commutes) _) ⟩
          H.M₁ ι₁-hom ⟨$⟩ H.mult.η _ ⟨$⟩ H.M₁ (σ .morphism) ⟨$⟩ H.M₁ (H.unit.η _) ⟨$⟩ δ .morphism ⟨$⟩ H.unit.η _ ⟨$⟩ α
            ≡˘⟨ strict-order-happly (H.mult.is-natural _ _ ι₁-hom) _ ⟩
          H.mult.η _ ⟨$⟩ H.M₁ (H.M₁ ι₁-hom) ⟨$⟩ H.M₁ (σ .morphism) ⟨$⟩ H.M₁ (H.unit.η _) ⟨$⟩ δ .morphism ⟨$⟩ H.unit.η _ ⟨$⟩ α
            ≡˘⟨ ap (λ ϕ → H.mult.η _ ∘ ϕ ∘ δ .morphism ∘ H.unit.η _ ⟨$⟩ α) (H.M-∘ _ _ ∙ ap (H.M₁ (H.M₁ ι₁-hom) ∘_) (H.M-∘ _ _)) ⟩
          H.mult.η _ ⟨$⟩ H.M₁ (H.M₁ ι₁-hom ∘ σ .morphism ∘ H.unit.η _) ⟨$⟩ δ .morphism ⟨$⟩ H.unit.η _ ⟨$⟩ α
            ≡⟨ ap (λ ϕ → H.mult.η _ ⟨$⟩ H.M₁ ϕ ⟨$⟩ δ .morphism ⟨$⟩ H.unit.η _ ⟨$⟩ α) (strict-order-path λ _ → refl) ⟩
          H.mult.η _ ⟨$⟩ H.M₁ (σ̅ σ ∘ ι₁-hom) ⟨$⟩ δ .morphism ⟨$⟩ H.unit.η _ ⟨$⟩ α
            ≡⟨ ap (λ ϕ → H.mult.η _ ⟨$⟩ ϕ ⟨$⟩ δ .morphism ⟨$⟩ H.unit.η _ ⟨$⟩ α) (H.M-∘ _ _) ⟩
          H.mult.η _ ⟨$⟩ H.M₁ (σ̅ σ) ⟨$⟩ H.M₁ ι₁-hom ⟨$⟩ δ .morphism ⟨$⟩ H.unit.η _ ⟨$⟩ α ∎
        (ι₂ α) →
          H.unit.η _ ⟨$⟩ ι₂ α                               ≡˘⟨ strict-order-happly H.right-ident (H.unit.η _ ⟨$⟩ ι₂ α) ⟩
          H.mult.η _ ⟨$⟩ H.unit.η _ ⟨$⟩ H.unit.η _ ⟨$⟩ ι₂ α ≡⟨ ap (H.mult.η _ ⟨$⟩_) (strict-order-happly (H.unit.is-natural _ _ (σ̅ σ)) (ι₂ α)) ⟩
          H.mult.η _ ⟨$⟩ H.M₁ (σ̅ σ) ∘ H.unit.η _ ⟨$⟩ ι₂ α   ∎

      functor : Functor (Endos SOrdᴴ Fᴴ⟨ Δ ⟩) (Endos SOrdᴹᴰ Fᴹᴰ⟨ Disc Ψ ⟩)
      functor .Functor.F₀ _ = tt
      functor .Functor.F₁ σ .morphism ⟨$⟩ (α , d) = α , (T′ σ SOrdᴴ.∘ d)
      functor .Functor.F₁ σ .morphism .homo {α , d1} {β , d2} =
        ⋉-elim (λ α≡β d1<d2 → biased α≡β (𝒟.left-invariant d1<d2))
               (λ α<β d1≤id id≤d2 → absurd (Lift.lower α<β))
               (λ _ → Fᴹᴰ⟨Ψ⟩.has-prop)
      functor .Functor.F₁ σ .commutes = strict-order-path λ where
        ((α , d₁) , d₂) → Σ-pathp refl (SOrdᴴ.assoc (T′ σ) d₁ d₂)
      functor .Functor.F-id = hierarchy-algebra-path λ where
        (α , d) → Σ-pathp refl $ Algebra-hom-path _ $
          H.mult.η _ ∘ H.M₁ (σ̅ SOrdᴴ.id) ∘ d .morphism ≡⟨ ap (λ ϕ → H.mult.η _ ∘ H.M₁ ϕ ∘ d .morphism) σ̅-id ⟩
          H.mult.η _ ∘ H.M₁ (H.unit.η _) ∘ d .morphism ≡⟨ cancell H.left-ident ⟩
          d .morphism ∎
      functor .Functor.F-∘ σ δ = hierarchy-algebra-path λ where
        (α , d) → Σ-pathp refl $ Algebra-hom-path _ $
          H.mult.η _ ∘ H.M₁ (σ̅ (σ SOrdᴴ.∘ δ)) ∘ d .morphism                             ≡⟨ ap (λ ϕ → H.mult.η _ ∘ (H.M₁ ϕ ∘ d .morphism)) (σ̅-∘ σ δ) ⟩
          H.mult.η _ ∘ H.M₁ (H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ σ̅ δ) ∘ d .morphism               ≡⟨ ap (λ ϕ → H.mult.η _ ∘ ϕ ∘ d .morphism) (H.M-∘ _ _ ∙ ap (H.M₁ (H.mult.η _) ∘_) (H.M-∘ _ _)) ⟩
          H.mult.η _ ∘ H.M₁ (H.mult.η _) ∘ H.M₁ (H.M₁ (σ̅ σ)) ∘ H.M₁ (σ̅ δ) ∘ d .morphism ≡⟨ extendl H.mult-assoc ⟩
          H.mult.η _ ∘ H.mult.η _ ∘ H.M₁ (H.M₁ (σ̅ σ)) ∘ H.M₁ (σ̅ δ) ∘ d .morphism        ≡⟨ ap (H.mult.η _ ∘_) (extendl (H.mult.is-natural _ _ (σ̅ σ))) ⟩
          H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ H.mult.η _ ∘ H.M₁ (σ̅ δ) ∘ d .morphism ∎

  --------------------------------------------------------------------------------
  -- NOTE: Forgetful Functors + Levels
  --
  -- To avoid dealing with an annoying level shifting functor, we bake in the
  -- required lifts into Uᴴ instead.

  Uᴴ : ∀ {X} → Functor (Endos SOrdᴴ X) (StrictOrders (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r))
  Uᴴ {X} .Functor.F₀ _ = Lift< _ _ (fst X)
  Uᴴ .Functor.F₁ σ ⟨$⟩ lift α = lift (σ .morphism ⟨$⟩ α)
  Uᴴ .Functor.F₁ σ .homo (lift α<β) = lift (σ .morphism .homo α<β)
  Uᴴ .Functor.F-id = strict-order-path λ where
    (lift x) → refl
  Uᴴ .Functor.F-∘ _ _ = strict-order-path λ where
    (lift x) → refl

  Uᴹᴰ : ∀ {X} → Functor (Endos SOrdᴹᴰ X) (StrictOrders (lsuc o ⊔ lsuc r) (lsuc o ⊔ lsuc r))
  Uᴹᴰ {X} .Functor.F₀ _ = fst X
  Uᴹᴰ .Functor.F₁ σ = σ .morphism
  Uᴹᴰ .Functor.F-id = refl
  Uᴹᴰ .Functor.F-∘ _ _ = refl

  ν : (pt : ∣ Ψ ∣) → Uᴴ => Uᴹᴰ F∘ T
  ν pt = nt
    where
      open Cat (StrictOrders o r)

      ℓ̅ : ⌞ H.M₀ Δ ⌟ → Hom Δ⁺ (H.M₀ Δ⁺)
      ℓ̅ ℓ ⟨$⟩ ι₀ _ = H.M₁ ι₁-hom ⟨$⟩ ℓ
      ℓ̅ ℓ ⟨$⟩ ι₁ α = H.unit.η _ ⟨$⟩ ι₂ α
      ℓ̅ ℓ ⟨$⟩ ι₂ α = H.unit.η _ ⟨$⟩ ι₂ α
      ℓ̅ ℓ .homo {ι₀ α} {ι₀ β} (lift ff) = absurd ff
      ℓ̅ ℓ .homo {ι₁ α} {ι₁ β} α<β = H.unit.η _ .homo α<β
      ℓ̅ ℓ .homo {ι₂ α} {ι₂ β} α<β = H.unit.η _ .homo α<β

      ℓ̅-mono : ∀ {ℓ ℓ′} → H.M₀ Δ [ ℓ′ < ℓ ] → ∀ α → H.M₀ Δ⁺ [ ℓ̅ ℓ′ ⟨$⟩ α ≤ ℓ̅ ℓ ⟨$⟩ α ]
      ℓ̅-mono ℓ′<ℓ (ι₀ _) = inr (H.M₁ ι₁-hom .homo ℓ′<ℓ)
      ℓ̅-mono ℓ′<ℓ (ι₁ _) = inl refl
      ℓ̅-mono ℓ′<ℓ (ι₂ _) = inl refl

      ν′ : ⌞ H.M₀ Δ ⌟ → Algebra-hom _ H Fᴴ⟨ Δ⁺ ⟩ Fᴴ⟨ Δ⁺ ⟩
      ν′ ℓ .morphism = H.mult.η _ ∘ H.M₁ (ℓ̅ ℓ)
      ν′ ℓ .commutes = strict-order-path λ α →
        H.mult.η _ ∘ HR.F₁ (ℓ̅ ℓ) ∘ H.mult.η _ ⟨$⟩ α               ≡˘⟨ strict-order-happly (refl⟩∘⟨ (H.mult.is-natural _ _ (ℓ̅ ℓ))) α  ⟩
        H.mult.η _ ∘ H.mult.η _ ∘ H.M₁ (H.M₁ (ℓ̅ ℓ)) ⟨$⟩ α         ≡⟨ strict-order-happly (extendl (sym H.mult-assoc)) α ⟩
        H.mult.η _ ∘ HR.F₁ (H.mult.η _) ∘ H.M₁ (H.M₁ (ℓ̅ ℓ)) ⟨$⟩ α ≡˘⟨ strict-order-happly (refl⟩∘⟨ H.M-∘ _ _) α ⟩
        H.mult.η _ ∘ HR.F₁ (H.mult.η _ ∘ H.M₁ (ℓ̅ ℓ)) ⟨$⟩ α        ∎

      ν′-strictly-mono : ∀ {ℓ′ ℓ : ⌞ H.M₀ Δ ⌟} → H.M₀ Δ [ ℓ′ < ℓ ] → Endo H Δ⁺ [ ν′ ℓ′ < ν′ ℓ ]ᵈ
      ν′-strictly-mono {ℓ′} {ℓ} ℓ′<ℓ .endo[_<_].endo-≤ α = begin-≤
          H.mult.η _ ∘ HR.F₁ (ℓ̅ ℓ′) ∘ H.unit.η _ ⟨$⟩ α ≡̇⟨ strict-order-happly (refl⟩∘⟨ (sym $ H.unit.is-natural _ _ (ℓ̅ ℓ′))) α ⟩
          H.mult.η _ ∘ H.unit.η _ ∘ ℓ̅ ℓ′ ⟨$⟩ α         ≤⟨ strictly-mono→mono (H.mult.η _ ∘ H.unit.η _) (ℓ̅-mono ℓ′<ℓ α) ⟩
          H.mult.η _ ∘ H.unit.η _ ∘ ℓ̅ ℓ ⟨$⟩ α          ≡̇⟨ strict-order-happly (refl⟩∘⟨ H.unit.is-natural _ _ (ℓ̅ ℓ)) α ⟩
          H.mult.η _ ∘ HR.F₁ (ℓ̅ ℓ) ∘ H.unit.η _ ⟨$⟩ α  <∎
        where
          open StrictOrder-Reasoning (H.M₀ Δ⁺)
      ν′-strictly-mono {ℓ′} {ℓ} ℓ′<ℓ .endo[_<_].endo-< =
        inc (ι₀ ⋆ , ν′⟨ℓ′⟩⟨⋆⟩<ν′⟨ℓ⟩⟨⋆⟩)
        where
          open StrictOrder-Reasoning (H.M₀ Δ⁺)

          ν′⟨ℓ′⟩⟨⋆⟩<ν′⟨ℓ⟩⟨⋆⟩ : H.M₀ Δ⁺ [ H.mult.η _ ∘ H.M₁ (ℓ̅ ℓ′) ∘ H.unit.η _ ⟨$⟩ ι₀ ⋆ < H.mult.η _ ∘ H.M₁ (ℓ̅ ℓ) ∘ H.unit.η _ ⟨$⟩ ι₀ ⋆ ]
          ν′⟨ℓ′⟩⟨⋆⟩<ν′⟨ℓ⟩⟨⋆⟩ = begin-<
            H.mult.η _ ∘ HR.F₁ (ℓ̅ ℓ′) ∘ H.unit.η _ ⟨$⟩ ι₀ ⋆ ≡̇⟨ strict-order-happly (refl⟩∘⟨ (sym $ H.unit.is-natural _ _ (ℓ̅ ℓ′))) (ι₀ ⋆) ⟩
            H.mult.η _ ∘ H.unit.η _ ∘ H.M₁ ι₁-hom ⟨$⟩ ℓ′   <⟨ (H.mult.η _ ∘ (H.unit.η _ ∘ H.M₁ ι₁-hom)) .homo ℓ′<ℓ ⟩
            H.mult.η _ ∘ H.unit.η _ ∘ H.M₁ ι₁-hom ⟨$⟩ ℓ    ≡̇⟨ strict-order-happly (refl⟩∘⟨ (H.unit.is-natural _ _ (ℓ̅ ℓ))) (ι₀ ⋆) ⟩
            H.mult.η _ ∘ H.M₁ (ℓ̅ ℓ) ∘ H.unit.η _ ⟨$⟩ ι₀ ⋆  <∎

      ℓ̅-σ̅ : ∀ {ℓ : ⌞ fst Fᴴ⟨ Δ ⟩ ⌟} (σ : Algebra-hom _ _ Fᴴ⟨ Δ ⟩ Fᴴ⟨ Δ ⟩) → ℓ̅ (σ .morphism ⟨$⟩ ℓ) ≡ H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ ℓ̅ ℓ
      ℓ̅-σ̅ {ℓ} σ = strict-order-path λ where
        (ι₀ ⋆) →
          H.M₁ ι₁-hom ∘ σ .morphism ⟨$⟩ ℓ                                                ≡⟨ strict-order-happly (refl⟩∘⟨ (intror H.left-ident)) ℓ ⟩
          H.M₁ ι₁-hom ∘ σ .morphism ∘ H.mult.η _ ∘ H.M₁ (H.unit.η _) ⟨$⟩ ℓ               ≡⟨ strict-order-happly (refl⟩∘⟨ pulll (σ .commutes)) ℓ ⟩
          H.M₁ ι₁-hom ∘ H.mult.η _ ∘ H.M₁ (σ .morphism) ∘ H.M₁ (H.unit.η _) ⟨$⟩ ℓ        ≡⟨ strict-order-happly (pulll (sym $ H.mult.is-natural _ _ ι₁-hom)) ℓ ⟩
          H.mult.η _ ∘ H.M₁ (H.M₁ ι₁-hom) ∘ H.M₁ (σ .morphism) ∘ H.M₁ (H.unit.η _) ⟨$⟩ ℓ ≡⟨ strict-order-happly (refl⟩∘⟨ refl⟩∘⟨ (sym $ H.M-∘ _ _)) ℓ ⟩
          H.mult.η _ ∘ H.M₁ (H.M₁ ι₁-hom) ∘ H.M₁ (σ .morphism ∘ H.unit.η _) ⟨$⟩ ℓ        ≡⟨ strict-order-happly (refl⟩∘⟨ (sym $ H.M-∘ _ _)) ℓ ⟩
          H.mult.η _ ∘ H.M₁ (H.M₁ ι₁-hom ∘ σ .morphism ∘ H.unit.η _) ⟨$⟩ ℓ               ≡⟨ strict-order-happly (refl⟩∘⟨ (H.M-∘ (σ̅ σ) ι₁-hom)) ℓ ⟩
          H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ H.M₁ ι₁-hom ⟨$⟩ ℓ                                    ∎
        (ι₁ α) →
          H.unit.η _ ⟨$⟩ ι₂ α                             ≡⟨ strict-order-happly {f = H.unit.η _} (introl H.right-ident) (ι₂ α) ⟩
          H.mult.η _ ∘ H.unit.η _ ∘ H.unit.η _ ⟨$⟩ ι₂ α   ≡⟨ strict-order-happly (refl⟩∘⟨ H.unit.is-natural _ _ (σ̅ σ)) (ι₂ α) ⟩
          H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ H.unit.η _ ⟨$⟩ ι₂ α   ∎
        (ι₂ α) →
          H.unit.η _ ⟨$⟩ ι₂ α                             ≡⟨ strict-order-happly {f = H.unit.η _} (introl H.right-ident) (ι₂ α) ⟩
          H.mult.η _ ∘ H.unit.η _ ∘ H.unit.η _ ⟨$⟩ ι₂ α   ≡⟨ strict-order-happly (refl⟩∘⟨ H.unit.is-natural _ _ (σ̅ σ)) (ι₂ α) ⟩
          H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ H.unit.η _ ⟨$⟩ ι₂ α   ∎

      nt : Uᴴ => Uᴹᴰ F∘ T
      nt ._=>_.η _ ⟨$⟩ (lift ℓ) = pt , ν′ ℓ
      nt ._=>_.η _ .homo (lift ℓ<ℓ′) = biased refl (ν′-strictly-mono ℓ<ℓ′)
      nt ._=>_.is-natural _ _ σ = strict-order-path λ ℓ →
        Σ-pathp refl $ Algebra-hom-path _ $ strict-order-path λ α →
          H.mult.η _ ∘ H.M₁ (ℓ̅ (σ .morphism ⟨$⟩ ℓ .Lift.lower)) ⟨$⟩ α                         ≡⟨ ap (λ ϕ → (H.mult.η _ ∘ H.M₁ ϕ) ⟨$⟩ α) (ℓ̅-σ̅ σ) ⟩
          H.mult.η _ ∘ H.M₁ (H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ ℓ̅ (ℓ .Lift.lower)) ⟨$⟩ α               ≡⟨ strict-order-happly (refl⟩∘⟨ H.M-∘ _ _) α ⟩
          H.mult.η _ ∘ H.M₁ (H.mult.η _) ∘ H.M₁ (H.M₁ (σ̅ σ) ∘ ℓ̅ (ℓ .Lift.lower)) ⟨$⟩ α        ≡⟨ strict-order-happly (refl⟩∘⟨ refl⟩∘⟨ H.M-∘ _ _) α ⟩
          H.mult.η _ ∘ H.M₁ (H.mult.η _) ∘ H.M₁ (H.M₁ (σ̅ σ)) ∘ H.M₁ (ℓ̅ (ℓ .Lift.lower)) ⟨$⟩ α ≡⟨ strict-order-happly (pulll H.mult-assoc) α ⟩
          H.mult.η _ ∘ H.mult.η _ ∘ H.M₁ (H.M₁ (σ̅ σ)) ∘ H.M₁ (ℓ̅ (ℓ .Lift.lower)) ⟨$⟩ α        ≡⟨ strict-order-happly (refl⟩∘⟨ pulll (H.mult.is-natural _ _ (σ̅ σ))) α ⟩
          H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ H.mult.η _ ∘ H.M₁ (ℓ̅ (ℓ .Lift.lower)) ⟨$⟩ α ∎


  T-faithful : ∣ Ψ ∣ → preserves-monos H → is-faithful T
  T-faithful pt H-preserves-monos {x} {y} {σ} {δ} p =
    free-algebra-path $ H-preserves-monos ι₁-hom ι₁-monic _ _ $
    strict-order-path λ α →
      -- NOTE: More pointless reasoning steps because of unifier failures!!
      H.M₁ ι₁-hom ∘ σ .morphism ∘ H.unit.η _ ⟨$⟩ α ≡⟨⟩
      σ̅ σ ⟨$⟩ (ι₁ α)                                    ≡⟨ strict-order-happly (introl H.right-ident {f = σ̅ σ}) (ι₁ α) ⟩
      H.mult.η _ ∘ H.unit.η _ ∘ σ̅ σ ⟨$⟩ (ι₁ α)          ≡⟨ strict-order-happly (assoc (H.mult.η _) (H.unit.η _) (σ̅ σ)) (ι₁ α) ⟩
      H.mult.η _ ∘ (H.unit.η _ ∘ σ̅ σ) ⟨$⟩ (ι₁ α)        ≡⟨ ap (λ ϕ →  H.mult.η _ ∘ ϕ ⟨$⟩ (ι₁ α)) (H.unit.is-natural _ _ (σ̅ σ)) ⟩
      H.mult.η _ ∘ (H.M₁ (σ̅ σ) ∘ H.unit.η _) ⟨$⟩ (ι₁ α) ≡˘⟨ strict-order-happly (assoc (H.mult.η _) (H.M₁ (σ̅ σ)) (H.unit.η _)) (ι₁ α) ⟩
      H.mult.η _ ∘ H.M₁ (σ̅ σ) ∘ H.unit.η _ ⟨$⟩ (ι₁ α)   ≡⟨ hierarchy-algebra-happly (ap snd $ hierarchy-algebra-happly p (pt , SOrdᴴ.id)) (H.unit.η _ ⟨$⟩ ι₁ α) ⟩
      H.mult.η _ ∘ H.M₁ (σ̅ δ) ∘ H.unit.η _ ⟨$⟩ (ι₁ α)   ≡˘⟨ strict-order-happly (assoc (H.mult.η _) (H.M₁ (σ̅ δ)) (H.unit.η _)) (ι₁ α) ⟩
      H.mult.η _ ∘ (H.M₁ (σ̅ δ) ∘ H.unit.η _) ⟨$⟩ (ι₁ α) ≡˘⟨ ap (λ ϕ →  H.mult.η _ ∘ ϕ ⟨$⟩ (ι₁ α)) (H.unit.is-natural _ _ (σ̅ δ)) ⟩
      H.mult.η _ ∘ (H.unit.η _ ∘ σ̅ δ) ⟨$⟩ (ι₁ α)        ≡˘⟨ strict-order-happly (assoc (H.mult.η _) (H.unit.η _) (σ̅ δ)) (ι₁ α) ⟩
      H.mult.η _ ∘ H.unit.η _ ∘ σ̅ δ ⟨$⟩ (ι₁ α)          ≡⟨  strict-order-happly (eliml H.right-ident {f = σ̅ δ}) (ι₁ α) ⟩
      σ̅ δ ⟨$⟩ (ι₁ α)                                    ≡⟨⟩
      H.M₁ ι₁-hom ∘ δ .morphism ∘ H.unit.η _ ⟨$⟩ α      ∎
      where
        open Cat (StrictOrders o r)
