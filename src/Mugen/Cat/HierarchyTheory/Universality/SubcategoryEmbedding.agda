-- vim: nowrap
open import Data.Nat

open import Order.Instances.Discrete
open import Order.Instances.Disjoint
open import Order.Base

open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Morphism
open import Cat.Functor.Properties
open import Cat.Diagram.Monad
open import Cat.Displayed.Total

import Cat.Reasoning as Cat

open import Mugen.Prelude

open import Mugen.Cat.Instances.Endomorphisms
open import Mugen.Cat.Instances.Indexed
open import Mugen.Cat.Instances.StrictOrders
open import Mugen.Cat.Monad
open import Mugen.Cat.HierarchyTheory

open import Mugen.Order.StrictOrder
open import Mugen.Order.Instances.Copower

import Mugen.Order.Reasoning as Reasoning

--------------------------------------------------------------------------------
-- The Universal Embedding Theorem
-- Section 3.4, Lemma 3.9

module Mugen.Cat.HierarchyTheory.Universality.SubcategoryEmbedding {o o' r}
  {F : Functor (Strict-orders (o ⊔ o') (r ⊔ o')) (Strict-orders (o ⊔ o') (r ⊔ o'))}
  (H : Hierarchy-theory-on F) {I : Type o'} ⦃ Discrete-I : Discrete I ⦄
  (Δ₋ : ⌞ I ⌟ → Poset (o ⊔ o') (r ⊔ o')) where

  --------------------------------------------------------------------------------
  -- Notation
  --
  -- We begin by defining some useful notation.

  private
    open Strictly-monotone
    open ∫Hom
    open Cat (Strict-orders (o ⊔ o') (r ⊔ o'))
    module Δ₋ i = Poset (Δ₋ i)
    module H = Monad-on H

    ⌞Δ₋⌟ : I → Type (o ⊔ o')
    ⌞Δ₋⌟ i = ⌞ Δ₋ i ⌟

    I-is-set : is-set I
    I-is-set = Discrete→is-set Discrete-I

  -- Δ is made public for proving the main theorem
  Δ : Poset (o ⊔ o') (r ⊔ o')
  Δ = Copower (el! Nat) (Disjoint (el I I-is-set) Δ₋)
  module Δ = Poset Δ

  private
    H⟨Δ⟩ : Poset (o ⊔ o') (r ⊔ o')
    H⟨Δ⟩ = H.M₀ Δ
    module H⟨Δ⟩ = Reasoning H⟨Δ⟩

    SOrd : Precategory (lsuc (o ⊔ r ⊔ o')) (o ⊔ r ⊔ o')
    SOrd = Strict-orders (o ⊔ o') (r ⊔ o')
    module SOrd = Cat SOrd

    SOrdᴴ : Precategory (lsuc (o ⊔ r ⊔ o')) (o ⊔ r ⊔ o')
    SOrdᴴ = Eilenberg-Moore {C = SOrd} H
    module SOrdᴴ = Cat SOrdᴴ

    Fᴴ₀ : Poset (o ⊔ o') (r ⊔ o') → Algebra H
    Fᴴ₀ = Free-EM .Functor.F₀

    FᴴΔ₋ : I → Algebra H
    FᴴΔ₋ i =  Fᴴ₀ (Δ₋ i)

  pattern ι n i α = (n , i , α)

  ι-inj : ∀ {n : Nat} {i : I} {x y : ⌞ Δ₋ i ⌟} → _≡_ {A = ⌞ Δ ⌟} (ι n i x) (ι n i y) → x ≡ y
  ι-inj p = is-set→cast-pathp ⌞Δ₋⌟ I-is-set λ j → p j .snd .snd

  ι-hom : ∀ (n : Nat) (i : I) → Hom (Δ₋ i) Δ
  ι-hom n i .hom = ι n i
  ι-hom n i .pres-≤[]-equal α≤β = (reflᵢ , injᵖ {I = el I I-is-set} {F = Δ₋} i .Monotone.pres-≤ α≤β) , ι-inj

  ι-monic : ∀ {n : Nat} {i : I} → SOrd.is-monic (ι-hom n i)
  ι-monic g h eq = ext λ α → ι-inj (eq ·ₚ α)

  --------------------------------------------------------------------------------
  -- Construction of the functor T
  -- Section 3.4, Lemma 3.9

  σ̅ : {i j : I} → SOrdᴴ.Hom (FᴴΔ₋ i) (FᴴΔ₋ j) → Hom Δ H⟨Δ⟩
  σ̅ {i} {j} σ .hom (ι n k α) with k ≡ᵢ? i | n | k ≡ᵢ? j
  ... | yes k=ᵢi | 0     | _     = H.M₁ (ι-hom 0 j) · (σ · (H.η (Δ₋ i) · substᵢ ⌞Δ₋⌟ k=ᵢi α)) -- case k0j
  ... | yes _    | suc n | yes _ = H.η Δ · ι (suc n) k α                                      -- case k1k
  ... | yes _    | suc n | no _  = H.η Δ · ι n k α                                            -- case k1j
  ... | no _     | n     | yes _ = H.η Δ · ι (suc n) k α                                      -- case ik
  ... | no _     | n     | no  _ = H.η Δ · ι n k α                                            -- case ij
  σ̅ {i} {j} σ .pres-≤[]-equal {ι n k α} {ι n k β} (reflᵢ , reflᵢ , α≤β) with k ≡ᵢ? i | n | k ≡ᵢ? j
  ... | yes reflᵢ | 0     | _     = H⟨Δ⟩.≤[]-map (ap (ι 0 i)) $ (H.M₁ (ι-hom 0 j) ∘ σ .fst ∘ H.η (Δ₋ i)) .pres-≤[]-equal (α≤β reflᵢ)
  ... | yes reflᵢ | suc n | yes _ = H.η Δ .pres-≤[]-equal (reflᵢ , reflᵢ , α≤β)
  ... | yes reflᵢ | suc n | no _  = H⟨Δ⟩.≤[]-map (ap (ι (suc n) k)) $ (H.η Δ ∘ ι-hom n k) .pres-≤[]-equal (α≤β reflᵢ)
  ... | no _      | n     | yes _ = H⟨Δ⟩.≤[]-map (ap (ι n k)) $ (H.η Δ ∘ ι-hom (suc n) k) .pres-≤[]-equal (α≤β reflᵢ)
  ... | no _      | n     | no _  = H.η Δ .pres-≤[]-equal (reflᵢ , reflᵢ , α≤β)

  -- Raw β rules of σ̅ σ matching its five cases
  module _ where
    abstract
      σ̅-ι-k0j-ext : ∀ {i j k : I} (σ : SOrdᴴ.Hom (FᴴΔ₋ i) (FᴴΔ₋ j))
        → (p : k ≡ᵢ i)
        → (α : ⌞ Δ₋ k ⌟)
        → σ̅ σ · ι 0 k α ≡ H.M₁ (ι-hom 0 j) · (σ · (H.η (Δ₋ i) · substᵢ ⌞Δ₋⌟ p α))
      σ̅-ι-k0j-ext {i = i} {j} {k} σ p α with k ≡ᵢ? i
      ... | no  k≠ᵢi  = absurd (k≠ᵢi p)
      ... | yes reflᵢ =
        H.M₁ (ι-hom 0 j) · (σ · (H.η (Δ₋ i) · α))
         ≡⟨ ap· (H.M₁ (ι-hom 0 j) ∘ σ .fst ∘ H.η (Δ₋ i)) $ substᵢ-filler-set ⌞Δ₋⌟ I-is-set p α ⟩
        H.M₁ (ι-hom 0 j) · (σ · (H.η (Δ₋ i) · substᵢ ⌞Δ₋⌟ p α))
          ∎

      σ̅-ι-k1k-ext : ∀ (n : Nat) {i j k : I} (σ : SOrdᴴ.Hom (Fᴴ₀ (Δ₋ i)) (Fᴴ₀ (Δ₋ j)))
        → k ≡ᵢ i
        → k ≡ᵢ j
        → (α : ⌞ Δ₋ k ⌟)
        → σ̅ σ · ι (suc n) k α ≡ H.η Δ · ι (suc n) k α
      σ̅-ι-k1k-ext n {i = i} {j} {k} σ k=ᵢi k=ᵢj α with k ≡ᵢ? i | k ≡ᵢ? j
      ... | no  k≠ᵢi | _        = absurd (k≠ᵢi k=ᵢi)
      ... | yes _    | no  k≠ᵢj = absurd (k≠ᵢj k=ᵢj)
      ... | yes _    | yes _    = refl

      σ̅-ι-k1j-ext : ∀ (n : Nat) {i j k : I} (σ : SOrdᴴ.Hom (Fᴴ₀ (Δ₋ i)) (Fᴴ₀ (Δ₋ j)))
        → k ≡ᵢ i
        → ¬ (k ≡ᵢ j)
        → (α : ⌞ Δ₋ k ⌟)
        → σ̅ σ · ι (suc n) k α ≡ H.η Δ · ι n k α
      σ̅-ι-k1j-ext n {i = i} {j} {k} σ k=ᵢi k≠ᵢj α with k ≡ᵢ? i | k ≡ᵢ? j
      ... | no  k≠ᵢi | _        = absurd (k≠ᵢi k=ᵢi)
      ... | yes _    | yes k=ᵢj = absurd (k≠ᵢj k=ᵢj)
      ... | yes _    | no _     = refl

      σ̅-ι-ik-ext : ∀ (n : Nat) {i j k : I} (σ : SOrdᴴ.Hom (Fᴴ₀ (Δ₋ i)) (Fᴴ₀ (Δ₋ j)))
        → ¬ (k ≡ᵢ i)
        → k ≡ᵢ j
        → (α : ⌞ Δ₋ k ⌟)
        → σ̅ σ · ι n k α ≡ H.η Δ · ι (suc n) k α
      σ̅-ι-ik-ext n {i = i} {j} {k} σ k≠ᵢi k=ᵢj α with k ≡ᵢ? i | k ≡ᵢ? j
      ... | yes k=ᵢi | _        = absurd (k≠ᵢi k=ᵢi)
      ... | no  _    | no  k≠ᵢj = absurd (k≠ᵢj k=ᵢj)
      ... | no  _    | yes _    = refl

      σ̅-ι-ij-ext : ∀ (n : Nat) {i j k : I} (σ : SOrdᴴ.Hom (Fᴴ₀ (Δ₋ i)) (Fᴴ₀ (Δ₋ j)))
        → ¬ (k ≡ᵢ i)
        → ¬ (k ≡ᵢ j)
        → (α : ⌞ Δ₋ k ⌟)
        → σ̅ σ · ι n k α ≡ H.η Δ · ι n k α
      σ̅-ι-ij-ext n {i = i} {j} {k} σ k≠ᵢi k≠ᵢj α with k ≡ᵢ? i | k ≡ᵢ? j
      ... | yes k=ᵢi | _        = absurd (k≠ᵢi k=ᵢi)
      ... | no  _    | yes k=ᵢj = absurd (k≠ᵢj k=ᵢj)
      ... | no  _    | no  _    = refl

  -- Wrapped β rules of H.M₁ (σ̅ σ)
  module _ where
    abstract
      H-σ̅-ι-k0j : ∀ {k j : I} (σ : SOrdᴴ.Hom (FᴴΔ₋ k) (FᴴΔ₋ j)) (α : ⌞ H.M₀ (Δ₋ k) ⌟)
        → H.μ Δ · (H.M₁ (σ̅ σ) · (H.M₁ (ι-hom 0 k) · α))
        ≡ H.M₁ (ι-hom 0 j) · (σ · α)
      H-σ̅-ι-k0j {k = k} {j} σ α =
        H.μ Δ · (H.M₁ (σ̅ σ) · (H.M₁ (ι-hom 0 k) · α))
          ≡˘⟨ ap· (H.μ Δ) $ H.M-∘ (σ̅ σ) (ι-hom 0 k) ·ₚ α ⟩
        H.μ Δ · (H.M₁ (σ̅ σ ∘ ι-hom 0 k) · α)
          ≡⟨ ap (λ m → H.μ Δ · (H.M₁ m · α)) $ ext $ σ̅-ι-k0j-ext σ reflᵢ ⟩
        H.μ Δ · (H.M₁ (H.M₁ (ι-hom 0 j) ∘ σ .fst ∘ H.η (Δ₋ k)) · α)
          ≡⟨ μ-M-∘-M H (ι-hom 0 j) (σ .fst ∘ H.η (Δ₋ k)) ·ₚ α ⟩
        H.M₁ (ι-hom 0 j) · (H.μ (Δ₋ j) · (H.M₁ (σ .fst ∘ H.η (Δ₋ k)) · α))
          ≡⟨ ap· (H.M₁ (ι-hom 0 j)) $ μ-M-∘-Algebraic H σ (H.η (Δ₋ k)) ·ₚ α ⟩
        H.M₁ (ι-hom 0 j) · (σ · (H.μ (Δ₋ k) · (H.M₁ (H.η (Δ₋ k)) · α)))
          ≡⟨ ap· (H.M₁ (ι-hom 0 j) ∘ σ .fst) $ H.μ-unitr ·ₚ _ ⟩
        H.M₁ (ι-hom 0 j) · (σ · α)
          ∎

      H-σ̅-η-ι-k1k : ∀ (n : Nat) {i : I} (σ : SOrdᴴ.Hom (Fᴴ₀ (Δ₋ i)) (Fᴴ₀ (Δ₋ i)))
        → (α : ⌞ Δ₋ i ⌟)
        → H.μ Δ · (H.M₁ (σ̅ σ) · (H.η Δ · ι (suc n) i α))
        ≡ H.η Δ · ι (suc n) i α
      H-σ̅-η-ι-k1k n {i = i} σ α =
        H.μ Δ · (H.M₁ (σ̅ σ) · (H.η Δ · ι (suc n) i α))
          ≡⟨ μ-η H (σ̅ σ) ·ₚ _ ⟩
        σ̅ σ · ι (suc n) i α
          ≡⟨ σ̅-ι-k1k-ext n σ reflᵢ reflᵢ α ⟩
        H.η Δ · ι (suc n) i α
          ∎

      H-σ̅-η-ι-k1j : ∀ (n : Nat) {k j : I} (σ : SOrdᴴ.Hom (Fᴴ₀ (Δ₋ k)) (Fᴴ₀ (Δ₋ j)))
        → ¬ (k ≡ᵢ j)
        → (α : ⌞ Δ₋ k ⌟)
        → H.μ Δ · (H.M₁ (σ̅ σ) · (H.η Δ · ι (suc n) k α))
        ≡ H.η Δ · ι n k α
      H-σ̅-η-ι-k1j n {k = k} σ k≠j α =
        H.μ Δ · (H.M₁ (σ̅ σ) · (H.η Δ · ι (suc n) k α))
          ≡⟨ μ-η H (σ̅ σ) ·ₚ _ ⟩
        σ̅ σ · ι (suc n) k α
          ≡⟨ σ̅-ι-k1j-ext n σ reflᵢ k≠j α ⟩
        H.η Δ · ι n k α
          ∎

      H-σ̅-η-ι-ik : ∀ (n : Nat) {i k : I} (σ : SOrdᴴ.Hom (Fᴴ₀ (Δ₋ i)) (Fᴴ₀ (Δ₋ k)))
        → ¬ (k ≡ᵢ i)
        → (α : ⌞ Δ₋ k ⌟)
        → H.μ Δ · (H.M₁ (σ̅ σ) · (H.η Δ · ι n k α))
        ≡ H.η Δ · ι (suc n) k α
      H-σ̅-η-ι-ik n {i = i} {k} σ k≠i α =
        H.μ Δ · (H.M₁ (σ̅ σ) · (H.η Δ · ι n k α))
          ≡⟨ μ-η H (σ̅ σ) ·ₚ _ ⟩
        σ̅ σ · ι n k α
          ≡⟨ σ̅-ι-ik-ext n σ k≠i reflᵢ α ⟩
        H.η Δ · ι (suc n) k α
          ∎

      H-σ̅-η-ι-ij : ∀ (n : Nat) {i j k : I} (σ : SOrdᴴ.Hom (Fᴴ₀ (Δ₋ i)) (Fᴴ₀ (Δ₋ j)))
        → ¬ (k ≡ᵢ i)
        → ¬ (k ≡ᵢ j)
        → (α : ⌞ Δ₋ k ⌟)
        → H.μ Δ · (H.M₁ (σ̅ σ) · (H.η Δ · ι n k α))
        ≡ H.η Δ · ι n k α
      H-σ̅-η-ι-ij n {i = i} {j} {k} σ k≠i k≠j α =
        H.μ Δ · (H.M₁ (σ̅ σ) · (H.η Δ · ι n k α))
          ≡⟨ μ-η H (σ̅ σ) ·ₚ _ ⟩
        σ̅ σ · ι n k α
          ≡⟨ σ̅-ι-ij-ext n σ k≠i k≠j α ⟩
        H.η Δ · ι n k α
          ∎

  abstract
    σ̅-id : ∀ {i : I} (n : Nat) (k : I) (α : ⌞ Δ₋ k ⌟) →
      σ̅ {i = i} SOrdᴴ.id · ι n k α ≡ H.η Δ · ι n k α
    σ̅-id {i = i} n k α with k ≡ᵢ? i | n
    ... | yes reflᵢ | 0     = sym (H.unit.is-natural (Δ₋ i) Δ (ι-hom 0 i)) ·ₚ α
    ... | yes reflᵢ | suc n = refl
    ... | no _      | n     = refl

  abstract
    σ̅-∘ : ∀ {i j k : I}
      (σ : SOrdᴴ.Hom (FᴴΔ₋ j) (FᴴΔ₋ k))
      (δ : SOrdᴴ.Hom (FᴴΔ₋ i) (FᴴΔ₋ j))
      (n : Nat) (l : I) (α : ⌞Δ₋⌟ l)
      → σ̅ (σ SOrdᴴ.∘ δ) · ι n l α
      ≡ (H.μ Δ ∘ H.M₁ (σ̅ σ) ∘ σ̅ δ) · ι n l α
    σ̅-∘ {i = i} {j} {k} σ δ n l α with l ≡ᵢ? i | n | l ≡ᵢ? j | l ≡ᵢ? k
    ... | yes reflᵢ | 0     | _         | _         = sym $ H-σ̅-ι-k0j σ (δ · (H.η (Δ₋ i) · α))
    -- Note: the following eight cases correspond to the table in the paper with eight rows.
    ... | yes reflᵢ | suc n | yes reflᵢ | yes reflᵢ = sym $ H-σ̅-η-ι-k1k n σ α
    ... | yes reflᵢ | suc n | yes reflᵢ | no  l≠k   = sym $ H-σ̅-η-ι-k1j n σ l≠k α
    ... | yes reflᵢ | suc n | no  l≠j   | yes reflᵢ = sym $ H-σ̅-η-ι-ik n σ l≠j α
    ... | yes reflᵢ | suc n | no  l≠j   | no  l≠k   = sym $ H-σ̅-η-ι-ij n σ l≠j l≠k α
    ... | no  l≠i   | n     | yes reflᵢ | yes reflᵢ = sym $ H-σ̅-η-ι-k1k n σ α
    ... | no  l≠i   | n     | yes reflᵢ | no  l≠k   = sym $ H-σ̅-η-ι-k1j n σ l≠k α
    ... | no  l≠i   | n     | no  l≠j   | yes reflᵢ = sym $ H-σ̅-η-ι-ik n σ l≠j α
    ... | no  l≠i   | n     | no  l≠j   | no  l≠k   = sym $ H-σ̅-η-ι-ij n σ l≠j l≠k α

  T : Functor (Indexed SOrdᴴ FᴴΔ₋) (Endos SOrdᴴ (Fᴴ₀ Δ))
  T .Functor.F₀ i = tt
  T .Functor.F₁ σ .fst = H.μ Δ ∘ H.M₁ (σ̅ σ)
  T .Functor.F₁ σ .snd = ext λ α →
    H.μ Δ · (H.M₁ (σ̅ σ) · (H.μ Δ · α))               ≡˘⟨ ap· (H.μ _) $ H.mult.is-natural _ _ (σ̅ σ) ·ₚ α ⟩
    H.μ Δ · (H.μ (H.M₀ Δ) · (H.M₁ (H.M₁ (σ̅ σ)) · α)) ≡˘⟨ μ-M-∘-μ H (H.M₁ (σ̅ σ)) ·ₚ α ⟩
    H.μ Δ · (H.M₁ (H.μ Δ ∘ H.M₁ (σ̅ σ)) · α)          ∎
  T .Functor.F-id = ext λ α →
    H.μ _ · (H.M₁ (σ̅ SOrdᴴ.id) · α) ≡⟨ ap (λ m → H.μ _ · (H.M₁ m · α)) $ ext σ̅-id ⟩
    H.μ _ · (H.M₁ (H.η _) · α)      ≡⟨ H.μ-unitr ·ₚ _ ⟩
    α                               ∎
  T .Functor.F-∘ σ δ = ext λ α →
    H.μ Δ · (H.M₁ (σ̅ (σ SOrdᴴ.∘ δ)) · α)                   ≡⟨ ap· (H.μ Δ) $ ap (H.M₁) (ext $ σ̅-∘ σ δ) ·ₚ α ⟩
    H.μ Δ · (H.M₁ (H.μ Δ ∘ H.M₁ (σ̅ σ) ∘ σ̅ δ) · α)          ≡⟨ μ-M-∘-μ H (H.M₁ (σ̅ σ) ∘ σ̅ δ) ·ₚ α ⟩
    H.μ Δ · (H.μ (H.M₀ Δ) · (H.M₁ (H.M₁ (σ̅ σ) ∘ σ̅ δ) · α)) ≡⟨ ap· (H.μ Δ) $ μ-M-∘-M H (σ̅ σ) (σ̅ δ) ·ₚ α ⟩
    H.μ Δ · (H.M₁ (σ̅ σ) · (H.μ Δ · (H.M₁ (σ̅ δ) · α)))      ∎

  --------------------------------------------------------------------------------
  -- Constructing the natural transformation ν
  -- Section 3.4, Lemma 3.8

  ν : Indexed-include => Endos-include F∘ T
  ν ._=>_.η i = Free-EM .Functor.F₁ (ι-hom 0 i)
  ν ._=>_.is-natural i j σ = sym $ ext $ H-σ̅-ι-k0j σ

  --------------------------------------------------------------------------------
  -- Faithfulness of T
  -- Section 3.4, Lemma 3.9

  abstract
    T-faithful : preserves-monos F → is-faithful T
    T-faithful H-preserves-monos {i} {j} {σ} {δ} eq =
      ∫Hom-path (Monad-algebras H)
        (H-preserves-monos ι-monic _ _ $ ext λ α →
         H.M₁ (ι-hom 0 j) · (σ · α)                    ≡˘⟨ H-σ̅-ι-k0j σ α ⟩
         H.μ Δ · (H.M₁ (σ̅ σ) · (H.M₁ (ι-hom 0 i) · α)) ≡⟨ eq ·ₚ (H.M₁ (ι-hom 0 i) · α) ⟩
         H.μ Δ · (H.M₁ (σ̅ δ) · (H.M₁ (ι-hom 0 i) · α)) ≡⟨ H-σ̅-ι-k0j δ α ⟩
         H.M₁ (ι-hom 0 j) · (δ · α)                    ∎)
        prop!
