module Mugen.Cat.Monad where

open import Cat.Diagram.Monad
import Cat.Reasoning as Cat

open import Mugen.Prelude

--------------------------------------------------------------------------------
-- Misc. Lemmas for Monads

module _ {o r} {C : Precategory o r} (M : Monad C) where
  private
    module M = Monad M

    open Cat C
    open Algebra-hom

    Free₀ : Ob → Algebra C M
    Free₀ = Functor.F₀ (Free C M)

    Free₁ : ∀ {X Y} → Hom X Y → Algebra-hom C M (Free₀ X) (Free₀ Y)
    Free₁ = Functor.F₁ (Free C M)

  abstract
    μ-M-∘-Algebraic : ∀ {X Y Z} (σ : Algebra-hom C M (Free₀ Y) (Free₀ Z)) (δ : Hom X (M.M₀ Y))
      → M.μ Z ∘ M.M₁ (σ .morphism ∘ δ) ≡ σ .morphism ∘ M.μ Y ∘ M.M₁ δ
    μ-M-∘-Algebraic {X = X} {Y} {Z} σ δ =
      M.μ Z ∘ M.M₁ (σ .morphism ∘ δ)
        ≡⟨ ap (M.μ Z ∘_) $ M.M-∘ (σ .morphism) δ ⟩
      M.μ Z ∘ M.M₁ (σ .morphism) ∘ (M.M₁ δ)
        ≡⟨ assoc (M.μ Z) (M.M₁ (σ .morphism)) (M.M₁ δ) ⟩
      (M.μ Z ∘ M.M₁ (σ .morphism)) ∘ (M.M₁ δ)
        ≡˘⟨ ap (_∘ M.M₁ δ) $ σ .commutes ⟩
      (σ .morphism ∘ M.μ Y) ∘ M.M₁ δ
        ≡˘⟨ assoc (σ .morphism) (M.μ Y) (M.M₁ δ) ⟩
      σ .morphism ∘ M.μ Y ∘ M.M₁ δ
        ∎

    μ-M-∘-M : ∀ {X Y Z} (σ : Hom Y Z) (δ : Hom X (M.M₀ Y))
      → M.μ Z ∘ M.M₁ (M.M₁ σ ∘ δ) ≡ M.M₁ σ ∘ M.μ Y ∘ M.M₁ δ
    μ-M-∘-M σ δ = μ-M-∘-Algebraic (Free₁ σ) δ

    μ-M-∘-μ : ∀ {X Y} (σ : Hom X (M.M₀ (M.M₀ Y)))
      → M.μ Y ∘ M.M₁ (M.μ Y ∘ σ) ≡ M.μ Y ∘ M.μ (M.M₀ Y) ∘ M.M₁ σ
    μ-M-∘-μ {Y = Y} σ =
      M.μ Y ∘ M.M₁ (M.μ Y ∘ σ)
        ≡⟨ ap (M.μ Y ∘_) $ M.M-∘ (M.μ Y) σ ⟩
      M.μ Y ∘ M.M₁ (M.μ Y) ∘ M.M₁ σ
        ≡⟨ assoc (M.μ Y) (M.M₁ (M.μ Y)) (M.M₁ σ) ⟩
      (M.μ Y ∘ M.M₁ (M.μ Y)) ∘ M.M₁ σ
        ≡⟨ ap (_∘ M.M₁ σ) $ M.mult-assoc ⟩
      (M.μ Y ∘ M.μ (M.M₀ Y)) ∘ M.M₁ σ
        ≡˘⟨ assoc (M.μ Y) (M.μ (M.M₀ Y)) (M.M₁ σ) ⟩
      M.μ Y ∘ M.μ (M.M₀ Y) ∘ M.M₁ σ
        ∎

    -- Favonia: what would be a better name?
    μ-η : ∀ {X Y} (σ : Hom X (M.M₀ Y))
      → M.μ Y ∘ M.M₁ σ ∘ M.η X ≡ σ
    μ-η {X = X} {Y} σ =
      M.μ Y ∘ M.M₁ σ ∘ M.η X
        ≡˘⟨ ap (M.μ Y ∘_) $ M.unit.is-natural X (M.M₀ Y) σ ⟩
      M.μ Y ∘ M.η (M.M₀ Y) ∘ σ
        ≡⟨ assoc (M.μ Y) (M.η (M.M₀ Y)) σ ⟩
      (M.μ Y ∘ M.η (M.M₀ Y)) ∘ σ
        ≡⟨ eliml M.right-ident ⟩
      σ
        ∎

    -- Favonia: does this lemma belong to 1lab?
    free-algebra-hom-path : ∀ {X Y} {f g : Algebra-hom C M (Free₀ X) (Free₀ Y)}
      → f .morphism ∘ M.η _ ≡ (g .morphism ∘ M.η _) → f ≡ g
    free-algebra-hom-path {f = f} {g = g} p = Algebra-hom-path _ $
      f .morphism                        ≡⟨ intror M.left-ident ⟩
      f .morphism ∘ M.μ _ ∘ M.M₁ (M.η _) ≡˘⟨ μ-M-∘-Algebraic f (M.η _) ⟩
      M.μ _ ∘ M.M₁ (f .morphism ∘ M.η _) ≡⟨ ap (λ ϕ → M.μ _ ∘ M.M₁ ϕ) p ⟩
      M.μ _ ∘ M.M₁ (g .morphism ∘ M.η _) ≡⟨ μ-M-∘-Algebraic g (M.η _) ⟩
      g .morphism ∘ M.μ _ ∘ M.M₁ (M.η _) ≡⟨ elimr M.left-ident ⟩
      g .morphism ∎
