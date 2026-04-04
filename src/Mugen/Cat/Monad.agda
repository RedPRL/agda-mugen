module Mugen.Cat.Monad where

open import Cat.Diagram.Monad
open import Cat.Displayed.Total using (∫Hom; ∫Hom-path)
import Cat.Reasoning as Cat

open import Mugen.Prelude

--------------------------------------------------------------------------------
-- Misc. Lemmas for Monads

module _ {o r} {C : Precategory o r} {F : Functor C C} (M : Monad-on F) where
  private
    open Cat C
    module M = Monad-on M

    Free₀ : Ob → Algebra M
    Free₀ = Free-EM {M = M} .Functor.F₀

    Free₁ : ∀ {X Y} → Hom X Y → Algebra-hom M (Free₀ X) (Free₀ Y)
    Free₁ = Functor.F₁ (Free-EM {M = M})

  abstract
    μ-M-∘-Algebraic : ∀ {X Y Z} (σ : Algebra-hom M (Free₀ Y) (Free₀ Z)) (δ : Hom X (M.M₀ Y))
      → M.μ Z ∘ M.M₁ (σ .∫Hom.fst ∘ δ) ≡ σ .∫Hom.fst ∘ M.μ Y ∘ M.M₁ δ
    μ-M-∘-Algebraic {X = X} {Y} {Z} σ δ =
      M.μ Z ∘ M.M₁ (σ .∫Hom.fst ∘ δ)
        ≡⟨ ap (M.μ Z ∘_) $ M.M-∘ (σ .∫Hom.fst) δ ⟩
      M.μ Z ∘ M.M₁ (σ .∫Hom.fst) ∘ (M.M₁ δ)
        ≡⟨ assoc (M.μ Z) (M.M₁ (σ .∫Hom.fst)) (M.M₁ δ) ⟩
      (M.μ Z ∘ M.M₁ (σ .∫Hom.fst)) ∘ (M.M₁ δ)
        ≡˘⟨ ap (_∘ M.M₁ δ) $ σ .∫Hom.snd ⟩
      (σ .∫Hom.fst ∘ M.μ Y) ∘ M.M₁ δ
        ≡˘⟨ assoc (σ .∫Hom.fst) (M.μ Y) (M.M₁ δ) ⟩
      σ .∫Hom.fst ∘ M.μ Y ∘ M.M₁ δ
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
        ≡⟨ ap (_∘ M.M₁ σ) $ M.μ-assoc ⟩
      (M.μ Y ∘ M.μ (M.M₀ Y)) ∘ M.M₁ σ
        ≡˘⟨ assoc (M.μ Y) (M.μ (M.M₀ Y)) (M.M₁ σ) ⟩
      M.μ Y ∘ M.μ (M.M₀ Y) ∘ M.M₁ σ
        ∎

    -- Favonia: what would be a better name?
    μ-η : ∀ {X Y} (σ : Hom X (M.M₀ Y))
      → M.μ Y ∘ M.M₁ σ ∘ M.η X ≡ σ
    μ-η {X = X} {Y} σ =
      M.μ Y ∘ M.M₁ σ ∘ M.η X
        ≡˘⟨ ap (M.μ Y ∘_) $ M.unit ._=>_.is-natural X (M.M₀ Y) σ ⟩
      M.μ Y ∘ M.η (M.M₀ Y) ∘ σ
        ≡⟨ assoc (M.μ Y) (M.η (M.M₀ Y)) σ ⟩
      (M.μ Y ∘ M.η (M.M₀ Y)) ∘ σ
        ≡⟨ eliml M.μ-unitl ⟩
      σ
        ∎

    -- Favonia: does this lemma belong to 1lab?
    free-algebra-hom-path : ∀ {X Y} {f g : Algebra-hom M (Free₀ X) (Free₀ Y)}
      → f .∫Hom.fst ∘ M.η _ ≡ (g .∫Hom.fst ∘ M.η _) → f ≡ g
    free-algebra-hom-path {f = f} {g = g} p =
      ∫Hom-path (Monad-algebras M)
        (f .∫Hom.fst                        ≡⟨ intror M.μ-unitr ⟩
         f .∫Hom.fst ∘ M.μ _ ∘ M.M₁ (M.η _) ≡˘⟨ μ-M-∘-Algebraic f (M.η _) ⟩
         M.μ _ ∘ M.M₁ (f .∫Hom.fst ∘ M.η _) ≡⟨ ap (λ ϕ → M.μ _ ∘ M.M₁ ϕ) p ⟩
         M.μ _ ∘ M.M₁ (g .∫Hom.fst ∘ M.η _) ≡⟨ μ-M-∘-Algebraic g (M.η _) ⟩
         g .∫Hom.fst ∘ M.μ _ ∘ M.M₁ (M.η _) ≡⟨ elimr M.μ-unitr ⟩
         g .∫Hom.fst                        ∎)
        prop!
