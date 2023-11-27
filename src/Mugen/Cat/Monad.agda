module Mugen.Cat.Monad where

open import Cat.Diagram.Monad
import Cat.Reasoning as Cat

open import Mugen.Prelude
open import Mugen.Order.Poset

--------------------------------------------------------------------------------
-- Misc. Lemmas for Monads

module _ {o r} {C : Precategory o r} (M : Monad C) where
  private
    module M = Monad M

    open Cat C
    open Algebra-hom

    Free⟨_⟩ : C .Precategory.Ob → Algebra C M
    Free⟨_⟩ = Functor.F₀ (Free C M)

  -- Favonia: does this lemma belong to 1lab?
  --
  -- NOTE: We can't use any fancy reasoning combinators in this proof, as it really
  -- upsets the unifier, as it will fail to unify the homomorphism proofs...
  free-algebra-hom-path : ∀ {X Y} {f g : Algebra-hom C M Free⟨ X ⟩ Free⟨ Y ⟩}
    → f .morphism ∘ M.unit.η _ ≡ (g .morphism ∘ M.unit.η _)
    → f ≡ g
  free-algebra-hom-path {f = f} {g = g} p = Algebra-hom-path _ $
    f .morphism                                           ≡⟨ intror M.left-ident ⟩
    f .morphism ∘ M.mult.η _ ∘ M.M₁ (M.unit.η _)          ≡⟨ assoc (f .morphism) (M.mult.η _) (M.M₁ (M.unit.η _)) ⟩
    (f .morphism ∘ M.mult.η _) ∘ M.M₁ (M.unit.η _)        ≡⟨ ap (_∘ M.M₁ (M.unit.η _)) (f .commutes) ⟩
    (M.mult.η _ ∘ M.M₁ (f .morphism)) ∘ M.M₁ (M.unit.η _) ≡˘⟨ assoc (M.mult.η _) (M.M₁ (f .morphism)) (M.M₁ (M.unit.η _)) ⟩
    M.mult.η _ ∘ M.M₁ (f .morphism) ∘ M.M₁ (M.unit.η _)   ≡˘⟨ ap (M.mult.η _ ∘_) (M.M-∘ _ _) ⟩
    M.mult.η _ ∘ M.M₁ (f .morphism ∘ M.unit.η _)          ≡⟨ ap (λ ϕ → M.mult.η _ ∘ M.M₁ ϕ) p ⟩
    M.mult.η _ ∘ M.M₁ (g .morphism ∘ M.unit.η _)          ≡⟨ ap (M.mult.η _ ∘_) (M.M-∘ _ _) ⟩
    M.mult.η _ ∘ M.M₁ (g .morphism) ∘ M.M₁ (M.unit.η _)   ≡⟨ assoc (M.mult.η _) (M.M₁ (g .morphism)) (M.M₁ (M.unit.η _)) ⟩
    (M.mult.η _ ∘ M.M₁ (g .morphism)) ∘ M.M₁ (M.unit.η _) ≡˘⟨ ap (_∘ M.M₁ (M.unit.η _)) (g .commutes) ⟩
    (g .morphism ∘ M.mult.η _) ∘ M.M₁ (M.unit.η _)        ≡˘⟨ assoc (g .morphism) (M.mult.η _) (M.M₁ (M.unit.η _)) ⟩
    g .morphism ∘ M.mult.η _ ∘ M.M₁ (M.unit.η _)          ≡⟨ elimr M.left-ident ⟩
    g .morphism ∎
