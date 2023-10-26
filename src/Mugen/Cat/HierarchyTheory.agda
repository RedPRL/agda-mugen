module Mugen.Cat.HierarchyTheory where

open import Cat.Diagram.Monad
import Cat.Reasoning as Cat

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Order.StrictOrder

open import Mugen.Cat.StrictOrders

open import Mugen.Order.LeftInvariantRightCentered

open Strictly-monotone
open Functor
open _=>_

--------------------------------------------------------------------------------
-- Heirarchy Theories
--
-- A heirarchy theory is defined to be a monad on the category of strict orders.
-- We also define the McBride Heirarchy Theory.

Hierarchy-theory : ∀ o r → Type (lsuc o ⊔ lsuc r)
Hierarchy-theory o r = Monad (Strict-orders o r)

--------------------------------------------------------------------------------
-- The McBride Hierarchy Theory
-- Section 3.1
--
-- A construction of the McBride Monad for any displacement algebra '𝒟'

ℳ : ∀ {o} → Displacement-algebra o o → Hierarchy-theory o o
ℳ {o = o} 𝒟 = ht where
  open Displacement-algebra 𝒟

  M : Functor (Strict-orders o o) (Strict-orders o o)
  M .F₀ L = L ⋉ strict-order [ ε ]
  M .F₁ f .hom (l , d) = (f .hom l) , d
  M .F₁ f .strict-mono x<y =
    ⋉-elim (λ a1≡a2 b1<b2 → biased (ap (f .hom) a1≡a2) b1<b2)
           (λ a1<a2 b1≤b b≤b2 → centred (f .strict-mono a1<a2) b1≤b b≤b2)
           (λ _ → trunc) x<y
  M .F-id = ext λ _ → refl
  M .F-∘ f g = ext λ _ → refl

  unit : Id => M
  unit .η L .hom l = l , ε
  unit .η L .strict-mono l<l' = centred l<l' (inl refl) (inl refl)
  unit .is-natural L L' f = ext λ _ → refl

  mult : M F∘ M => M
  mult .η L .hom ((l , x) , y) = l , (x ⊗ y)
  mult .η L .strict-mono {(α , d1) , d2} {(β , e1) , e2} l<l' =
    ⋉-elim (λ α≡β d2<e2 → biased (ap fst α≡β) (≡-transl (ap (λ ϕ → snd ϕ ⊗ d2) α≡β) (left-invariant d2<e2)))
           (λ α<β d2≤ε ε≤e2 →
             let d1⊗d2≤d1 = ≤-trans (left-invariant-≤ d2≤ε) (inl idr)
                 e1≤e1⊗e2 = ≤-trans (inl (sym idr)) (left-invariant-≤ ε≤e2)
             in
             ⋉-elim (λ α≡β d1<e1 →
                      biased α≡β (≤-transl d1⊗d2≤d1 (≤-transr d1<e1 e1≤e1⊗e2)))
                    (λ α<β d1≤ε ε≤e1 →
                      centred α<β (≤-trans d1⊗d2≤d1 d1≤ε) (≤-trans ε≤e1 e1≤e1⊗e2))
                      (λ _ → trunc)
                    α<β)
           (λ _ → trunc) l<l'
  mult .is-natural L L' f = ext λ _ → refl

  ht : Hierarchy-theory o o
  ht .Monad.M = M
  ht .Monad.unit = unit
  ht .Monad.mult = mult
  ht .Monad.left-ident = ext λ where
    (α , d) i → (α , idl {d} i)
  ht .Monad.right-ident = ext λ where
    (α , d) i → (α , idr {d} i)
  ht .Monad.mult-assoc = ext λ where
    (((α , d1) , d2) , d3) i → α , associative {d1} {d2} {d3} (~ i)

--------------------------------------------------------------------------------
-- Hierarchy Theory Algebras

module _ {o r} {H : Hierarchy-theory o r} where
  private
    module H = Monad H

    Free⟨_⟩ : Strict-order o r → Algebra (Strict-orders o r) H
    Free⟨_⟩ = Functor.F₀ (Free (Strict-orders o r) H)

    open Cat (Strict-orders o r)
    open Algebra-hom

  -- NOTE: We can't use any fancy reasoning combinators in this proof, as it really
  -- upsets the unifier, as it will fail to unify the homomorphism proofs...
  free-algebra-path : ∀ {X Y} {f g : Algebra-hom (Strict-orders o r) H Free⟨ X ⟩ Free⟨ Y ⟩}
                                         → f .morphism ∘ H.unit.η _ ≡ (g .morphism ∘ H.unit.η _)
                                         → f ≡ g
  free-algebra-path {f = f} {g = g} p = Algebra-hom-path _ $
    f .morphism                                           ≡⟨ intror H.left-ident ⟩
    f .morphism ∘ H.mult.η _ ∘ H.M₁ (H.unit.η _)          ≡⟨ assoc (f .morphism) (H.mult.η _) (H.M₁ (H.unit.η _)) ⟩
    (f .morphism ∘ H.mult.η _) ∘ H.M₁ (H.unit.η _)        ≡⟨ ap (_∘ H.M₁ (H.unit.η _)) (f .commutes) ⟩
    (H.mult.η _ ∘ H.M₁ (f .morphism)) ∘ H.M₁ (H.unit.η _) ≡˘⟨ assoc (H.mult.η _) (H.M₁ (f .morphism)) (H.M₁ (H.unit.η _)) ⟩
    H.mult.η _ ∘ H.M₁ (f .morphism) ∘ H.M₁ (H.unit.η _)   ≡˘⟨ ap (H.mult.η _ ∘_) (H.M-∘ _ _) ⟩
    H.mult.η _ ∘ H.M₁ (f .morphism ∘ H.unit.η _)          ≡⟨ ap (λ ϕ → H.mult.η _ ∘ H.M₁ ϕ) p ⟩
    H.mult.η _ ∘ H.M₁ (g .morphism ∘ H.unit.η _)          ≡⟨ ap (H.mult.η _ ∘_) (H.M-∘ _ _) ⟩
    H.mult.η _ ∘ H.M₁ (g .morphism) ∘ H.M₁ (H.unit.η _)   ≡⟨ assoc (H.mult.η _) (H.M₁ (g .morphism)) (H.M₁ (H.unit.η _)) ⟩
    (H.mult.η _ ∘ H.M₁ (g .morphism)) ∘ H.M₁ (H.unit.η _) ≡˘⟨ ap (_∘ H.M₁ (H.unit.η _)) (g .commutes) ⟩
    (g .morphism ∘ H.mult.η _) ∘ H.M₁ (H.unit.η _)        ≡˘⟨ assoc (g .morphism) (H.mult.η _) (H.M₁ (H.unit.η _)) ⟩
    g .morphism ∘ H.mult.η _ ∘ H.M₁ (H.unit.η _)          ≡⟨ elimr H.left-ident ⟩
    g .morphism ∎

--------------------------------------------------------------------------------
-- Misc. Definitions

preserves-monos : ∀ {o r} (H : Hierarchy-theory o r) → Type (lsuc o ⊔ lsuc r)
preserves-monos {o} {r} H = ∀ {X Y} → (f : Hom X Y) → is-monic f → is-monic (H.M₁ f)
  where
    module H = Monad H
    open Cat (Strict-orders o r)
