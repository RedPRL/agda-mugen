module Mugen.Cat.HierarchyTheory where

open import Cat.Diagram.Monad
import Cat.Reasoning as Cat

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Cat.StrictOrders
open import Mugen.Order.LeftInvariantRightCentered
open import Mugen.Order.Poset

import Mugen.Order.Reasoning

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
  open Mugen.Order.Reasoning poset

  M : Functor (Strict-orders o o) (Strict-orders o o)
  M .F₀ L = L ⋉[ ε ] poset
  M .F₁ f .hom (l , d) = (f .hom l) , d
  M .F₁ {L} {N} f .mono {l1 , d1} {l2 , d2} = ∥-∥-map λ where
    (biased l1=l2 d1≤d2) → biased (ap (f .hom) l1=l2) d1≤d2
    (centred l1≤l2 d1≤ε ε≤d2) → centred (f .mono l1≤l2) d1≤ε ε≤d2
  M .F₁ {L} {N} f .inj-on-related {l1 , d1} {l2 , d2} =
    ∥-∥-rec (Π-is-hlevel 1 λ _ → Poset.has-is-set (M .F₀ L) _ _) λ where
      (biased l1=l2 _) p → ap₂ _,_ l1=l2 (ap snd p)
      (centred l1≤l2 _ _) p → ap₂ _,_ (f .inj-on-related l1≤l2 (ap fst p)) (ap snd p)
  M .F-id = trivial!
  M .F-∘ f g = trivial!

  unit : Id => M
  unit .η L .hom l = l , ε
  unit .η L .mono l1≤l2 = inc (centred l1≤l2 ≤-refl ≤-refl)
  unit .η L .inj-on-related _ p = ap fst p
  unit .is-natural L L' f = trivial!

  mult : M F∘ M => M
  mult .η L .hom ((l , x) , y) = l , (x ⊗ y)
  mult .η L .mono {(a1 , d1) , e1} {(a2 , d2) , e2} =
    ∥-∥-rec squash lemma where
      lemma : (M .F₀ L) ⋉[ ε ] poset [ ((a1 , d1) , e1) raw≤ ((a2 , d2) , e2) ]
        → L ⋉[ ε ] poset [ (a1 , (d1 ⊗ e1)) ≤ (a2 , (d2 ⊗ e2)) ]
      lemma (biased ad1=ad2 e1≤e2) =
        inc (biased (ap fst ad1=ad2) (=+≤→≤ (ap (_⊗ e1) (ap snd ad1=ad2)) (≤-left-invariant e1≤e2)))
      lemma (centred ad1≤ad2 e1≤ε ε≤e2) = ∥-∥-map lemma₂ ad1≤ad2 where
        d1⊗e1≤d1 : (d1 ⊗ e1) ≤ d1
        d1⊗e1≤d1 = ≤+=→≤ (≤-left-invariant e1≤ε) idr

        d2≤d2⊗e2 : d2 ≤ (d2 ⊗ e2)
        d2≤d2⊗e2 = =+≤→≤ (sym idr) (≤-left-invariant ε≤e2)

        lemma₂ : L ⋉[ ε ] poset [ (a1 , d1) raw≤ (a2 , d2) ]
          → L ⋉[ ε ] poset [ (a1 , (d1 ⊗ e1)) raw≤ (a2 , (d2 ⊗ e2)) ]
        lemma₂ (biased a1=a2 d1≤d2) = biased a1=a2 (≤-trans d1⊗e1≤d1 (≤-trans d1≤d2 d2≤d2⊗e2))
        lemma₂ (centred a1≤a2 d1≤ε ε≤d2) = centred a1≤a2 (≤-trans d1⊗e1≤d1 d1≤ε) (≤-trans ε≤d2 d2≤d2⊗e2)
  mult .η L .inj-on-related {(a1 , d1) , e1} {(a2 , d2) , e2} =
    ∥-∥-rec (Π-is-hlevel 1 λ _ → Poset.has-is-set (M .F₀ (M .F₀ L)) _ _) lemma where
      lemma : (M .F₀ L) ⋉[ ε ] poset [ ((a1 , d1) , e1) raw≤ ((a2 , d2) , e2) ]
        → (a1 , (d1 ⊗ e1)) ≡ (a2 , (d2 ⊗ e2))
        → ((a1 , d1) , e1) ≡ ((a2 , d2) , e2)
      lemma (biased ad1=ad2 e1≤e2) p i =
        ad1=ad2 i , injr-on-≤ e1≤e2 (ap snd p ∙ ap (_⊗ e2) (sym $ ap snd ad1=ad2)) i
      lemma (centred ad1≤ad2 e1≤ε ε≤e2) p i = (a1=a2 i , d1=d2 i) , e1=e2 i where
        a1=a2 : a1 ≡ a2
        a1=a2 = ap fst p

        d2≤d1 : d2 ≤ d1
        d2≤d1 =
          d2      ≐⟨ sym idr ⟩
          d2 ⊗ ε  ≤⟨ ≤-left-invariant ε≤e2 ⟩
          d2 ⊗ e2 ≐⟨ sym $ ap snd p ⟩
          d1 ⊗ e1 ≤⟨ ≤-left-invariant e1≤ε ⟩
          d1 ⊗ ε  ≐⟨ idr ⟩
          d1      ≤∎

        d1=d2 : d1 ≡ d2
        d1=d2 = ≤-antisym (⋉-snd-invariant ad1≤ad2) d2≤d1

        e1=e2 : e1 ≡ e2
        e1=e2 = injr-on-≤ (≤-trans e1≤ε ε≤e2) $ ap snd p ∙ ap (_⊗ e2) (sym d1=d2)
  mult .is-natural L L' f = trivial!

  ht : Hierarchy-theory o o
  ht .Monad.M = M
  ht .Monad.unit = unit
  ht .Monad.mult = mult
  ht .Monad.left-ident = ext λ where
    (α , d) → (refl , idl {d})
  ht .Monad.right-ident = ext λ where
    (α , d) → (refl , idr {d})
  ht .Monad.mult-assoc = ext λ where
    (((α , d1) , d2) , d3) → (refl , sym (associative {d1} {d2} {d3}))

--------------------------------------------------------------------------------
-- Hierarchy Theory Algebras

module _ {o r} {H : Hierarchy-theory o r} where
  private
    module H = Monad H

    Free⟨_⟩ : Poset o r → Algebra (Strict-orders o r) H
    Free⟨_⟩ = Functor.F₀ (Free (Strict-orders o r) H)

    open Cat (Strict-orders o r)
    open Algebra-hom

  -- NOTE: We can't use any fancy reasoning combinators in this proof, as it really
  -- upsets the unifier, as it will fail to unify the homomorphism proofs...
  free-algebra-hom-path : ∀ {X Y} {f g : Algebra-hom (Strict-orders o r) H Free⟨ X ⟩ Free⟨ Y ⟩}
    → f .morphism ∘ H.unit.η _ ≡ (g .morphism ∘ H.unit.η _)
    → f ≡ g
  free-algebra-hom-path {f = f} {g = g} p = Algebra-hom-path _ $
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
