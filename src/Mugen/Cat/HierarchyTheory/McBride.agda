module Mugen.Cat.HierarchyTheory.McBride where

open import Cat.Diagram.Monad

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Order.Instances.LeftInvariantRightCentered
open import Mugen.Order.StrictOrder
open import Mugen.Cat.StrictOrders
open import Mugen.Cat.HierarchyTheory

import Mugen.Order.Reasoning

--------------------------------------------------------------------------------
-- The McBride Hierarchy Theory
-- Section 3.1
--
-- A construction of the McBride Monad for any displacement algebra '𝒟'

ℳ : ∀ {o} {A : Poset o o} → Displacement-on A → Hierarchy-theory o o
ℳ {o = o} {A = A} 𝒟 = ht where
  open Displacement-on 𝒟
  open Mugen.Order.Reasoning A

  open Strictly-monotone
  open Functor
  open _=>_

  M : Functor (Strict-orders o o) (Strict-orders o o)
  M .F₀ L = L ⋉[ ε ] A
  M .F₁ f .hom (l , d) = (f .hom l) , d
  M .F₁ {L} {N} f .pres-≤[]-equal {l1 , d1} {l2 , d2} =
    ∥-∥-rec (×-is-hlevel 1 squash $ Π-is-hlevel 1 λ _ → Poset.Ob-is-set (M .F₀ L) _ _) λ where
      (biased l1=l2 d1≤d2) → inc (biased (ap (f .hom) l1=l2) d1≤d2) , λ p → ap₂ _,_ l1=l2 (ap snd p)
      (centred l1≤l2 d1≤ε ε≤d2) → inc (centred (pres-≤ f l1≤l2) d1≤ε ε≤d2) , λ p →
        ap₂ _,_ (injective-on-related f l1≤l2 (ap fst p)) (ap snd p)
  M .F-id = trivial!
  M .F-∘ f g = trivial!

  unit : Id => M
  unit .η L .hom l = l , ε
  unit .η L .pres-≤[]-equal l1≤l2 = inc (centred l1≤l2 ≤-refl ≤-refl) , ap fst
  unit .is-natural L L' f = trivial!

  mult : M F∘ M => M
  mult .η L .hom ((l , x) , y) = l , (x ⊗ y)
  mult .η L .pres-≤[]-equal {(a1 , d1) , e1} {(a2 , d2) , e2} =
    ∥-∥-rec (×-is-hlevel 1 squash $ Π-is-hlevel 1 λ _ → Poset.Ob-is-set (M .F₀ (M .F₀ L)) _ _) lemma where
      lemma : (M .F₀ L) ⋉[ ε ] A [ ((a1 , d1) , e1) raw≤ ((a2 , d2) , e2) ]
        → (L ⋉[ ε ] A [ (a1 , (d1 ⊗ e1)) ≤ (a2 , (d2 ⊗ e2)) ])
        × ((a1 , (d1 ⊗ e1)) ≡ (a2 , (d2 ⊗ e2)) → ((a1 , d1) , e1) ≡ ((a2 , d2) , e2))
      lemma (biased ad1=ad2 e1≤e2) =
        inc (biased (ap fst ad1=ad2) (=+≤→≤ (ap (_⊗ e1) (ap snd ad1=ad2)) (left-invariant e1≤e2))) ,
        λ p i → ad1=ad2 i , injectiver-on-related e1≤e2 (ap snd p ∙ ap (_⊗ e2) (sym $ ap snd ad1=ad2)) i
      lemma (centred ad1≤ad2 e1≤ε ε≤e2) = ∥-∥-map lemma₂ ad1≤ad2 , lemma₃ where
        d1⊗e1≤d1 : (d1 ⊗ e1) ≤ d1
        d1⊗e1≤d1 = ≤+=→≤ (left-invariant e1≤ε) idr

        d2≤d2⊗e2 : d2 ≤ (d2 ⊗ e2)
        d2≤d2⊗e2 = =+≤→≤ (sym idr) (left-invariant ε≤e2)

        lemma₂ : L ⋉[ ε ] A [ (a1 , d1) raw≤ (a2 , d2) ]
          → L ⋉[ ε ] A [ (a1 , (d1 ⊗ e1)) raw≤ (a2 , (d2 ⊗ e2)) ]
        lemma₂ (biased a1=a2 d1≤d2) = biased a1=a2 (≤-trans d1⊗e1≤d1 (≤-trans d1≤d2 d2≤d2⊗e2))
        lemma₂ (centred a1≤a2 d1≤ε ε≤d2) = centred a1≤a2 (≤-trans d1⊗e1≤d1 d1≤ε) (≤-trans ε≤d2 d2≤d2⊗e2)

        lemma₃ : (a1 , (d1 ⊗ e1)) ≡ (a2 , (d2 ⊗ e2)) → ((a1 , d1) , e1) ≡ ((a2 , d2) , e2)
        lemma₃ p i = (a1=a2 i , d1=d2 i) , e1=e2 i where
          a1=a2 : a1 ≡ a2
          a1=a2 = ap fst p

          d2≤d1 : d2 ≤ d1
          d2≤d1 = begin-≤
            d2      ≤⟨ d2≤d2⊗e2 ⟩
            d2 ⊗ e2 ≐⟨ sym $ ap snd p ⟩
            d1 ⊗ e1 ≤⟨ d1⊗e1≤d1 ⟩
            d1      ≤∎

          d1=d2 : d1 ≡ d2
          d1=d2 = ≤-antisym (⋉-snd-invariant ad1≤ad2) d2≤d1

          e1=e2 : e1 ≡ e2
          e1=e2 = injectiver-on-related (≤-trans e1≤ε ε≤e2) $ ap snd p ∙ ap (_⊗ e2) (sym d1=d2)

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
