module Mugen.Cat.HierarchyTheory.McBride where

open import Cat.Diagram.Monad
open import Cat.Instances.Monads
open import Cat.Displayed.Total

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Order.Instances.LeftInvariantRightCentered
open import Mugen.Order.StrictOrder
open import Mugen.Cat.Instances.StrictOrders
open import Mugen.Cat.Instances.Displacements
open import Mugen.Cat.HierarchyTheory

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- The McBride Hierarchy Theory
-- Section 3.1
--
-- A construction of the McBride Monad for any displacement algebra '𝒟'

module _ {A : Poset o r} (𝒟 : Displacement-on A) where
  open Functor
  open _=>_
  open Strictly-monotone

  open Reasoning A
  open Displacement-on 𝒟

  McBride : Hierarchy-theory o (o ⊔ r)
  McBride = ht where
    M : Functor (Strict-orders o (o ⊔ r)) (Strict-orders o (o ⊔ r))
    M .F₀ L = L ⋉[ ε ] A
    M .F₁ f .hom (l , d) = (f .hom l) , d
    M .F₁ {L} {N} f .pres-≤[]-equal {l1 , d1} {l2 , d2} =
      let module N⋉A = Reasoning (N ⋉[ ε ] A) in
      ∥-∥-rec (N⋉A.≤[]-is-hlevel 0 $ Poset.Ob-is-set (L ⋉[ ε ] A) _ _) λ where
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
      let module L⋉A = Reasoning (L ⋉[ ε ] A) in
      ∥-∥-rec (L⋉A.≤[]-is-hlevel 0 $ Poset.Ob-is-set (M .F₀ (M .F₀ L)) _ _) lemma where
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

    ht : Hierarchy-theory o (o ⊔ r)
    ht .Monad.M = M
    ht .Monad.unit = unit
    ht .Monad.mult = mult
    ht .Monad.left-ident = ext λ α d → (refl , idl {d})
    ht .Monad.right-ident = ext λ α d → (refl , idr {d})
    ht .Monad.mult-assoc = ext λ α d1 d2 d3 → (refl , sym (associative {d1} {d2} {d3}))

--------------------------------------------------------------------------------
-- The Additional Functoriality of McBride Hierarchy Theory
--
-- The McBride monad is functorial in the parameter displacement.

module _ where
  open Functor
  open _=>_
  open Monad-hom
  open Total-hom
  open Strictly-monotone
  open Displacement-on
  open is-displacement-hom

  McBride-functor : Functor (Displacements o r) (Hierarchy-theories o (o ⊔ r))
  McBride-functor .F₀ (_ , 𝒟) = McBride 𝒟
  McBride-functor .F₁ σ .nat .η L .hom (l , d) = l , σ .hom # d
  McBride-functor .F₁ {A , 𝒟} {B , ℰ} σ .nat .η L .pres-≤[]-equal {l1 , d1} {l2 , d2} =
    let module A = Reasoning A
        module B = Reasoning B
        module σ = Strictly-monotone (σ .hom)
        module L⋉A = Reasoning (L ⋉[ 𝒟 .ε ] A)
        module L⋉B = Reasoning (L ⋉[ ℰ .ε ] B)
    in
    ∥-∥-rec (L⋉B.≤[]-is-hlevel 0 $ L⋉A.Ob-is-set _ _) λ where
      (biased l1=l2 d1≤d2) →
        inc (biased l1=l2 (σ.pres-≤ d1≤d2)) ,
        λ p → ap₂ _,_ (ap fst p) (σ.injective-on-related d1≤d2 $ ap snd p)
      (centred l1≤l2 d1≤ε ε≤d2) →
        inc (centred l1≤l2
          (B.≤+=→≤ (σ.pres-≤ d1≤ε) (σ .preserves .pres-ε))
          (B.=+≤→≤ (sym $ σ .preserves .pres-ε) (σ.pres-≤ ε≤d2))) ,
        λ p → ap₂ _,_ (ap fst p) (σ.injective-on-related (A.≤-trans d1≤ε ε≤d2) $ ap snd p)
  McBride-functor .F₁ σ .nat .is-natural L N f = trivial!
  McBride-functor .F₁ σ .pres-unit = ext λ L l → refl , σ .preserves .pres-ε
  McBride-functor .F₁ σ .pres-mult = ext λ L l d1 d2 → refl , σ .preserves .pres-⊗
  McBride-functor .F-id = trivial!
  McBride-functor .F-∘ f g = trivial!
