module Mugen.Cat.HierarchyTheory.McBride where

open import Cat.Diagram.Monad
open import Cat.Instances.Monads
open import Cat.Displayed.Total

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
import Mugen.Order.Instances.LeftInvariantRightCentred as LeftInvariantRightCentred
open import Mugen.Order.StrictOrder
open import Mugen.Cat.Instances.StrictOrders
open import Mugen.Cat.Instances.Displacements
open import Mugen.Cat.HierarchyTheory

import Mugen.Order.Reasoning as Reasoning

private variable
  o r : Level

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

  private
    module ⋉A (L : Poset o (o ⊔ r)) = LeftInvariantRightCentred L A ε

  McBride : Hierarchy-theory-on _
  McBride = ht where
    M : Functor (Strict-orders o (o ⊔ r)) (Strict-orders o (o ⊔ r))
    M .F₀ L = ⋉A.poset L
    M .F₁ f .hom (l , d) = (f .hom l) , d
    M .F₁ {L} {N} f .pres-≤[]-equal {l1 , d1} {l2 , d2} =
      let module N⋉A = Reasoning (⋉A.poset N) in
      ∥-∥-rec (N⋉A.≤[]-is-hlevel 0 $ Poset.Ob-is-set (⋉A.poset L) _ _) λ where
        (⋉A.biased l1=l2 d1≤d2) → inc (⋉A.biased (ap (f .hom) l1=l2) d1≤d2) , λ p → ap₂ _,_ l1=l2 (ap snd p)
        (⋉A.centred l1≤l2 d1≤ε ε≤d2) → inc (⋉A.centred (pres-≤ f l1≤l2) d1≤ε ε≤d2) , λ p →
          ap₂ _,_ (injective-on-related f l1≤l2 (ap fst p)) (ap snd p)
    M .F-id = trivial!
    M .F-∘ f g = trivial!

    unit : Id => M
    unit .η L .hom l = l , ε
    unit .η L .pres-≤[]-equal l1≤l2 = inc (⋉A.centred l1≤l2 ≤-refl ≤-refl) , ap fst
    unit .is-natural L L' f = trivial!

    mult : M F∘ M => M
    mult .η L .hom ((l , x) , y) = l , (x ⊗ y)
    mult .η L .pres-≤[]-equal {(a1 , d1) , e1} {(a2 , d2) , e2} =
      let module L⋉A = Reasoning (⋉A.poset L) in
      ∥-∥-rec (L⋉A.≤[]-is-hlevel 0 $ Poset.Ob-is-set (M .F₀ (M .F₀ L)) _ _) lemma where
        lemma : ⋉A._≤'_ (M .F₀ L) ((a1 , d1) , e1) ((a2 , d2) , e2)
          → ⋉A._≤_ L (a1 , (d1 ⊗ e1)) (a2 , (d2 ⊗ e2))
          × ((a1 , (d1 ⊗ e1)) ≡ (a2 , (d2 ⊗ e2)) → ((a1 , d1) , e1) ≡ ((a2 , d2) , e2))
        lemma (⋉A.biased ad1=ad2 e1≤e2) =
          inc (⋉A.biased (ap fst ad1=ad2) (=+≤→≤ (ap (_⊗ e1) (ap snd ad1=ad2)) (left-invariant e1≤e2))) ,
          λ p i → ad1=ad2 i , injectiver-on-related e1≤e2 (ap snd p ∙ ap (_⊗ e2) (sym $ ap snd ad1=ad2)) i
        lemma (⋉A.centred ad1≤ad2 e1≤ε ε≤e2) = ∥-∥-map lemma₂ ad1≤ad2 , lemma₃ where
          d1⊗e1≤d1 : (d1 ⊗ e1) ≤ d1
          d1⊗e1≤d1 = ≤+=→≤ (left-invariant e1≤ε) idr

          d2≤d2⊗e2 : d2 ≤ (d2 ⊗ e2)
          d2≤d2⊗e2 = =+≤→≤ (sym idr) (left-invariant ε≤e2)

          lemma₂ : ⋉A._≤'_ L (a1 , d1) (a2 , d2)
            → ⋉A._≤'_ L (a1 , (d1 ⊗ e1)) (a2 , (d2 ⊗ e2))
          lemma₂ (⋉A.biased a1=a2 d1≤d2) = ⋉A.biased a1=a2 (≤-trans d1⊗e1≤d1 (≤-trans d1≤d2 d2≤d2⊗e2))
          lemma₂ (⋉A.centred a1≤a2 d1≤ε ε≤d2) = ⋉A.centred a1≤a2 (≤-trans d1⊗e1≤d1 d1≤ε) (≤-trans ε≤d2 d2≤d2⊗e2)

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
            d1=d2 = ≤-antisym (⋉A.≤-snd-invariant _ ad1≤ad2) d2≤d1

            e1=e2 : e1 ≡ e2
            e1=e2 = injectiver-on-related (≤-trans e1≤ε ε≤e2) $ ap snd p ∙ ap (_⊗ e2) (sym d1=d2)
    mult .is-natural L L' f = trivial!

    ht : Hierarchy-theory-on M
    ht .Monad-on.unit = unit
    ht .Monad-on.mult = mult
    ht .Monad-on.μ-unitl = ext λ α d → Σ-path refl (transport-refl _ ∙ idr {d})
    ht .Monad-on.μ-unitr = ext λ α d → Σ-path refl (transport-refl _ ∙ idl {d})
    ht .Monad-on.μ-assoc = ext λ α d1 d2 d3 → Σ-path refl (transport-refl _ ∙ sym (associative {d1} {d2} {d3}))

--------------------------------------------------------------------------------
-- The Additional Functoriality of McBride Hierarchy Theory
--
-- The McBride monad is functorial in the parameter displacement.

module _ where
  open Functor
  open _=>_
  open is-monad-hom
  open ∫Hom
  open Strictly-monotone
  open Displacement-on
  open is-displacement-hom

  McBride-functor : Functor (Displacements o r) (Hierarchy-theories o (o ⊔ r))
  McBride-functor .F₀ (_ , 𝒟) = _ , McBride 𝒟
  McBride-functor .F₁ σ .fst .η L .hom (l , d) = l , σ · d
  McBride-functor .F₁ {A , 𝒟} {B , ℰ} σ .fst .η L .pres-≤[]-equal {l1 , d1} {l2 , d2} =
    let module A = Reasoning A
        module B = Reasoning B
        module σ₀ = Strictly-monotone (σ .fst)
        module σ₁ = is-displacement-hom (σ .snd)
        module ⋉A (L : Poset _ _) = LeftInvariantRightCentred L A (𝒟 .ε)
        module ⋉B (L : Poset _ _) = LeftInvariantRightCentred L B (ℰ .ε)
        module ⋉A-poset (L : Poset _ _) = Reasoning (⋉A.poset L)
        module ⋉B-poset (L : Poset _ _) = Reasoning (⋉B.poset L)
    in
    ∥-∥-rec (⋉B-poset.≤[]-is-hlevel L 0 $ ⋉A-poset.Ob-is-set L _ _) λ where
      (⋉A.biased l1=l2 d1≤d2) →
        inc (⋉B.biased l1=l2 (σ₀.pres-≤ d1≤d2)) ,
        λ p → ap₂ _,_ (ap fst p) (σ₀.injective-on-related d1≤d2 $ ap snd p)
      (⋉A.centred l1≤l2 d1≤ε ε≤d2) →
        inc (⋉B.centred l1≤l2
          (B.≤+=→≤ (σ₀.pres-≤ d1≤ε) (σ₁.pres-ε))
          (B.=+≤→≤ (sym $ σ₁.pres-ε) (σ₀.pres-≤ ε≤d2))) ,
        λ p → ap₂ _,_ (ap fst p) (σ₀.injective-on-related (A.≤-trans d1≤ε ε≤d2) $ ap snd p)
  McBride-functor .F₁ σ .fst .is-natural L N f = trivial!
  McBride-functor .F₁ σ .snd .pres-unit = ext λ L l → Σ-path refl (transport-refl _ ∙ σ .snd .pres-ε)
  McBride-functor .F₁ σ .snd .pres-mult = ext λ L l d1 d2 → Σ-path refl (transport-refl _ ∙ σ .snd .pres-⊗)
  McBride-functor .F-id =
    ∫Hom-path _
      (Nat-path λ L → Strictly-monotone-path _ _ $ funext λ where
        (l , d) → refl)
      prop!
  McBride-functor .F-∘ f g =
    ∫Hom-path _
      (Nat-path λ L → Strictly-monotone-path _ _ $ funext λ where
        (l , d) → refl)
      prop!
