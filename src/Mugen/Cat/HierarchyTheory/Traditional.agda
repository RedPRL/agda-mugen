module Mugen.Cat.HierarchyTheory.Traditional where

open import Cat.Diagram.Monad

open import Order.Instances.Nat
open import Order.Instances.Coproduct

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Order.Instances.LeftInvariantRightCentered
open import Mugen.Order.StrictOrder
open import Mugen.Cat.Instances.StrictOrders
open import Mugen.Cat.HierarchyTheory

import Mugen.Order.Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- The Traditional Hierarchy Theory

module _ {o : Level} where
  open Strictly-monotone
  open Functor
  open _=>_

  Traditional : Hierarchy-theory o o
  Traditional = ht where
    M : Functor (Strict-orders o o) (Strict-orders o o)
    M .F₀ L = Nat-poset ⊎ᵖ L
    M .F₁ f .hom (inl n) = inl n
    M .F₁ f .hom (inr l) = inr (f .hom l)
    M .F₁ {L} {N} f .pres-≤[]-equal {inl n1} {inl n2} n1≤n2 = n1≤n2 , ap inl ⊙ inl-inj
    M .F₁ {L} {N} f .pres-≤[]-equal {inr l1} {inr l2} (lift l1≤l2) =
      lift {ℓ = lzero} (Strictly-monotone.pres-≤ f l1≤l2) ,
      λ eq → ap inr $ Strictly-monotone.injective-on-related f l1≤l2 $ inr-inj eq
    M .F-id = ext λ where
      (inl n) → refl
      (inr l) → refl
    M .F-∘ f g = ext λ where
      (inl n) → refl
      (inr l) → refl

    unit : Id => M
    unit .η L .hom l = inr l
    unit .η L .pres-≤[]-equal l1≤l2 = lift {ℓ = lzero} l1≤l2 , inr-inj
    unit .is-natural L L' f = ext λ _ → refl

    mult : M F∘ M => M
    mult .η L .hom (inl n) = inl n
    mult .η L .hom (inr l) = l
    mult .η L .pres-≤[]-equal {inl n1} {inl n2} n1≤n2        = n1≤n2 , ap inl ⊙ inl-inj
    mult .η L .pres-≤[]-equal {inr l1} {inr l2} (lift l1≤l2) = l1≤l2 , ap inr
    mult .is-natural L L' f = ext λ { (inl n) → {! refl !} ; (inr (inl l)) → refl ; (inr (inr _)) → {! refl !} }

    ht : Hierarchy-theory o o
    ht .Monad.M = M
    ht .Monad.unit = unit
    ht .Monad.mult = mult
    ht .Monad.left-ident = ext λ { (inl n) → refl ; (inr l) → refl }
    ht .Monad.right-ident = ext λ { (inl n) → refl ; (inr l) → refl }
    ht .Monad.mult-assoc = ext λ { (inl n) → refl ; (inr l) → refl }
