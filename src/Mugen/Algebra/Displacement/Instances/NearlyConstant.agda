-- vim: nowrap
module Mugen.Algebra.Displacement.Instances.NearlyConstant where

open import Mugen.Prelude
open import Mugen.Data.List
open import Mugen.Order.StrictOrder
open import Mugen.Order.Instances.Pointwise
open import Mugen.Order.Instances.BasedSupport
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Subalgebra
open import Mugen.Algebra.Displacement.Instances.IndexedProduct
open import Mugen.Algebra.OrderedMonoid

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- Nearly Constant Functions
-- Section 3.3.5
--
-- A "nearly constant function" is a function 'f : Nat → 𝒟'
-- that differs from some fixed 'base : 𝒟' for only
-- a finite set of 'n : Nat'
--
-- We represent these via prefix lists. IE: the function
--
-- > λ n → if n = 1 then 2 else if n = 3 then 1 else 5
--
-- will be represented as a pair (5, [5,2,5,3]). We will call the
-- first element of this pair "the base" of the function, and the
-- prefix list "the support".
--
-- However, there is a problem: there can be multiple representations
-- for the same function. The above function can also be represented
-- as (5, [5,2,5,3,5,5,5,5,5,5]), with trailing base elements.
-- To resolve this, we say that a list is compact relative
-- to some 'base : 𝒟' if it does not have any trailing base's.
-- We then only work with compact lists.

--------------------------------------------------------------------------------
-- Displacement

module _
  {A : Poset o r}
  ⦃ _ : Discrete ⌞ A ⌟ ⦄
  (𝒟 : Displacement-on A)
  where
  private
    module 𝒟 = Displacement-on 𝒟

    rep : represents-full-subdisplacement (Indexed-product Nat (λ _ → 𝒟)) (Based-support→Pointwise-is-full-subposet A)
    rep .represents-full-subdisplacement.ε = based-support-list (raw [] 𝒟.ε) (lift tt)
    rep .represents-full-subdisplacement._⊗_ = merge-with 𝒟._⊗_
    rep .represents-full-subdisplacement.pres-ε = refl
    rep .represents-full-subdisplacement.pres-⊗ {xs} {ys} = index-merge-with 𝒟._⊗_ xs ys
    module rep = represents-full-subdisplacement rep

  Nearly-constant : Displacement-on (Based-support A)
  Nearly-constant = rep.displacement-on

  Nearly-constant→Pointwise-is-full-subdisplacement :
    is-full-subdisplacement Nearly-constant (Indexed-product Nat (λ _ → 𝒟)) (Based-support→Pointwise A)
  Nearly-constant→Pointwise-is-full-subdisplacement = rep.has-is-full-subdisplacement

--------------------------------------------------------------------------------
-- Ordered Monoid

module _
  {A : Poset o r}
  ⦃ _ : Discrete ⌞ A ⌟ ⦄
  (𝒟 : Displacement-on A)
  (𝒟-ordered-monoid : has-ordered-monoid 𝒟)
  where
  private
    module 𝒟 = Displacement-on 𝒟
    module B = Reasoning (Based-support A)
    module N = Displacement-on (Nearly-constant 𝒟)
    module P = Reasoning (Pointwise Nat λ _ → A)
    module I-is-ordered-monoid =
      is-ordered-monoid (Indexed-product-has-ordered-monoid Nat (λ _ → 𝒟) λ _ → 𝒟-ordered-monoid)

    right-invariant : ∀ {xs ys zs} → xs B.≤ ys → (xs N.⊗ zs) B.≤ (ys N.⊗ zs)
    right-invariant {xs} {ys} {zs} xs≤ys =
      coe1→0 (λ i → index-merge-with 𝒟._⊗_ xs zs i P.≤ index-merge-with 𝒟._⊗_ ys zs i) $
      I-is-ordered-monoid.right-invariant xs≤ys

  Nearly-constant-has-ordered-monoid : has-ordered-monoid (Nearly-constant 𝒟)
  Nearly-constant-has-ordered-monoid =
    right-invariant→has-ordered-monoid (Nearly-constant 𝒟) λ {xs} {ys} {zs} →
    right-invariant {xs} {ys} {zs}
