module Mugen.Algebra.Displacement.Instances.Support where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Subalgebra
open import Mugen.Algebra.Displacement.Instances.IndexedProduct
open import Mugen.Algebra.Displacement.Instances.NearlyConstant
open import Mugen.Algebra.OrderedMonoid

open import Mugen.Order.StrictOrder
open import Mugen.Order.Instances.Pointwise
open import Mugen.Order.Instances.BasedSupport
open import Mugen.Order.Instances.Support renaming (Support to Support-poset)

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- Finitely Supported Functions
-- Section 3.3.5
--
-- Finitely supported functions over some displacement algebra '𝒟' are
-- functions 'f : Nat → 𝒟' that differ from the unit 'ε' in only a finite number of positions.
-- These are a special case of the Nearly Constant functions where the base is always ε
-- and are implemented as such.

module _
  {A : Poset o r}
  ⦃ _ : Discrete ⌞ A ⌟ ⦄
  (𝒟 : Displacement-on A)
  where
  private
    module NearlyConstant = Displacement-on (NearlyConstant 𝒟)
    module 𝒟 = Displacement-on 𝒟
    open SupportList

    rep : represents-full-subdisplacement (NearlyConstant 𝒟) (Support→BasedSupport-is-full-subposet A 𝒟.ε)
    rep .represents-full-subdisplacement.ε = support-list NearlyConstant.ε refl
    rep .represents-full-subdisplacement._⊗_ x y .based-support =
      NearlyConstant._⊗_ (x .based-support) (y .based-support)
    rep .represents-full-subdisplacement._⊗_ x y .base-is-ε =
      ap₂ 𝒟._⊗_ (x .base-is-ε) (y .base-is-ε) ∙ 𝒟.idl
    rep .represents-full-subdisplacement.pres-ε = refl
    rep .represents-full-subdisplacement.pres-⊗ = refl
    module rep = represents-full-subdisplacement rep

  Support : Displacement-on (Support-poset A 𝒟.ε)
  Support = rep.displacement-on

  Support→NearlyConstant-is-full-subdisplacement :
    is-full-subdisplacement Support (NearlyConstant 𝒟) (Support→BasedSupport A 𝒟.ε)
  Support→NearlyConstant-is-full-subdisplacement = rep.has-is-full-subdisplacement

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
    module N-is-ordered-monoid = is-ordered-monoid (NearlyConstant-has-ordered-monoid 𝒟 𝒟-ordered-monoid)
    open SupportList

  Support-has-ordered-monoid : has-ordered-monoid (Support 𝒟)
  Support-has-ordered-monoid = right-invariant→has-ordered-monoid (Support 𝒟) λ {xs} {ys} {zs} xs≤ys →
    N-is-ordered-monoid.right-invariant {xs .based-support} {ys .based-support} {zs .based-support} xs≤ys
