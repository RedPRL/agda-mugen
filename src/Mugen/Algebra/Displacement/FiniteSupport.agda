module Mugen.Algebra.Displacement.FiniteSupport where

open import 1Lab.Reflection.Record

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Coimage
open import Mugen.Algebra.Displacement.InfiniteProduct
open import Mugen.Algebra.Displacement.NearlyConstant
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

open import Mugen.Data.List


--------------------------------------------------------------------------------
-- Finitely Supported Functions
--
-- These are a special case of the Nearly Constant functions,
-- and are implemented as such.

module FinSupport {o r} (𝒟 : DisplacementAlgebra o r) (cmp : ∀ x y → Tri (DisplacementAlgebra._<_ 𝒟) x y) where
  private
    module 𝒟 = DisplacementAlgebra 𝒟
    open 𝒟 using (ε; _⊗_; _<_; _≤_)
    open NearlyConst 𝒟 cmp


  record FinSupportList : Type o where
    no-eta-equality
    field
      support : SupportList

    open SupportList support public

    field
      is-ε : base ≡ ε

  open FinSupportList

  fin-support-list-path : ∀ {xs ys} → xs .support ≡ ys .support → xs ≡ ys
  fin-support-list-path p i .support = p i
  fin-support-list-path {xs = xs} {ys = ys} p i .is-ε =
    is-set→squarep (λ _ _ → ⌞ 𝒟 ⌟-set) (ap SupportList.base p) (xs .is-ε) (ys .is-ε) refl i

  private unquoteDecl eqv = declare-record-iso eqv (quote FinSupportList)

  FinSupportList-is-set : is-set FinSupportList
  FinSupportList-is-set =
    is-hlevel≃ 2 (Iso→Equiv eqv e⁻¹) $
      Σ-is-hlevel 2 SupportList-is-set λ support →
        is-hlevel-suc 2 ⌞ 𝒟 ⌟-set (SupportList.base support) ε

  merge-fin : FinSupportList → FinSupportList → FinSupportList
  merge-fin xs ys .FinSupportList.support = merge (xs .support) (ys .support)
  merge-fin xs ys .FinSupportList.is-ε = ap₂ _⊗_ (xs .is-ε) (ys .is-ε) ∙ 𝒟.idl
  
  empty-fin : FinSupportList
  empty-fin .support = empty
  empty-fin .is-ε = refl

  --------------------------------------------------------------------------------
  -- Algebra

  merge-fin-is-magma : is-magma merge-fin
  merge-fin-is-magma .has-is-set = FinSupportList-is-set

  merge-fin-semigroup : is-semigroup merge-fin
  merge-fin-semigroup .has-is-magma = merge-fin-is-magma
  merge-fin-semigroup .associative {xs} {ys} {zs} = fin-support-list-path (merge-assoc (xs .support) (ys .support) (zs .support))

  merge-fin-monoid : is-monoid empty-fin merge-fin
  merge-fin-monoid .has-is-semigroup = merge-fin-semigroup
  merge-fin-monoid .idl {xs} = fin-support-list-path (merge-idl (xs .support))
  merge-fin-monoid .idr {xs} = fin-support-list-path (merge-idr (xs .support))

  --------------------------------------------------------------------------------
  -- Order

  _merge-fin<_ : FinSupportList → FinSupportList → Type (o ⊔ r)
  _merge-fin<_ xs ys = (xs .support) merge< (ys .support)

  merge-fin-strict-order : is-strict-order _merge-fin<_
  merge-fin-strict-order .is-strict-order.irrefl {xs} = merge-list<-irrefl (base xs) (list xs)
  merge-fin-strict-order .is-strict-order.trans {xs} {ys} {zs} = merge-list<-trans (base xs) (list xs) (base ys) (list ys) (base zs) (list zs)
  merge-fin-strict-order .is-strict-order.has-prop {xs} {ys} = merge-list<-is-prop (base xs) (list xs) (base ys) (list ys)

  --------------------------------------------------------------------------------
  -- Displacement Algebra

  merge-fin-is-displacement-algebra : is-displacement-algebra _merge-fin<_ empty-fin merge-fin
  merge-fin-is-displacement-algebra .is-displacement-algebra.has-monoid = merge-fin-monoid
  merge-fin-is-displacement-algebra .is-displacement-algebra.has-strict-order = merge-fin-strict-order
  merge-fin-is-displacement-algebra .is-displacement-algebra.left-invariant {xs} {ys} {zs} = merge-left-invariant (support xs) (support ys) (support zs)


module _ {o r} (𝒟 : DisplacementAlgebra o r) (cmp : ∀ x y → Tri (DisplacementAlgebra._<_ 𝒟) x y) where
  open FinSupport 𝒟 cmp

  FiniteSupport : DisplacementAlgebra o (o ⊔ r)
  ⌞ FiniteSupport ⌟ = FinSupportList
  FiniteSupport .structure .DisplacementAlgebra-on._<_ = _merge-fin<_
  FiniteSupport .structure .DisplacementAlgebra-on.ε = empty-fin
  FiniteSupport .structure .DisplacementAlgebra-on._⊗_ = merge-fin
  FiniteSupport .structure .DisplacementAlgebra-on.has-displacement-algebra = merge-fin-is-displacement-algebra
  ⌞ FiniteSupport ⌟-set = FinSupportList-is-set

--------------------------------------------------------------------------------
-- Subalgebra Structure

module _ {o r} {𝒟 : DisplacementAlgebra o r} (cmp : ∀ x y → Tri (DisplacementAlgebra._<_ 𝒟) x y) where
  open FinSupport 𝒟 cmp
  open FinSupportList
  
  FinSupport⊆NearlyConstant : is-displacement-subalgebra (FiniteSupport 𝒟 cmp) (NearlyConstant 𝒟 cmp)
  FinSupport⊆NearlyConstant .is-displacement-subalgebra.into ._⟨$⟩_ = support
  FinSupport⊆NearlyConstant .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-ε = refl
  FinSupport⊆NearlyConstant .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-⊗ _ _ = refl
  FinSupport⊆NearlyConstant .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.strictly-mono xs<ys = xs<ys
  FinSupport⊆NearlyConstant .is-displacement-subalgebra.inj = fin-support-list-path

  FinSupport⊆InfProd : is-displacement-subalgebra (FiniteSupport 𝒟 cmp) (InfProd 𝒟)
  FinSupport⊆InfProd = is-displacement-subalgebra-trans FinSupport⊆NearlyConstant (NearlyConstant⊆InfProd cmp)

--------------------------------------------------------------------------------
-- Ordered Monoid

module _ {o r} {𝒟 : DisplacementAlgebra o r} (𝒟-ordered-monoid : has-ordered-monoid 𝒟) (cmp : ∀ x y → Tri (DisplacementAlgebra._<_ 𝒟) x y) where
  open FinSupport 𝒟 cmp
  open FinSupportList
  open NearlyConst 𝒟 cmp
  open is-ordered-monoid 𝒟-ordered-monoid

  fin-support-ordered-monoid : has-ordered-monoid (FiniteSupport 𝒟 cmp)
  fin-support-ordered-monoid = right-invariant→has-ordered-monoid (FiniteSupport 𝒟 cmp) λ {xs} {ys} {zs} xs≤ys →
    ⊎-mapl fin-support-list-path (merge-right-invariant 𝒟-ordered-monoid cmp (support xs) (support ys) (support zs) (⊎-mapl (ap support) xs≤ys))
