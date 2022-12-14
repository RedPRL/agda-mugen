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
-- Section 3.3.5
--
-- Finitely supported functions over some displacement algebra 'π' are
-- functions 'f : Nat β π' that differ from 'const Ξ΅' in only a finite number of positions.
-- These are a special case of the Nearly Constant functions where the base is always Ξ΅
-- and are implemented as such.

module FinSupport {o r} (π : DisplacementAlgebra o r) (cmp : β x y β Tri (DisplacementAlgebra._<_ π) x y) where
  private
    module π = DisplacementAlgebra π
    open π using (Ξ΅; _β_; _<_; _β€_)
    open NearlyConst π cmp

  --------------------------------------------------------------------------------
  -- Finite Support Lists
  --
  -- As noted above, these are defined to be SupportLists of nearly constant functions,
  -- with the constraint that the base is 'Ξ΅'.

  record FinSupportList : Type o where
    no-eta-equality
    field
      support : SupportList

    open SupportList support public

    field
      is-Ξ΅ : base β‘ Ξ΅

  open FinSupportList

  -- Paths between finitely supportd functions are purely determined by their elements.
  fin-support-list-path : β {xs ys} β xs .support β‘ ys .support β xs β‘ ys
  fin-support-list-path p i .support = p i
  fin-support-list-path {xs = xs} {ys = ys} p i .is-Ξ΅ =
    is-setβsquarep (Ξ» _ _ β β π β-set) (ap SupportList.base p) (xs .is-Ξ΅) (ys .is-Ξ΅) refl i

  private unquoteDecl eqv = declare-record-iso eqv (quote FinSupportList)

  FinSupportList-is-set : is-set FinSupportList
  FinSupportList-is-set =
    is-hlevelβ 2 (IsoβEquiv eqv eβ»ΒΉ) $
      Ξ£-is-hlevel 2 SupportList-is-set Ξ» support β
        is-hlevel-suc 2 β π β-set (SupportList.base support) Ξ΅

  merge-fin : FinSupportList β FinSupportList β FinSupportList
  merge-fin xs ys .FinSupportList.support = merge (xs .support) (ys .support)
  merge-fin xs ys .FinSupportList.is-Ξ΅ = apβ _β_ (xs .is-Ξ΅) (ys .is-Ξ΅) β π.idl
  
  empty-fin : FinSupportList
  empty-fin .support = empty
  empty-fin .is-Ξ΅ = refl

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

  _merge-fin<_ : FinSupportList β FinSupportList β Type (o β r)
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


module _ {o r} (π : DisplacementAlgebra o r) (cmp : β x y β Tri (DisplacementAlgebra._<_ π) x y) where
  open FinSupport π cmp

  FiniteSupport : DisplacementAlgebra o (o β r)
  β FiniteSupport β = FinSupportList
  FiniteSupport .structure .DisplacementAlgebra-on._<_ = _merge-fin<_
  FiniteSupport .structure .DisplacementAlgebra-on.Ξ΅ = empty-fin
  FiniteSupport .structure .DisplacementAlgebra-on._β_ = merge-fin
  FiniteSupport .structure .DisplacementAlgebra-on.has-displacement-algebra = merge-fin-is-displacement-algebra
  β FiniteSupport β-set = FinSupportList-is-set

--------------------------------------------------------------------------------
-- Subalgebra Structure

module _ {o r} {π : DisplacementAlgebra o r} (cmp : β x y β Tri (DisplacementAlgebra._<_ π) x y) where
  open FinSupport π cmp
  open FinSupportList
  
  FinSupportβNearlyConstant : is-displacement-subalgebra (FiniteSupport π cmp) (NearlyConstant π cmp)
  FinSupportβNearlyConstant .is-displacement-subalgebra.into ._β¨$β©_ = support
  FinSupportβNearlyConstant .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-Ξ΅ = refl
  FinSupportβNearlyConstant .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-β _ _ = refl
  FinSupportβNearlyConstant .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.strictly-mono xs<ys = xs<ys
  FinSupportβNearlyConstant .is-displacement-subalgebra.inj = fin-support-list-path

  FinSupportβInfProd : is-displacement-subalgebra (FiniteSupport π cmp) (InfProd π)
  FinSupportβInfProd = is-displacement-subalgebra-trans FinSupportβNearlyConstant (NearlyConstantβInfProd cmp)

--------------------------------------------------------------------------------
-- Ordered Monoid

module _ {o r} {π : DisplacementAlgebra o r} (π-ordered-monoid : has-ordered-monoid π) (cmp : β x y β Tri (DisplacementAlgebra._<_ π) x y) where
  open FinSupport π cmp
  open FinSupportList
  open NearlyConst π cmp
  open is-ordered-monoid π-ordered-monoid

  fin-support-ordered-monoid : has-ordered-monoid (FiniteSupport π cmp)
  fin-support-ordered-monoid = right-invariantβhas-ordered-monoid (FiniteSupport π cmp) Ξ» {xs} {ys} {zs} xsβ€ys β
    β-mapl fin-support-list-path (merge-right-invariant π-ordered-monoid cmp (support xs) (support ys) (support zs) (β-mapl (ap support) xsβ€ys))
