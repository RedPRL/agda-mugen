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
-- Finitely supported functions over some displacement algebra '𝒟' are
-- functions 'f : Nat → 𝒟' that differ from 'const ε' in only a finite number of positions.
-- These are a special case of the Nearly Constant functions where the base is always ε
-- and are implemented as such.

module FinSupport {o r} (𝒟 : Displacement-algebra o r) (cmp : ∀ x y → Tri (Displacement-algebra._<_ 𝒟) x y) where
  private
    module 𝒟 = Displacement-algebra 𝒟
    open 𝒟 using (ε; _⊗_; _<_; _≤_)
  open NearlyConst 𝒟 cmp public

  --------------------------------------------------------------------------------
  -- Finite Support Lists
  --
  -- As noted above, these are defined to be SupportLists of nearly constant functions,
  -- with the constraint that the base is 'ε'.

  record FinSupportList : Type o where
    no-eta-equality
    field
      support : SupportList

    open SupportList support public

    field
      is-ε : base ≡ ε

  open FinSupportList

  -- Paths between finitely supportd functions are purely determined by their elements.
  fin-support-list-path : ∀ {xs ys} → xs .support ≡ ys .support → xs ≡ ys
  fin-support-list-path p i .support = p i
  fin-support-list-path {xs = xs} {ys = ys} p i .is-ε =
    is-set→squarep (λ _ _ → 𝒟.has-is-set) (ap SupportList.base p) (xs .is-ε) (ys .is-ε) refl i

  private unquoteDecl eqv = declare-record-iso eqv (quote FinSupportList)

  FinSupportList-is-set : is-set FinSupportList
  FinSupportList-is-set =
    is-hlevel≃ 2 (Iso→Equiv eqv) $
      Σ-is-hlevel 2 SupportList-is-set λ support →
        is-hlevel-suc 2 𝒟.has-is-set (SupportList.base support) ε

  merge-fin : FinSupportList → FinSupportList → FinSupportList
  merge-fin xs ys .FinSupportList.support = merge (xs .support) (ys .support)
  merge-fin xs ys .FinSupportList.is-ε = ap₂ _⊗_ (xs .is-ε) (ys .is-ε) ∙ 𝒟.idl
  
  empty-fin : FinSupportList
  empty-fin .support = empty
  empty-fin .is-ε = refl

  --------------------------------------------------------------------------------
  -- Algebra


  --------------------------------------------------------------------------------
  -- Order

  _merge-fin<_ : FinSupportList → FinSupportList → Type (o ⊔ r)
  _merge-fin<_ xs ys = (xs .support) merge< (ys .support)


--------------------------------------------------------------------------------
-- Displacement Algebra

module _ {o r} (𝒟 : Displacement-algebra o r) (cmp : ∀ x y → Tri (Displacement-algebra._<_ 𝒟) x y) where
  open FinSupport 𝒟 cmp
  open FinSupportList

  FiniteSupport : Displacement-algebra o (o ⊔ r)
  FiniteSupport = to-displacement-algebra mk where
    mk-strict : make-strict-order (o ⊔ r) FinSupportList
    mk-strict .make-strict-order._<_ = _merge-fin<_
    mk-strict .make-strict-order.<-irrefl {xs} =
      merge-list<-irrefl (base xs) (list xs)
    mk-strict .make-strict-order.<-trans {xs} {ys} {zs} =
      merge-list<-trans (base xs) (list xs) (base ys) (list ys) (base zs) (list zs)
    mk-strict .make-strict-order.<-thin {xs} {ys} =
      merge-list<-is-prop (base xs) (list xs) (base ys) (list ys)
    mk-strict .make-strict-order.has-is-set = FinSupportList-is-set

    mk : make-displacement-algebra (to-strict-order mk-strict)
    mk .make-displacement-algebra.ε = empty-fin
    mk .make-displacement-algebra._⊗_ = merge-fin
    mk .make-displacement-algebra.idl {xs} =
      fin-support-list-path (merge-idl (xs .support))
    mk .make-displacement-algebra.idr {xs} =
      fin-support-list-path (merge-idr (xs .support))
    mk .make-displacement-algebra.associative {xs} {ys} {zs} =
      fin-support-list-path (merge-assoc (xs .support) (ys .support) (zs .support))
    mk .make-displacement-algebra.left-invariant {xs} {ys} {zs} =
      merge-left-invariant (support xs) (support ys) (support zs)

--------------------------------------------------------------------------------
-- Subalgebra Structure

module _
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (cmp : ∀ x y → Tri 𝒟._<_ x y)
  where
  open FinSupport 𝒟 cmp
  open FinSupportList
  
  FinSupport⊆NearlyConstant : is-displacement-subalgebra (FiniteSupport 𝒟 cmp) (NearlyConstant 𝒟 cmp)
  FinSupport⊆NearlyConstant = to-displacement-subalgebra mk where
    mk : make-displacement-subalgebra _ _
    mk .make-displacement-subalgebra.into = support
    mk .make-displacement-subalgebra.pres-ε = refl
    mk .make-displacement-subalgebra.pres-⊗ _ _ = refl
    mk .make-displacement-subalgebra.strictly-mono _ _ xs<ys = xs<ys
    mk .make-displacement-subalgebra.inj = fin-support-list-path

  FinSupport⊆InfProd : is-displacement-subalgebra (FiniteSupport 𝒟 cmp) (InfProd 𝒟)
  FinSupport⊆InfProd =
    is-displacement-subalgebra-trans
      FinSupport⊆NearlyConstant
      (NearlyConstant⊆InfProd cmp)

--------------------------------------------------------------------------------
-- Ordered Monoid

module _
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (𝒟-ordered-monoid : has-ordered-monoid 𝒟)
  (cmp : ∀ x y → Tri 𝒟._<_ x y)
  where
  open FinSupport 𝒟 cmp
  open FinSupportList
  open NearlyConst 𝒟 cmp
  open is-ordered-monoid 𝒟-ordered-monoid

  fin-support-ordered-monoid : has-ordered-monoid (FiniteSupport 𝒟 cmp)
  fin-support-ordered-monoid = right-invariant→has-ordered-monoid (FiniteSupport 𝒟 cmp) λ {xs} {ys} {zs} xs≤ys →
    ⊎-mapl fin-support-list-path (merge-right-invariant 𝒟-ordered-monoid cmp (support xs) (support ys) (support zs) (⊎-mapl (ap support) xs≤ys))
