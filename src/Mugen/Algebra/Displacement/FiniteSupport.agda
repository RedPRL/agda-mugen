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
    open 𝒟 using (ε; _⊗_)
    module 𝒩 = NearlyConst 𝒟 cmp

  --------------------------------------------------------------------------------
  -- Finite Support Lists
  --
  -- As noted above, these are defined to be SupportLists of nearly constant functions,
  -- with the constraint that the base is 'ε'.

  record FinSupportList : Type o where
    no-eta-equality
    field
      support : 𝒩.SupportList

    open 𝒩.SupportList support public

    field
      is-ε : base ≡ ε

  open FinSupportList

  -- Paths between finitely supportd functions are purely determined by their elements.
  fin-support-list-path : ∀ {xs ys} → xs .support ≡ ys .support → xs ≡ ys
  fin-support-list-path p i .support = p i
  fin-support-list-path {xs = xs} {ys = ys} p i .is-ε =
    is-set→squarep (λ _ _ → 𝒟.has-is-set) (ap 𝒩.SupportList.base p) (xs .is-ε) (ys .is-ε) refl i

  private unquoteDecl eqv = declare-record-iso eqv (quote FinSupportList)

  FinSupportList-is-set : is-set FinSupportList
  FinSupportList-is-set =
    is-hlevel≃ 2 (Iso→Equiv eqv) $
      Σ-is-hlevel 2 𝒩.SupportList-is-set λ support →
        is-hlevel-suc 2 𝒟.has-is-set (𝒩.SupportList.base support) ε

  merge-fin : FinSupportList → FinSupportList → FinSupportList
  merge-fin xs ys .FinSupportList.support = 𝒩.merge (xs .support) (ys .support)
  merge-fin xs ys .FinSupportList.is-ε =
    𝒩.base-merge (xs .support) (ys .support) ∙ ap₂ _⊗_ (xs .is-ε) (ys .is-ε) ∙ 𝒟.idl

  empty-fin : FinSupportList
  empty-fin .support = 𝒩.empty
  empty-fin .is-ε = refl

  --------------------------------------------------------------------------------
  -- Order

  _<_ : FinSupportList → FinSupportList → Type (o ⊔ r)
  _<_ xs ys = (xs .support) 𝒩.< (ys .support)

--------------------------------------------------------------------------------
-- Displacement Algebra

module _ {o r} (𝒟 : Displacement-algebra o r) (cmp : ∀ x y → Tri (Displacement-algebra._<_ 𝒟) x y) where
  open FinSupport 𝒟 cmp
  open FinSupportList
  private module 𝒩𝒟 = Displacement-algebra (NearlyConstant 𝒟 cmp)

  FiniteSupport : Displacement-algebra o (o ⊔ r)
  FiniteSupport = to-displacement-algebra mk where
    mk-strict : make-strict-order (o ⊔ r) FinSupportList
    mk-strict .make-strict-order._<_ = _<_
    mk-strict .make-strict-order.<-irrefl {xs} =
      𝒩𝒟.<-irrefl {xs .support}
    mk-strict .make-strict-order.<-trans {xs} {ys} {zs} =
      𝒩𝒟.<-trans {xs .support} {ys .support} {zs .support}
    mk-strict .make-strict-order.<-thin {xs} {ys} =
      𝒩𝒟.<-thin {xs .support} {ys .support}
    mk-strict .make-strict-order.has-is-set = FinSupportList-is-set

    mk : make-displacement-algebra (to-strict-order mk-strict)
    mk .make-displacement-algebra.ε = empty-fin
    mk .make-displacement-algebra._⊗_ = merge-fin
    mk .make-displacement-algebra.idl = fin-support-list-path 𝒩𝒟.idl
    mk .make-displacement-algebra.idr = fin-support-list-path 𝒩𝒟.idr
    mk .make-displacement-algebra.associative = fin-support-list-path 𝒩𝒟.associative
    mk .make-displacement-algebra.left-invariant {xs} {ys} {zs} =
      𝒩𝒟.left-invariant {xs .support} {ys .support} {zs .support}

--------------------------------------------------------------------------------
-- Subalgebra Structure

module _
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (cmp : ∀ x y → Tri 𝒟._<_ x y)
  where
  open FinSupport 𝒟 cmp

  FinSupport⊆NearlyConstant : is-displacement-subalgebra (FiniteSupport 𝒟 cmp) (NearlyConstant 𝒟 cmp)
  FinSupport⊆NearlyConstant = to-displacement-subalgebra mk where
    mk : make-displacement-subalgebra _ _
    mk .make-displacement-subalgebra.into = FinSupportList.support
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

  fin-support-ordered-monoid : has-ordered-monoid (FiniteSupport 𝒟 cmp)
  fin-support-ordered-monoid = right-invariant→has-ordered-monoid (FiniteSupport 𝒟 cmp) λ {xs} {ys} {zs} xs≤ys →
    ⊎-mapl fin-support-list-path (≤-right-invariant 𝒟-ordered-monoid cmp (⊎-mapl (ap FinSupportList.support) xs≤ys))

--------------------------------------------------------------------------------
-- Extensionality based on 'finite-support-list' and eventually 'index-inj'
-- from NearlyConst.

module _ {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  {cmp : ∀ x y → Tri 𝒟._<_ x y}
  where
  module 𝒩 = NearlyConst 𝒟 cmp
  open FinSupport 𝒟 cmp
  open FinSupportList

  Extensional-FinSupportList : ∀ {ℓr} ⦃ s : Extensional 𝒩.SupportList ℓr ⦄ → Extensional FinSupportList ℓr
  Extensional-FinSupportList ⦃ s ⦄ .Pathᵉ xs ys = s .Pathᵉ (xs .support) (ys .support)
  Extensional-FinSupportList ⦃ s ⦄ .reflᵉ xs = s .reflᵉ (xs .support)
  Extensional-FinSupportList ⦃ s ⦄ .idsᵉ .to-path p = fin-support-list-path $ s .idsᵉ .to-path p
  Extensional-FinSupportList ⦃ s ⦄ .idsᵉ .to-path-over p =
    is-prop→pathp (λ _ → identity-system-hlevel 1 (s .idsᵉ) 𝒩.SupportList-is-set) _ p

  instance
    extensionality-fin-support-list : ∀ {ℓr} ⦃ s : Extensional ⌞ 𝒟 ⌟ ℓr ⦄ → Extensionality FinSupportList
    extensionality-fin-support-list = record { lemma = quote Extensional-FinSupportList }
