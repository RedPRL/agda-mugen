module Mugen.Algebra.Displacement.FiniteSupport where

open import 1Lab.Reflection.Record

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Order.Poset
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.IndexedProduct
open import Mugen.Algebra.Displacement.NearlyConstant
open import Mugen.Algebra.OrderedMonoid


--------------------------------------------------------------------------------
-- Finitely Supported Functions
-- Section 3.3.5
--
-- Finitely supported functions over some displacement algebra '𝒟' are
-- functions 'f : Nat → 𝒟' that differ from the unit 'ε' in only a finite number of positions.
-- These are a special case of the Nearly Constant functions where the base is always ε
-- and are implemented as such.

module FinSupport {o r} (𝒟 : Displacement-algebra o r) (_≡?_ : Discrete ⌞ 𝒟 ⌟) where
  private
    module 𝒟 = Displacement-algebra 𝒟
    open NearlyConst 𝒟 _≡?_

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
      is-ε : base ≡ 𝒟.ε

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
        is-hlevel-suc 2 𝒟.has-is-set (SupportList.base support) 𝒟.ε

  merge-fin : FinSupportList → FinSupportList → FinSupportList
  merge-fin xs ys .FinSupportList.support = merge (xs .support) (ys .support)
  merge-fin xs ys .FinSupportList.is-ε =
    base-merge (xs .support) (ys .support) ∙ ap₂ 𝒟._⊗_ (xs .is-ε) (ys .is-ε) ∙ 𝒟.idl

  empty-fin : FinSupportList
  empty-fin .support = empty
  empty-fin .is-ε = refl

  --------------------------------------------------------------------------------
  -- Order

  _≤_ : FinSupportList → FinSupportList → Type r
  _≤_ xs ys = (xs .support) supp≤ (ys .support)

--------------------------------------------------------------------------------
-- Displacement Algebra

module _ {o r} (𝒟 : Displacement-algebra o r) (_≡?_ : Discrete ⌞ 𝒟 ⌟) where
  open FinSupport 𝒟 _≡?_
  open FinSupportList
  private module 𝒩 = Displacement-algebra (NearlyConstant 𝒟 _≡?_)

  FiniteSupport : Displacement-algebra o r
  FiniteSupport = to-displacement-algebra mk where
    mk-strict : make-poset r FinSupportList
    mk-strict .make-poset._≤_ = _≤_
    mk-strict .make-poset.≤-refl {xs} =
      𝒩.≤-refl {xs .support}
    mk-strict .make-poset.≤-thin {xs} {ys} =
      𝒩.≤-thin {xs .support} {ys .support}
    mk-strict .make-poset.≤-trans {xs} {ys} {zs} =
      𝒩.≤-trans {xs .support} {ys .support} {zs .support}
    mk-strict .make-poset.≤-antisym {xs} {ys} p q =
      fin-support-list-path $ 𝒩.≤-antisym {xs .support} {ys .support} p q

    mk : make-displacement-algebra (to-poset mk-strict)
    mk .make-displacement-algebra.ε = empty-fin
    mk .make-displacement-algebra._⊗_ = merge-fin
    mk .make-displacement-algebra.idl = fin-support-list-path 𝒩.idl
    mk .make-displacement-algebra.idr = fin-support-list-path 𝒩.idr
    mk .make-displacement-algebra.associative = fin-support-list-path 𝒩.associative
    mk .make-displacement-algebra.≤-left-invariant {xs} {ys} {zs} =
      𝒩.≤-left-invariant {xs .support} {ys .support} {zs .support}
    mk .make-displacement-algebra.injr-on-≤ {xs} {ys} p q =
      fin-support-list-path $ 𝒩.injr-on-≤ {xs .support} {ys .support} p (ap support q)

--------------------------------------------------------------------------------
-- Subalgebra Structure

module _
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (_≡?_ : Discrete ⌞ 𝒟 ⌟)
  where
  open FinSupport 𝒟 _≡?_

  FinSupport⊆NearlyConstant : is-displacement-subalgebra (FiniteSupport 𝒟 _≡?_) (NearlyConstant 𝒟 _≡?_)
  FinSupport⊆NearlyConstant = to-displacement-subalgebra mk where
    mk : make-displacement-subalgebra _ _
    mk .make-displacement-subalgebra.into = FinSupportList.support
    mk .make-displacement-subalgebra.pres-ε = refl
    mk .make-displacement-subalgebra.pres-⊗ _ _ = refl
    mk .make-displacement-subalgebra.mono _ _ xs<ys = xs<ys
    mk .make-displacement-subalgebra.inj = fin-support-list-path

  FinSupport⊆IndProd : is-displacement-subalgebra (FiniteSupport 𝒟 _≡?_) (IndProd Nat λ _ → 𝒟)
  FinSupport⊆IndProd =
    is-displacement-subalgebra-trans
      FinSupport⊆NearlyConstant
      (NearlyConstant⊆IndProd _≡?_)

--------------------------------------------------------------------------------
-- Ordered Monoid

module _
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (𝒟-ordered-monoid : has-ordered-monoid 𝒟)
  (_≡?_ : Discrete ⌞ 𝒟 ⌟)
  where
  open FinSupport 𝒟 _≡?_
  open FinSupportList

  fin-support-ordered-monoid : has-ordered-monoid (FiniteSupport 𝒟 _≡?_)
  fin-support-ordered-monoid = right-invariant→has-ordered-monoid (FiniteSupport 𝒟 _≡?_) λ {xs} {ys} {zs} xs≤ys →
    supp≤-right-invariant {𝒟 = 𝒟} 𝒟-ordered-monoid _≡?_ {xs .support} {ys .support} {zs .support} xs≤ys

--------------------------------------------------------------------------------
-- Extensionality based on 'finite-support-list' and eventually 'index-inj'
-- from NearlyConst.

module _ {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  {_≡?_ : Discrete ⌞ 𝒟 ⌟}
  where
  open NearlyConst 𝒟 _≡?_
  open FinSupport 𝒟 _≡?_
  open FinSupportList

  Extensional-FinSupportList : ∀ {ℓr} ⦃ s : Extensional SupportList ℓr ⦄ → Extensional FinSupportList ℓr
  Extensional-FinSupportList ⦃ s ⦄ .Pathᵉ xs ys = s .Pathᵉ (xs .support) (ys .support)
  Extensional-FinSupportList ⦃ s ⦄ .reflᵉ xs = s .reflᵉ (xs .support)
  Extensional-FinSupportList ⦃ s ⦄ .idsᵉ .to-path p = fin-support-list-path $ s .idsᵉ .to-path p
  Extensional-FinSupportList ⦃ s ⦄ .idsᵉ .to-path-over p =
    is-prop→pathp (λ _ → identity-system-hlevel 1 (s .idsᵉ) SupportList-is-set) _ p

  instance
    extensionality-fin-support-list : ∀ {ℓr} ⦃ s : Extensional ⌞ 𝒟 ⌟ ℓr ⦄ → Extensionality FinSupportList
    extensionality-fin-support-list = record { lemma = quote Extensional-FinSupportList }
