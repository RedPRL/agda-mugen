module Mugen.Algebra.Displacement.NearlyConstant where

open import 1Lab.Reflection.Record

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude

open import Mugen.Axioms.WLPO
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Coimage
open import Mugen.Algebra.Displacement.InfiniteProduct
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

open import Mugen.Data.List

--------------------------------------------------------------------------------
-- Nearly Constant Functions
-- Section 3.3.5
--
-- A "nearly constant function" is some function 'f : Nat → 𝒟'
-- that differs from some fixed 'd : 𝒟' for only a finite set of 'n : Nat'
--
-- We represent these via prefix lists. IE: the function
--
-- > λ n → if n = 1 then 2 else if n = 3 then 1 else 5
--
-- will be represented as a pair (5, [5,2,5,3]). We will call the
-- first element of this pair "the base" of the function, and the
-- prefix list "the support".
--
-- However, there is a slight problem here when we go to show that
-- this is a subalgebra of 'InfProd': it's not injective! The problem
-- occurs when you have trailing base elements, meaning 2 lists can
-- denote the same function!
--
-- To resolve this, we say that a list is compact relative
-- to some 'base : 𝒟' if it does not have any trailing base's.
-- We then only work with compact lists in our displacement algebra.

module NearlyConst
  {o r}
  (𝒟 : Displacement-algebra o r)
  (let module 𝒟 = Displacement-algebra 𝒟)
  (cmp : ∀ x y → Tri 𝒟._<_ x y) where

  private
    open 𝒟 using (ε; _⊗_)
    open Inf 𝒟

    instance
      HLevel-< : ∀ {x y} {n} → H-Level (x 𝒟.< y) (suc n)
      HLevel-< = prop-instance 𝒟.<-thin

      HLevel-≤ : ∀ {x y} {n} → H-Level (x 𝒟.≤ y) (suc n)
      HLevel-≤ = prop-instance 𝒟.≤-thin

  _≡?_ : Discrete ⌞ 𝒟 ⌟
  x ≡? y =
    tri-elim
      (λ _ → Dec (x ≡ y))
      (λ x<y → no λ x≡y → 𝒟.<→≠ x<y x≡y)
      yes
      (λ y<x → no λ x≡y → 𝒟.<→≠ y<x (sym x≡y))
      (cmp x y)

  --------------------------------------------------------------------------------
  -- Raw Support Lists
  --

  record RawList : Type o where
    constructor raw
    field
      elts : List ⌞ 𝒟 ⌟
      base : ⌞ 𝒟 ⌟

  open RawList

  raw-path : ∀ {xs ys : RawList}
    → xs .elts ≡ ys .elts
    → xs .base ≡ ys .base
    → xs ≡ ys
  raw-path p q i .elts = p i
  raw-path p q i .base = q i

  _raw∷_ : ⌞ 𝒟 ⌟ → RawList → RawList
  x raw∷ (raw xs b) = raw (x ∷ xs) b

  private unquoteDecl raw-eqv = declare-record-iso raw-eqv (quote RawList)

  RawList-is-set : is-set RawList
  RawList-is-set =
    is-hlevel≃ 2 (Iso→Equiv raw-eqv) $
    ×-is-hlevel 2 (ListPath.List-is-hlevel 0 𝒟.has-is-set) (hlevel 2)

  -- Operations and properties for raw support lists
  module Raw where

    -- Indexing function that turns a list into a map 'Nat → ⌞ 𝒟 ⌟'
    index : RawList → (Nat → ⌞ 𝒟 ⌟)
    index (raw [] b) n = b
    index (raw (x ∷ xs) b) zero = x
    index (raw (x ∷ xs) b) (suc n) = index (raw xs b) n

    --------------------------------------------------------------------------------
    -- Compact Support Lists
    --
    -- These will be the actual elements of our displacement algebra.
    -- A SupportList consists of a choice of base, and a compact list
    -- relative to that base.

    is-compact : RawList → Type o
    is-compact (raw [] b) = Lift o ⊤
    is-compact (raw (x ∷ []) b) = ¬ (x ≡ b)
    is-compact (raw (_ ∷ y ∷ ys) b) = is-compact (raw (y ∷ ys) b)

    abstract
      is-compact-is-prop : ∀ xs → is-prop (is-compact xs)
      is-compact-is-prop (raw [] _) = hlevel 1
      is-compact-is-prop (raw (_ ∷ []) _) = hlevel 1
      is-compact-is-prop (raw (_ ∷ y ∷ ys) _) = is-compact-is-prop (raw (y ∷ ys) _)

    compact-step : ⌞ 𝒟 ⌟ → RawList → RawList
    compact-step x (raw [] b) with x ≡? b
    ... | yes _ = raw [] b
    ... | no _ = raw (x ∷ []) b
    compact-step x (raw (y ∷ ys) b) = (raw (x ∷ y ∷ ys) b)

    compact : RawList → RawList
    compact (raw [] b) = raw [] b
    compact (raw (x ∷ xs) b) = compact-step x (compact (raw xs b))

    -- compact preserves 'base'
    abstract
      private
        base-compact-step : ∀ x xs → compact-step x xs .base ≡ xs .base
        base-compact-step x (raw [] b) with x ≡? b
        ... | yes _ = refl
        ... | no _ = refl
        base-compact-step x (raw (y ∷ ys) b) = refl

      base-compact : ∀ xs → compact xs .base ≡ xs .base
      base-compact (raw [] b) = refl
      base-compact (raw (x ∷ xs) b) =
        base-compact-step x (compact (raw xs b)) ∙ base-compact (raw xs b)

    abstract
      compact-compacted : ∀ {xs} → is-compact xs → compact xs ≡ xs
      compact-compacted {xs = raw [] _} _ = refl
      compact-compacted {xs = raw (x ∷ []) b} x≠b with x ≡? b
      ... | yes x=b = absurd (x≠b x=b)
      ... | no _ = refl
      compact-compacted {xs = raw (x ∷ y ∷ ys) b} is-compact =
        ap (compact-step x) $ compact-compacted {xs = raw (y ∷ ys) b} is-compact

    abstract
      tail-is-compact : ∀ x xs → is-compact (x raw∷ xs) → is-compact xs
      tail-is-compact x (raw [] _) _ = lift tt
      tail-is-compact x (raw (y ∷ ys) _) compact = compact

    -- the result of 'compact' is a compact list
    abstract
      private
        compact-step-is-compact : ∀ x xs
          → is-compact xs
          → is-compact (compact-step x xs)
        compact-step-is-compact x (raw [] b) _ with x ≡? b
        ... | yes _ = lift tt
        ... | no x≠b = x≠b
        compact-step-is-compact x (raw (y ∷ ys) b) is-compact = is-compact

      compact-is-compact : ∀ xs → is-compact (compact xs)
      compact-is-compact (raw [] _) = lift tt
      compact-is-compact (raw (x ∷ xs) b) =
        compact-step-is-compact x (compact (raw xs b)) (compact-is-compact (raw xs b))

    -- 'compact' does not change the result of 'index'
    abstract
      private
        index-compact-step-zero : ∀ x xs
          → index (compact-step x xs) zero ≡ x
        index-compact-step-zero x (raw [] b) with x ≡? b
        ... | yes x=b = sym x=b
        ... | no _ = refl
        index-compact-step-zero x (raw (_ ∷ _) _) = refl

        index-compact-step-suc : ∀ x xs n
          → index (compact-step x xs) (suc n) ≡ index xs n
        index-compact-step-suc x (raw [] b) n with x ≡? b
        ... | yes _ = refl
        ... | no _ = refl
        index-compact-step-suc x (raw (_ ∷ _) _) n = refl

    -- Indexing a compacted list is the same as indexing the uncompacted list.
    abstract
      index-compact : ∀ xs n → index (compact xs) n ≡ index xs n
      index-compact (raw [] _) n = refl
      index-compact (raw (x ∷ xs) b) zero =
        index-compact-step-zero x (compact (raw xs b))
      index-compact (raw (x ∷ xs) b) (suc n) =
        index (compact-step x (compact (raw xs b))) (suc n)
          ≡⟨ index-compact-step-suc x (compact (raw xs b)) n ⟩
        index (compact (raw xs b)) n
          ≡⟨ index-compact (raw xs b) n ⟩
        index (raw xs b) n
          ∎

    --------------------------------------------------------------------------------
    -- Merging Lists

    merge-list-with : (⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟) → RawList → RawList → List ⌞ 𝒟 ⌟
    merge-list-with _⊚_ (raw [] b1) (raw [] b2) = []
    merge-list-with _⊚_ (raw [] b1) (raw (y ∷ ys) b2) = (b1 ⊚ y) ∷ merge-list-with _⊚_ (raw [] b1) (raw ys b2)
    merge-list-with _⊚_ (raw (x ∷ xs) b1) (raw [] b2) = (x ⊚ b2) ∷ merge-list-with _⊚_ (raw xs b1) (raw [] b2)
    merge-list-with _⊚_ (raw (x ∷ xs) b1) (raw (y ∷ ys) b2) = (x ⊚ y) ∷ merge-list-with _⊚_ (raw xs b1) (raw ys b2)

    merge-with : (⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟) → RawList → RawList → RawList
    merge-with _⊚_ xs ys = raw (merge-list-with _⊚_ xs ys) (xs .base ⊚ ys .base)

    abstract
      index-merge-with : ∀ f xs ys n → index (merge-with f xs ys) n ≡ f (index xs n) (index ys n)
      index-merge-with f (raw [] b1) (raw [] b2) n = refl
      index-merge-with f (raw [] b1) (raw (y ∷ ys) b2) zero = refl
      index-merge-with f (raw [] b1) (raw (y ∷ ys) b2) (suc n) = index-merge-with f (raw [] b1) (raw ys b2) n
      index-merge-with f (raw (x ∷ xs) b1) (raw [] b2) zero = refl
      index-merge-with f (raw (x ∷ xs) b1) (raw [] b2) (suc n) = index-merge-with f (raw xs b1) (raw [] b2) n
      index-merge-with f (raw (x ∷ xs) b1) (raw (y ∷ ys) b2) zero = refl
      index-merge-with f (raw (x ∷ xs) b1) (raw (y ∷ ys) b2) (suc n) = index-merge-with f (raw xs b1) (raw ys b2) n

      base-merge-with : ∀ f xs ys → merge-with f xs ys .base ≡ f (xs .base) (ys .base)
      base-merge-with f xs ys = refl


    --------------------------------------------------------------------------------
    -- Order

    _<_ : RawList → RawList → Type (o ⊔ r)
    xs < ys = index xs inf< index ys

    index= : RawList → RawList → Type o
    index= xs ys = (n : Nat) → index xs n ≡ index ys n

    abstract
      index=? : ∀ xs ys → Dec (index= xs ys)
      index=? (raw [] b1) (raw [] b2) with b1 ≡? b2
      ... | yes b1=b2 = yes λ n → b1=b2
      ... | no  b1≠b2 = no  λ p → b1≠b2 (p 0)
      index=? (raw (x ∷ xs) b1) (raw [] b2) with x ≡? b2 | index=? (raw xs b1) (raw [] b2)
      ... | no  x≠b2 | _         = no  λ p → x≠b2 (p 0)
      ... | yes _    | no  xs≠[] = no  λ p → xs≠[] (p ⊙ suc)
      ... | yes x=b2 | yes xs=[] = yes λ { zero → x=b2; (suc n) → xs=[] n }
      index=? (raw [] b1) (raw (y ∷ ys) b2) with b1 ≡? y | index=? (raw [] b1) (raw ys b2)
      ... | no  b1≠y | _         = no  λ p → b1≠y (p 0)
      ... | yes _    | no  []≠ys = no  λ p → []≠ys (p ⊙ suc)
      ... | yes b1=y | yes []=ys = yes λ { zero → b1=y; (suc n) → []=ys n }
      index=? (raw (x ∷ xs) b1) (raw (y ∷ ys) b2) with x ≡? y | index=? (raw xs b1) (raw ys b2)
      ... | no  x≠y | _         = no  λ p → x≠y (p 0)
      ... | yes _   | no  xs≠ys = no  λ p → xs≠ys (p ⊙ suc)
      ... | yes x=y | yes xs=ys = yes λ { zero → x=y; (suc n) → xs=ys n }

    -- 'index=' implies equality
    abstract
      private
        base-singleton-isnt-compact : ∀ {x xs b} → x ≡ b → xs ≡ raw [] b → is-compact (x raw∷ xs) → ⊥
        base-singleton-isnt-compact {xs = raw [] _} x=b xs=[] is-compact = is-compact $ x=b ∙ sym (ap base xs=[])
        base-singleton-isnt-compact {xs = raw (_ ∷ _) _} x=b xs=[] is-compact = ∷≠[] $ ap elts xs=[]

      index-compacted-inj : ∀ xs ys
        → is-compact xs
        → is-compact ys
        → index= xs ys
        → xs ≡ ys
      index-compacted-inj (raw [] b1) (raw [] b2) _ _ p = raw-path refl (p 0)
      index-compacted-inj (raw (x ∷ xs) b1) (raw [] b2) x∷xs-compact []-compact p =
        let xs-compact = tail-is-compact x (raw xs b1) x∷xs-compact in
        let xs=[] = index-compacted-inj (raw xs b1) (raw [] b2) xs-compact []-compact (p ⊙ suc) in
        absurd $ base-singleton-isnt-compact (p 0) xs=[] x∷xs-compact
      index-compacted-inj (raw [] b1) (raw (y ∷ ys) b2) []-compact y∷ys-compact p =
        let ys-compact = tail-is-compact y (raw ys b2) y∷ys-compact in
        let []=ys = index-compacted-inj (raw [] b1) (raw ys b2) []-compact ys-compact (p ⊙ suc) in
        absurd $ base-singleton-isnt-compact (sym (p 0)) (sym []=ys) y∷ys-compact
      index-compacted-inj (raw (x ∷ xs) b1) (raw (y ∷ ys) b2) x∷xs-compact y∷ys-compact p =
        let xs-compact = tail-is-compact x (raw xs b1) x∷xs-compact in
        let ys-compact = tail-is-compact y (raw ys b2) y∷ys-compact in
        let xs=ys = index-compacted-inj (raw xs b1) (raw ys b2) xs-compact ys-compact (p ⊙ suc) in
        ap₂ _raw∷_ (p 0) xs=ys

  record SupportList : Type o where
    constructor support-list
    no-eta-equality
    field
      list : RawList
      has-is-compact : Raw.is-compact list

    open RawList list public

  open SupportList

  -- Paths in support lists are determined by paths between the bases + paths between the elements.
  support-list-path : ∀ {xs ys : SupportList} → xs .list ≡ ys .list → xs ≡ ys
  support-list-path p i .list = p i
  support-list-path {xs = xs} {ys = ys} p i .has-is-compact =
    is-prop→pathp (λ i → Raw.is-compact-is-prop (p i)) (xs .has-is-compact) (ys .has-is-compact) i

  private unquoteDecl eqv = declare-record-iso eqv (quote SupportList)

  SupportList-is-set : is-set SupportList
  SupportList-is-set =
    is-hlevel≃ 2 (Iso→Equiv eqv) $
      Σ-is-hlevel 2 RawList-is-set λ xs →
      is-prop→is-set (Raw.is-compact-is-prop xs)

  merge-with : (⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟) → SupportList → SupportList → SupportList
  merge-with f xs ys .list = Raw.compact $ Raw.merge-with f (xs .list) (ys .list)
  merge-with f xs ys .has-is-compact = Raw.compact-is-compact $ Raw.merge-with f (xs .list) (ys .list)

  merge : SupportList → SupportList → SupportList
  merge = merge-with _⊗_

  -- The empty SupportList
  empty : SupportList
  empty .list = raw [] ε
  empty .has-is-compact = lift tt

  _<_ : SupportList → SupportList → Type (o ⊔ r)
  xs < ys = xs .list Raw.< ys .list

  _≤_ : SupportList → SupportList → Type (o ⊔ r)
  _≤_ = non-strict _<_

  index : SupportList → (Nat → ⌞ 𝒟 ⌟)
  index xs = Raw.index (xs .list)

  abstract
    index-merge-with : ∀ f xs ys n → index (merge-with f xs ys) n ≡ f (index xs n) (index ys n)
    index-merge-with f xs ys n =
      Raw.index-compact (Raw.merge-with f (xs .list) (ys .list)) n
      ∙ Raw.index-merge-with f (xs .list) (ys .list) n

    index-merge : ∀ xs ys n → index (merge xs ys) n ≡ index xs n ⊗ index ys n
    index-merge = index-merge-with _⊗_

    base-merge-with : ∀ f xs ys → merge-with f xs ys .base ≡ f (xs .base) (ys .base)
    base-merge-with f xs ys = Raw.base-compact (Raw.merge-with f (xs .list) (ys .list))

    base-merge : ∀ xs ys → merge xs ys .base ≡ xs .base ⊗ ys .base
    base-merge = base-merge-with _⊗_

  abstract
    index-inj : ∀ {xs ys} → ((n : Nat) → index xs n ≡ index ys n) → xs ≡ ys
    index-inj {xs} {ys} p = support-list-path $
      Raw.index-compacted-inj (xs .list) (ys .list) (xs .has-is-compact) (ys .has-is-compact) p

  abstract
    ≤→≤-pointwise : ∀ {xs ys} → xs ≤ ys → (∀ n → index xs n 𝒟.≤ index ys n)
    ≤→≤-pointwise (inl xs=ys) n = inl $ ap (λ xs → index xs n) xs=ys
    ≤→≤-pointwise (inr xs<ys) n = xs<ys .≤-pointwise n

    ≤-pointwise→≤ : ∀ {xs ys} → (∀ n → index xs n 𝒟.≤ index ys n) → xs ≤ ys
    ≤-pointwise→≤ {xs} {ys} pointwise with Raw.index=? (xs .list) (ys .list)
    ... | no  xs≠ys = inr $ inf-< pointwise xs≠ys
    ... | yes xs=ys = inl $ index-inj xs=ys

--------------------------------------------------------------------------------
-- Bundled Instances

module _ {o r} (𝒟 : Displacement-algebra o r) (cmp : ∀ x y → Tri (Displacement-algebra._<_ 𝒟) x y) where
  private module 𝒟 = Displacement-algebra 𝒟
  open Inf 𝒟
  open NearlyConst 𝒟 cmp

  NearlyConstant : Displacement-algebra o (o ⊔ r)
  NearlyConstant = to-displacement-algebra mk where
    mk-strict : make-strict-order (o ⊔ r) SupportList
    mk-strict .make-strict-order._<_ = _<_
    mk-strict .make-strict-order.<-irrefl = inf<-irrefl
    mk-strict .make-strict-order.<-trans = inf<-trans
    mk-strict .make-strict-order.<-thin = inf<-is-prop
    mk-strict .make-strict-order.has-is-set = SupportList-is-set

    mk : make-displacement-algebra (to-strict-order mk-strict)
    mk .make-displacement-algebra.ε = empty
    mk .make-displacement-algebra._⊗_ = merge
    mk .make-displacement-algebra.idl {xs} = index-inj λ n →
      index-merge empty xs n ∙ 𝒟.idl
    mk .make-displacement-algebra.idr {xs} = index-inj λ n →
      index-merge xs empty n ∙ 𝒟.idr
    mk .make-displacement-algebra.associative {xs} {ys} {zs} = index-inj λ n →
      index (merge xs (merge ys zs)) n
        ≡⟨ index-merge xs (merge ys zs) n ⟩
      (index xs n 𝒟.⊗ index (merge ys zs) n)
        ≡⟨ ap (index xs n 𝒟.⊗_) $ index-merge ys zs n ⟩
      (index xs n 𝒟.⊗ (index ys n 𝒟.⊗ index zs n))
        ≡⟨ 𝒟.associative ⟩
      ((index xs n 𝒟.⊗ index ys n) 𝒟.⊗ index zs n)
        ≡˘⟨ ap (𝒟._⊗ index zs n) $ index-merge xs ys n ⟩
      (index (merge xs ys) n 𝒟.⊗ index zs n)
        ≡˘⟨ index-merge (merge xs ys) zs n ⟩
      index (merge (merge xs ys) zs) n
        ∎
    mk .make-displacement-algebra.left-invariant {xs} {ys} {zs} ys<zs =
      coe1→0 (λ i → (λ n → index-merge xs ys n i) inf< (λ n → index-merge xs zs n i)) $
      ⊗∞-left-invariant ys<zs

--------------------------------------------------------------------------------
-- Subalgebra Structure

module _ {o r} {𝒟 : Displacement-algebra o r} (cmp : ∀ x y → Tri (Displacement-algebra._<_ 𝒟) x y) where
  open NearlyConst 𝒟 cmp

  NearlyConstant⊆InfProd : is-displacement-subalgebra (NearlyConstant 𝒟 cmp) (InfProd 𝒟)
  NearlyConstant⊆InfProd = to-displacement-subalgebra mk where
    mk : make-displacement-subalgebra (NearlyConstant 𝒟 cmp) (InfProd 𝒟)
    mk .make-displacement-subalgebra.into = index
    mk .make-displacement-subalgebra.pres-ε = refl
    mk .make-displacement-subalgebra.pres-⊗ xs ys = funext (index-merge xs ys)
    mk .make-displacement-subalgebra.strictly-mono xs ys xs<ys = xs<ys
    mk .make-displacement-subalgebra.inj p = index-inj (happly p)

--------------------------------------------------------------------------------
-- Ordered Monoid

module _
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (𝒟-ordered-monoid : has-ordered-monoid 𝒟)
  (cmp : ∀ x y → Tri 𝒟._<_ x y)
  where
  open NearlyConst 𝒟 cmp
  open is-ordered-monoid 𝒟-ordered-monoid

  ≤-right-invariant : ∀ {xs ys zs} → xs ≤ ys → merge xs zs ≤ merge ys zs
  ≤-right-invariant {xs} {ys} {zs} xs≤ys = ≤-pointwise→≤ λ n →
    coe1→0 (λ i → index-merge xs zs n i 𝒟.≤ index-merge ys zs n i) $
    right-invariant (≤→≤-pointwise xs≤ys n)

  nearly-constant-has-ordered-monoid : has-ordered-monoid (NearlyConstant 𝒟 cmp)
  nearly-constant-has-ordered-monoid = right-invariant→has-ordered-monoid (NearlyConstant 𝒟 cmp) ≤-right-invariant

--------------------------------------------------------------------------------
-- Joins

module NearlyConstJoins
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (𝒟-joins : has-joins 𝒟) (cmp : ∀ x y → Tri 𝒟._<_ x y)
  where
  open NearlyConst 𝒟 cmp
  private module 𝒥 = has-joins 𝒟-joins

  join : SupportList → SupportList → SupportList
  join = merge-with 𝒥.join

  nearly-constant-has-joins : has-joins (NearlyConstant 𝒟 cmp)
  nearly-constant-has-joins .has-joins.join = join
  nearly-constant-has-joins .has-joins.joinl {xs} {ys} =
    ≤-pointwise→≤ λ n → 𝒟.≤+≡→≤ 𝒥.joinl (sym $ index-merge-with 𝒥.join xs ys n)
  nearly-constant-has-joins .has-joins.joinr {xs} {ys} =
    ≤-pointwise→≤ λ n → 𝒟.≤+≡→≤ 𝒥.joinr (sym $ index-merge-with 𝒥.join xs ys n)
  nearly-constant-has-joins .has-joins.universal {xs} {ys} {zs} xs≤zs ys≤zs =
    ≤-pointwise→≤ λ n → 𝒟.≡+≤→≤
      (index-merge-with 𝒥.join xs ys n)
      (𝒥.universal (≤→≤-pointwise xs≤zs n) (≤→≤-pointwise ys≤zs n))

  -- NOTE: 'index' preserves joins regardless of WLPO, but the joins in InfProd aren't /provably/
  -- joins unless we have WLPO, hence the extra module below.
  index-preserves-join : ∀ xs ys n → index (join xs ys) n ≡ 𝒥.join (index xs n) (index ys n)
  index-preserves-join = index-merge-with 𝒥.join

  module _ (𝒟-wlpo : WLPO 𝒟.strict-order _≡?_) where
    open InfProperties {𝒟 = 𝒟} _≡?_ 𝒟-wlpo

    nearly-constant-is-subsemilattice : is-displacement-subsemilattice nearly-constant-has-joins (⊗∞-has-joins 𝒟-joins)
    nearly-constant-is-subsemilattice .is-displacement-subsemilattice.has-displacement-subalgebra = NearlyConstant⊆InfProd cmp
    nearly-constant-is-subsemilattice .is-displacement-subsemilattice.pres-joins x y = funext (index-preserves-join x y)

--------------------------------------------------------------------------------
-- Bottoms

module _
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (𝒟-bottom : has-bottom 𝒟)
  (cmp : ∀ x y → Tri (Displacement-algebra._<_ 𝒟) x y) (b : ⌞ 𝒟 ⌟)
  where
  open 𝒟 using (ε; _⊗_; _<_; _≤_)
  open NearlyConst 𝒟 cmp
  open Inf 𝒟
  open SupportList
  open has-bottom 𝒟-bottom

  nearly-constant-has-bottom : has-bottom (NearlyConstant 𝒟 cmp)
  nearly-constant-has-bottom .has-bottom.bot = support-list (raw [] bot) (lift tt)
  nearly-constant-has-bottom .has-bottom.is-bottom xs = ≤-pointwise→≤ λ n → is-bottom _

  module _ (𝒟-wlpo : WLPO 𝒟.strict-order _≡?_) where
    open InfProperties {𝒟 = 𝒟} _≡?_ 𝒟-wlpo

    nearly-constant-is-bounded-subalgebra : is-bounded-displacement-subalgebra nearly-constant-has-bottom (⊗∞-has-bottom 𝒟-bottom)
    nearly-constant-is-bounded-subalgebra .is-bounded-displacement-subalgebra.has-displacement-subalgebra = NearlyConstant⊆InfProd cmp
    nearly-constant-is-bounded-subalgebra .is-bounded-displacement-subalgebra.pres-bottom = refl

--------------------------------------------------------------------------------
-- Extensionality based on 'index-inj'

-- this lemma should probably be put into 1lab
private
  identity-system-hlevel
    : ∀ {ℓ ℓ'} {A : Type ℓ} n {R : A → A → Type ℓ'} {r : ∀ x → R x x}
    → is-identity-system R r
    → is-hlevel A (suc n)
    → ∀ {x y : A} → is-hlevel (R x y) n
  identity-system-hlevel n ids hl {x} {y} =
    is-hlevel≃ n (identity-system-gives-path ids) (Path-is-hlevel' n hl x y)

-- 1lab's or Agda's instance search somehow does not seem to deal with
-- explicit arguments, so we re-parametrize things with implicit '𝒟' and 'cmp'.
module _ {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  {cmp : ∀ x y → Tri 𝒟._<_ x y}
  where
  open NearlyConst 𝒟 cmp

  Extensional-SupportList : ∀ {ℓr} ⦃ s : Extensional ⌞ 𝒟 ⌟ ℓr ⦄ → Extensional SupportList ℓr
  Extensional-SupportList ⦃ s ⦄ .Pathᵉ xs ys =
    (n : Nat) → s .Pathᵉ (index xs n) (index ys n)
  Extensional-SupportList ⦃ s ⦄ .reflᵉ xs =
    λ n → s .reflᵉ (index xs n)
  Extensional-SupportList ⦃ s ⦄ .idsᵉ .to-path p =
    index-inj λ n → s .idsᵉ .to-path (p n)
  Extensional-SupportList ⦃ s ⦄ .idsᵉ .to-path-over p =
    is-prop→pathp (λ _ → Π-is-hlevel 1 λ n → identity-system-hlevel 1 (s .idsᵉ) 𝒟.has-is-set) _ p

  instance
    extensionality-support-list : ∀ {ℓr} ⦃ s : Extensional ⌞ 𝒟 ⌟ ℓr ⦄ → Extensionality SupportList
    extensionality-support-list = record { lemma = quote Extensional-SupportList }
