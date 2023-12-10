-- vim: nowrap
module Mugen.Order.Instances.BasedSupport where

open import Mugen.Prelude
open import Mugen.Data.List
open import Mugen.Order.Lattice
open import Mugen.Order.StrictOrder
open import Mugen.Order.Instances.Pointwise

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
-- However, there is a slight problem here when we go to show that
-- this is a subalgebra of 'IdxProd': it's not injective! The problem
-- occurs when you have trailing base elements, meaning 2 lists can
-- denote the same function!
--
-- To resolve this, we say that a list is compact relative
-- to some 'base : 𝒟' if it does not have any trailing base's.
-- We then only work with compact lists in our displacement algebra.

--------------------------------------------------------------------------------
-- Raw Support Lists
--

record RawList (A : Type o) : Type o where
  constructor raw
  field
    elts : List A
    base : A
open RawList

raw-path : ∀ {A : Type o} {xs ys : RawList A}
  → xs .elts ≡ ys .elts
  → xs .base ≡ ys .base
  → xs ≡ ys
raw-path p q i .elts = p i
raw-path p q i .base = q i

-- Lemmas about hlevel
module _ {A : Type o} where
  abstract
    RawList-is-hlevel : (n : Nat) → is-hlevel A (2 + n) → is-hlevel (RawList A) (2 + n)
    RawList-is-hlevel n A-is-hlevel =
      is-hlevel≃ (2 + n) (Iso→Equiv raw-eqv) $
      ×-is-hlevel (2 + n) (ListPath.List-is-hlevel n A-is-hlevel) A-is-hlevel
      where
        unquoteDecl raw-eqv = declare-record-iso raw-eqv (quote RawList)

  instance
    decomp-RawList : hlevel-decomposition (RawList A)
    decomp-RawList = decomp (quote RawList-is-hlevel) (`level-minus 2 ∷ `search ∷ [])

-- Operations and properties for raw support lists
module Raw {A : Type o} where
  private
    _raw∷_ : A → RawList A → RawList A
    x raw∷ (raw xs b) = raw (x ∷ xs) b

  -- Indexing function that turns a list into a map 'Nat → A'
  index : RawList A → (Nat → A)
  index (raw [] b) n = b
  index (raw (x ∷ xs) b) zero = x
  index (raw (x ∷ xs) b) (suc n) = index (raw xs b) n

  --------------------------------------------------------------------------------
  -- Compactness of Raw Lists

  is-compact : RawList A → Type o
  is-compact (raw [] b) = Lift o ⊤
  is-compact (raw (x ∷ []) b) = ¬ (x ≡ b)
  is-compact (raw (_ ∷ y ∷ ys) b) = is-compact (raw (y ∷ ys) b)

  abstract
    is-compact-is-prop : ∀ xs → is-prop (is-compact xs)
    is-compact-is-prop (raw [] _) = hlevel 1
    is-compact-is-prop (raw (_ ∷ []) _) = hlevel 1
    is-compact-is-prop (raw (_ ∷ y ∷ ys) _) = is-compact-is-prop (raw (y ∷ ys) _)

  abstract
    tail-is-compact : ∀ x xs → is-compact (x raw∷ xs) → is-compact xs
    tail-is-compact x (raw [] _) _ = lift tt
    tail-is-compact x (raw (y ∷ ys) _) compact = compact

  abstract
    private
      base-singleton-isnt-compact : ∀ {x xs b} → x ≡ b → xs ≡ raw [] b → is-compact (x raw∷ xs) → ⊥
      base-singleton-isnt-compact {xs = raw [] _} x=b xs=[] is-compact = is-compact $ x=b ∙ sym (ap base xs=[])
      base-singleton-isnt-compact {xs = raw (_ ∷ _) _} x=b xs=[] is-compact = ∷≠[] $ ap elts xs=[]

  --------------------------------------------------------------------------------
  -- Compacting of Raw Lists

  module _ ⦃ _ : Discrete A ⦄ where
    module _ (b : A) where
      compact-list-step : A → List A  → List A
      compact-list-step x [] with x ≡? b
      ... | yes _ = []
      ... | no _ = x ∷ []
      compact-list-step x (y ∷ ys) = x ∷ y ∷ ys

      compact-list : List A → List A
      compact-list [] = []
      compact-list (x ∷ xs) = compact-list-step x (compact-list xs)

    compact-step : A → RawList A → RawList A
    compact-step x (raw xs b) = raw (compact-list-step b x xs) b

    compact : RawList A → RawList A
    compact (raw xs b) = raw (compact-list b xs) b

    abstract
      compact-compacted : ∀ {xs} → is-compact xs → compact xs ≡ xs
      compact-compacted {xs = raw [] _} _ = refl
      compact-compacted {xs = raw (x ∷ []) b} x≠b with x ≡? b
      ... | yes x=b = absurd (x≠b x=b)
      ... | no _ = refl
      compact-compacted {xs = raw (x ∷ y ∷ ys) b} is-compact =
        ap (compact-step x) $ compact-compacted {xs = raw (y ∷ ys) b} is-compact

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

  --------------------------------------------------------------------------------
  -- Lemmas about Indexing and Compacting
  --
  -- Compacting a raw list does not change its indexed values.

  module _ ⦃ _ : Discrete A ⦄ where
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

  merge-list-with : (A → A → A) → RawList A → RawList A → List A
  merge-list-with _⊚_ (raw [] b1) (raw [] b2) = []
  merge-list-with _⊚_ (raw [] b1) (raw (y ∷ ys) b2) = (b1 ⊚ y) ∷ merge-list-with _⊚_ (raw [] b1) (raw ys b2)
  merge-list-with _⊚_ (raw (x ∷ xs) b1) (raw [] b2) = (x ⊚ b2) ∷ merge-list-with _⊚_ (raw xs b1) (raw [] b2)
  merge-list-with _⊚_ (raw (x ∷ xs) b1) (raw (y ∷ ys) b2) = (x ⊚ y) ∷ merge-list-with _⊚_ (raw xs b1) (raw ys b2)

  merge-with : (A → A → A) → RawList A → RawList A → RawList A
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

  --------------------------------------------------------------------------------
  -- Order

  -- 'index' is injective for compacted lists
  abstract
    index-compacted-injective : ∀ xs ys
      → is-compact xs
      → is-compact ys
      → ((n : Nat) → index xs n ≡ index ys n)
      → xs ≡ ys
    index-compacted-injective (raw [] b1) (raw [] b2) _ _ p = raw-path refl (p 0)
    index-compacted-injective (raw (x ∷ xs) b1) (raw [] b2) x∷xs-compact []-compact p =
      let xs-compact = tail-is-compact x (raw xs b1) x∷xs-compact in
      let xs=[] = index-compacted-injective (raw xs b1) (raw [] b2) xs-compact []-compact (p ⊙ suc) in
      absurd (base-singleton-isnt-compact (p 0) xs=[] x∷xs-compact)
    index-compacted-injective (raw [] b1) (raw (y ∷ ys) b2) []-compact y∷ys-compact p =
      let ys-compact = tail-is-compact y (raw ys b2) y∷ys-compact in
      let []=ys = index-compacted-injective (raw [] b1) (raw ys b2) []-compact ys-compact (p ⊙ suc) in
      absurd $ᵢ base-singleton-isnt-compact (sym (p 0)) (sym []=ys) y∷ys-compact
    index-compacted-injective (raw (x ∷ xs) b1) (raw (y ∷ ys) b2) x∷xs-compact y∷ys-compact p =
      let xs-compact = tail-is-compact x (raw xs b1) x∷xs-compact in
      let ys-compact = tail-is-compact y (raw ys b2) y∷ys-compact in
      let xs=ys = index-compacted-injective (raw xs b1) (raw ys b2) xs-compact ys-compact (p ⊙ suc) in
      ap₂ _raw∷_ (p 0) xs=ys

--------------------------------------------------------------------------------
-- These will be the actual elements of our displacement algebra.
-- A support list is a compact raw list.

record BasedSupportList (A : Type o) : Type o where
  constructor based-support-list
  no-eta-equality
  field
    list : RawList A
    has-is-compact : Raw.is-compact list
  open RawList list public

module _ {A : Type o} where
  open BasedSupportList

  -- Paths in support lists are determined by paths between the bases + paths between the elements.
  abstract
    based-support-list-path : ∀ {xs ys : BasedSupportList A} → xs .list ≡ ys .list → xs ≡ ys
    based-support-list-path p i .list = p i
    based-support-list-path {xs = xs} {ys = ys} p i .has-is-compact =
      is-prop→pathp (λ i → Raw.is-compact-is-prop (p i)) (xs .has-is-compact) (ys .has-is-compact) i

    BasedSupportList-is-hlevel : (n : Nat)
      → is-hlevel A (2 + n) → is-hlevel (BasedSupportList A) (2 + n)
    BasedSupportList-is-hlevel n A-is-hlevel =
      is-hlevel≃ (2 + n) (Iso→Equiv eqv) $
      Σ-is-hlevel (2 + n) (RawList-is-hlevel n A-is-hlevel) λ xs →
      is-prop→is-hlevel-suc {n = 1 + n} (Raw.is-compact-is-prop xs)
      where
        unquoteDecl eqv = declare-record-iso eqv (quote BasedSupportList)

  instance
    decomp-BasedSupportList : hlevel-decomposition (BasedSupportList A)
    decomp-BasedSupportList = decomp (quote BasedSupportList-is-hlevel) (`level-minus 2 ∷ `search ∷ [])

  index : BasedSupportList A → (Nat → A)
  index xs = Raw.index (xs .list)

  module _ ⦃ _ : Discrete A ⦄ where
    merge-with : (A → A → A) → BasedSupportList A → BasedSupportList A → BasedSupportList A
    merge-with f xs ys .list = Raw.compact $ Raw.merge-with f (xs .list) (ys .list)
    merge-with f xs ys .has-is-compact = Raw.compact-is-compact $ Raw.merge-with f (xs .list) (ys .list)

    -- 'index' commutes with 'merge'
    abstract
      index-merge-with : ∀ f xs ys
        → index (merge-with f xs ys) ≡ pointwise-map₂ (λ _ x y → f x y) (index xs) (index ys)
      index-merge-with f xs ys = funext λ n →
        Raw.index-compact (Raw.merge-with f (xs .list) (ys .list)) n
        ∙ Raw.index-merge-with f (xs .list) (ys .list) n

  abstract
    index-injective : ∀ {xs ys} → index xs ≡ index ys → xs ≡ ys
    index-injective {xs} {ys} p = based-support-list-path $
      Raw.index-compacted-injective _ _ (xs .has-is-compact) (ys .has-is-compact) $
      happly p

module _ (A : Poset o r) where
  private
    rep : represents-full-subposet (Pointwise Nat (λ _ → A)) index
    rep .represents-full-subposet.injective = index-injective
    module rep = represents-full-subposet rep

  BasedSupport : Poset o r
  BasedSupport = rep.poset

  BasedSupport→Pointwise : Strictly-monotone BasedSupport (Pointwise Nat (λ _ → A))
  BasedSupport→Pointwise = rep.strictly-monotone

  BasedSupport→Pointwise-is-full-subposet : is-full-subposet BasedSupport→Pointwise
  BasedSupport→Pointwise-is-full-subposet = rep.has-is-full-subposet

--------------------------------------------------------------------------------
-- Joins

module _
  {A : Poset o r}
  ⦃ _ : Discrete ⌞ A ⌟ ⦄
  (A-has-joins : has-joins A)
  where
  private
    module A = Reasoning A
    module P = Reasoning (Pointwise Nat λ _ → A)
    module A-has-joins = has-joins A-has-joins
    P-has-joins = Pointwise-has-joins Nat λ _ → A-has-joins
    module P-has-joins = has-joins P-has-joins

    rep : represents-full-subsemilattice P-has-joins (BasedSupport→Pointwise-is-full-subposet A)
    rep .represents-full-subsemilattice.join = merge-with A-has-joins.join
    rep .represents-full-subsemilattice.pres-join {x} {y} = index-merge-with A-has-joins.join x y
    module rep = represents-full-subsemilattice rep

  BasedSupport-has-joins : has-joins (BasedSupport A)
  BasedSupport-has-joins = rep.joins

  BasedSupport→Pointwise-is-full-subsemilattice
    : is-full-subsemilattice BasedSupport-has-joins P-has-joins (BasedSupport→Pointwise A)
  BasedSupport→Pointwise-is-full-subsemilattice = rep.has-is-full-subsemilattice

--------------------------------------------------------------------------------
-- Bottoms

module _
  (A : Poset o r)
  ⦃ _ : Discrete ⌞ A ⌟ ⦄
  (A-has-bottom : has-bottom A)
  where
  private
    module A = Reasoning A
    module P = Reasoning (Pointwise Nat λ _ → A)
    module A-has-bottom = has-bottom A-has-bottom
    P-has-bottom = Pointwise-has-bottom Nat λ _ → A-has-bottom
    module P-has-bottom = has-bottom P-has-bottom

    rep : represents-full-bounded-subposet P-has-bottom (BasedSupport→Pointwise-is-full-subposet A)
    rep .represents-full-bounded-subposet.bot = based-support-list (raw [] A-has-bottom.bot) (lift tt)
    rep .represents-full-bounded-subposet.pres-bot = refl
    module rep = represents-full-bounded-subposet rep

  BasedSupport-has-bottom : has-bottom (BasedSupport A)
  BasedSupport-has-bottom = rep.bottom

  BasedSupport→Pointwise-is-full-bounded-subposet
    : is-full-bounded-subposet BasedSupport-has-bottom P-has-bottom (BasedSupport→Pointwise A)
  BasedSupport→Pointwise-is-full-bounded-subposet = rep.has-is-full-bounded-subposet

--------------------------------------------------------------------------------
-- Extensionality

module _ {A : Type o} ⦃ _ : H-Level A 2 ⦄ {ℓr} ⦃ s : Extensional (Nat → ⌞ A ⌟) ℓr ⦄ where

  Extensional-BasedSupportList : Extensional (BasedSupportList ⌞ A ⌟) ℓr
  Extensional-BasedSupportList = injection→extensional! index-injective s

  instance
    extensionality-based-support-list : Extensionality (BasedSupportList ⌞ A ⌟)
    extensionality-based-support-list = record { lemma = quote Extensional-BasedSupportList }
