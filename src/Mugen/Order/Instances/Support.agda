module Mugen.Order.Instances.Support where

open import Data.List

open import Mugen.Prelude
open import Mugen.Order.StrictOrder
open import Mugen.Order.Lattice
open import Mugen.Order.Instances.Pointwise
open import Mugen.Order.Instances.BasedSupport

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- Finitely Supported Functions
-- Section 3.3.5
--
-- Finitely supported functions over some displacement algebra '𝒟' are
-- functions 'f : Nat → 𝒟' that differ from the unit 'ε' in only a finite number of positions.
-- These are a special case of the Nearly Constant functions where the base is always ε.

record Support-list {A : Type o} (ε : ⌞ A ⌟) : Type o where
  constructor support-list
  no-eta-equality
  field
    based-support : Based-support-list ⌞ A ⌟
  open Based-support-list based-support public
  field
    base-is-ε : base ≡ ε

module _ {A : Type o} ⦃ A-set : H-Level A 2 ⦄ {ε : ⌞ A ⌟} where
  open Support-list

  abstract
    support-list-path : ∀ {xs ys : Support-list ε}
      → xs .based-support ≡ ys .based-support → xs ≡ ys
    support-list-path p i .based-support = p i
    support-list-path {xs} {ys} p i .base-is-ε =
      is-prop→pathp (λ i → hlevel 2 (p i .Based-support-list.base) ε)
        (xs .base-is-ε) (ys .base-is-ε) i

    Support-list-is-set : is-set (Support-list ε)
    Support-list-is-set =
      Equiv→is-hlevel 2 (Iso→Equiv eqv) $
      Σ-is-hlevel 2 (hlevel 2) λ _ →
      Path-is-hlevel 2 (hlevel 2)
      where
        unquoteDecl eqv = declare-record-iso eqv (quote Support-list)

  abstract instance
    H-Level-Support-list : ∀ {n} → H-Level (Support-list ε) (2 + n)
    H-Level-Support-list {n} = basic-instance 2 Support-list-is-set


module _ {A : Type o} where
  open Support-list

  supp-to-based : (ε : ⌞ A ⌟) → Support-list ε → Based-support-list A
  supp-to-based ε xs = xs .based-support

  supp-to-based-is-injective : ∀ ⦃ A-set : H-Level A 2 ⦄ {ε : A} {xs ys : Support-list ε}
    → supp-to-based ε xs ≡ supp-to-based ε ys → xs ≡ ys
  supp-to-based-is-injective p = support-list-path p

module _ (A : Poset o r) where
  private
    module A = Reasoning A
    rep : ∀ ε → represents-full-subposet (Based-support A) (supp-to-based ε)
    rep ε .represents-full-subposet.injective = supp-to-based-is-injective ⦃ hlevel-instance A.Ob-is-set ⦄
    module rep (ε : ⌞ A ⌟) = represents-full-subposet (rep ε)

  Support : ⌞ A ⌟ → Poset o r
  Support ε = rep.poset ε

  Support→Based-support : ∀ ε → Strictly-monotone (Support ε) (Based-support A)
  Support→Based-support ε = rep.strictly-monotone ε

  Support→Based-support-is-full-subposet : ∀ ε → is-full-subposet (Support→Based-support ε)
  Support→Based-support-is-full-subposet ε = rep.has-is-full-subposet ε

--------------------------------------------------------------------------------
-- Joins

module _
  {A : Poset o r}
  ⦃ _ : Discrete ⌞ A ⌟ ⦄
  (A-has-joins : has-joins A)
  where

  private
    module A = Reasoning A
    module A-has-joins = has-joins A-has-joins
    B-has-joins = Based-support-has-joins A-has-joins
    module B-has-joins = has-joins B-has-joins
    open Support-list

    rep : ∀ ε → represents-full-subsemilattice {A = Support A ε} B-has-joins (Support→Based-support-is-full-subposet A ε)
    rep ε .represents-full-subsemilattice.join x y .based-support =
      B-has-joins.join (x .based-support) (y .based-support)
    rep ε .represents-full-subsemilattice.join x y .base-is-ε =
      ap₂ A-has-joins.join (x .base-is-ε) (y .base-is-ε)
      ∙ A.≤-antisym (A-has-joins.universal A.≤-refl A.≤-refl) A-has-joins.joinl
    rep ε .represents-full-subsemilattice.pres-join = refl
    module rep (ε : ⌞ A ⌟) = represents-full-subsemilattice (rep ε)

  Support-has-joins : ∀ ε → has-joins (Support A ε)
  Support-has-joins ε = rep.joins ε

  Support→Based-support-is-full-subsemilattice : ∀ ε
    → is-full-subsemilattice (Support-has-joins ε) B-has-joins (Support→Based-support A ε)
  Support→Based-support-is-full-subsemilattice ε = rep.has-is-full-subsemilattice ε

--------------------------------------------------------------------------------
-- Extensionality

module _ {A : Type o} {ε : ⌞ A ⌟} {ℓr} ⦃ s : Extensional (Based-support-list ⌞ A ⌟) ℓr ⦄ where

  instance
    Extensional-Support-list
      : ⦃ A-is-set : H-Level A 2 ⦄
      → Extensional (Support-list ε) ℓr
    Extensional-Support-list =
      injection→extensional! supp-to-based-is-injective s
