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

record SupportList {A : Type o} (ε : ⌞ A ⌟) : Type o where
  constructor support-list
  no-eta-equality
  field
    based-support : BasedSupportList ⌞ A ⌟
  open BasedSupportList based-support public
  field
    base-is-ε : base ≡ ε

module _ {A : Type o} (A-set : is-set A) {ε : ⌞ A ⌟} where
  open SupportList

  abstract
    support-list-path : ∀ {xs ys : SupportList ε}
      → xs .based-support ≡ ys .based-support → xs ≡ ys
    support-list-path p i .based-support = p i
    support-list-path {xs} {ys} p i .base-is-ε =
      is-prop→pathp (λ i → A-set (p i .BasedSupportList.base) ε)
        (xs .base-is-ε) (ys .base-is-ε) i

    SupportList-is-set : is-set (SupportList ε)
    SupportList-is-set =
      Equiv→is-hlevel 2 (Iso→Equiv eqv) $
      Σ-is-hlevel 2 (BasedSupportList-is-hlevel 0 A-set) λ _ →
      Path-is-hlevel 2 A-set
      where
        unquoteDecl eqv = declare-record-iso eqv (quote SupportList)

  abstract instance


module _ {A : Type o} where
  open SupportList

  supp-to-based : (ε : ⌞ A ⌟) → SupportList ε → BasedSupportList A
  supp-to-based ε xs = xs .based-support

  supp-to-based-is-injective : ∀ (A-set : is-set A) {ε : A} {xs ys : SupportList ε}
    → supp-to-based ε xs ≡ supp-to-based ε ys → xs ≡ ys
  supp-to-based-is-injective A-set p = support-list-path A-set p

module _ (A : Poset o r) where
  private
    module A = Reasoning A
    rep : ∀ ε → represents-full-subposet (BasedSupport A) (supp-to-based ε)
    rep ε .represents-full-subposet.injective = supp-to-based-is-injective A.Ob-is-set
    module rep (ε : ⌞ A ⌟) = represents-full-subposet (rep ε)

  Support : ⌞ A ⌟ → Poset o r
  Support ε = rep.poset ε

  Support→BasedSupport : ∀ ε → Strictly-monotone (Support ε) (BasedSupport A)
  Support→BasedSupport ε = rep.strictly-monotone ε

  Support→BasedSupport-is-full-subposet : ∀ ε → is-full-subposet (Support→BasedSupport ε)
  Support→BasedSupport-is-full-subposet ε = rep.has-is-full-subposet ε

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
    B-has-joins = BasedSupport-has-joins A-has-joins
    module B-has-joins = has-joins B-has-joins
    open SupportList

    rep : ∀ ε → represents-full-subsemilattice {A = Support A ε} B-has-joins (Support→BasedSupport-is-full-subposet A ε)
    rep ε .represents-full-subsemilattice.join x y .based-support =
      B-has-joins.join (x .based-support) (y .based-support)
    rep ε .represents-full-subsemilattice.join x y .base-is-ε =
      ap₂ A-has-joins.join (x .base-is-ε) (y .base-is-ε)
      ∙ A.≤-antisym (A-has-joins.universal A.≤-refl A.≤-refl) A-has-joins.joinl
    rep ε .represents-full-subsemilattice.pres-join = refl
    module rep (ε : ⌞ A ⌟) = represents-full-subsemilattice (rep ε)

  Support-has-joins : ∀ ε → has-joins (Support A ε)
  Support-has-joins ε = rep.joins ε

  Support→BasedSupport-is-full-subsemilattice : ∀ ε
    → is-full-subsemilattice (Support-has-joins ε) B-has-joins (Support→BasedSupport A ε)
  Support→BasedSupport-is-full-subsemilattice ε = rep.has-is-full-subsemilattice ε

--------------------------------------------------------------------------------
-- Extensionality

module _ {A : Type o} {ε : ⌞ A ⌟} {ℓr} ⦃ s : Extensional (BasedSupportList ⌞ A ⌟) ℓr ⦄ where

  instance
    Extensional-FiniteSupportList
      : ⦃ A-is-set : H-Level A 2 ⦄
      → Extensional (SupportList ε) ℓr
    Extensional-FiniteSupportList ⦃ hlevel-instance A-is-set ⦄ =
      injection→extensional! (supp-to-based-is-injective A-is-set) s
