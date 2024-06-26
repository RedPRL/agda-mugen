module Mugen.Algebra.OrderedMonoid where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude

private variable
  o r : Level
  A : Type o

--------------------------------------------------------------------------------
-- Ordered Monoids
-- We define these as structures on posets.

record is-ordered-monoid {o r}
  (A : Poset o r) (ε : ⌞ A ⌟) (_⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟)
  : Type (o ⊔ r)
  where
  no-eta-equality
  open Poset A
  field
    has-is-monoid : is-monoid ε _⊗_
    invariant : ∀ {w x y z} → w ≤ y → x ≤ z → (w ⊗ x) ≤ (y ⊗ z)

  open is-monoid has-is-monoid public

  left-invariant : ∀ {x y z} → y ≤ z → (x ⊗ y) ≤ (x ⊗ z)
  left-invariant y≤z = invariant ≤-refl y≤z

  right-invariant : ∀ {x y z} → x ≤ y → (x ⊗ z) ≤ (y ⊗ z)
  right-invariant x≤y = invariant x≤y ≤-refl

record Ordered-monoid-on {o r : Level} (A : Poset o r) : Type (o ⊔ lsuc r) where
  field
    ε : ⌞ A ⌟
    _⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟
    has-ordered-monoid : is-ordered-monoid A ε _⊗_

  open is-ordered-monoid has-ordered-monoid public

--------------------------------------------------------------------------------
-- Ordered Monoid Actions

record is-right-ordered-monoid-action
  {o r o′ r′} (A : Poset o r) {B : Poset o′ r′} (M : Ordered-monoid-on B)
  (α : ⌞ A ⌟ → ⌞ B ⌟ → ⌞ A ⌟)
  : Type (o ⊔ r ⊔ o′ ⊔ r′)
  where
  no-eta-equality
  private
    module A = Poset A
    module M = Ordered-monoid-on M
  field
    identity : ∀ (a : ⌞ A ⌟) → α a M.ε ≡ a
    compat : ∀ (a : ⌞ A ⌟) (x y : ⌞ B ⌟) → α (α a x) y ≡ α a (x M.⊗ y)
    invariant : ∀ (a b : ⌞ A ⌟) (x : ⌞ B ⌟) → a A.≤ b → α a x A.≤ α b x
