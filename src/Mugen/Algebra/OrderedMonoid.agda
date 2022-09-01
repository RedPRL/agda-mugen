module Mugen.Algebra.OrderedMonoid where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Relation.Order

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

import Mugen.Data.Nat as Nat


private variable
  o r : Level
  A : Type o

--------------------------------------------------------------------------------
-- Ordered Monoids

record is-ordered-monoid {A : Type o} (_≤_ : A → A → Type r) (ε : A) (_⊗_ : A → A → A) : Type (o ⊔ r) where
  field
    has-monoid         : is-monoid ε _⊗_
    has-partial-order  : is-partial-order _≤_
    invariant          : ∀ {w x y z} → w ≤ y → x ≤ z → (w ⊗ x) ≤ (y ⊗ z)

  open is-monoid has-monoid public
  open is-partial-order has-partial-order public

  left-invariant : ∀ {x y z} → y ≤ z → (x ⊗ y) ≤ (x ⊗ z)
  left-invariant y≤z = invariant reflexive y≤z

  right-invariant : ∀ {x y z} → x ≤ y → (x ⊗ z) ≤ (y ⊗ z)
  right-invariant x≤y = invariant x≤y reflexive 

record OrderedMonoid-on {o : Level} (r : Level) (A : Type o) : Type (o ⊔ lsuc r) where
  field
    _≤_ : A → A → Type r
    ε : A
    _⊗_ : A → A → A
    has-ordered-monoid : is-ordered-monoid _≤_ ε _⊗_

  open is-ordered-monoid has-ordered-monoid public

OrderedMonoid : ∀ o r → Type (lsuc o ⊔ lsuc r)
OrderedMonoid o r = SetStructure (OrderedMonoid-on {o} r)

module OrderedMonoid {o r} (𝒟 : OrderedMonoid o r) where
  open OrderedMonoid-on (structure 𝒟) public

_[_≤_]ᵐ : (𝒟 : OrderedMonoid o r) → ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → Type r
𝒟 [ x ≤ y ]ᵐ = OrderedMonoid._≤_ 𝒟 x y

--------------------------------------------------------------------------------
-- Ordered Monoid Actions

record is-right-ordered-monoid-action {o r o′ r′} (A : StrictOrder o r) (B : OrderedMonoid o′ r′) (α : ⌞ A ⌟ → ⌞ B ⌟ → ⌞ A ⌟) : Type (o ⊔ r ⊔ o′ ⊔ r′) where
  open OrderedMonoid B
  field
    identity : ∀ (a : ⌞ A ⌟) → α a ε ≡ a
    compat : ∀ (a : ⌞ A ⌟) (x y : ⌞ B ⌟) → α (α a x) y ≡ α a (x ⊗ y)
    invariant : ∀ (a b : ⌞ A ⌟) (x : ⌞ B ⌟) → A [ a ≤ b ] → A [ α a x ≤ α b x ]

RightOrderedMonoidAction : ∀ {o r o′ r′} (A : StrictOrder o r) (B : OrderedMonoid o′ r′) → Type (o ⊔ r ⊔ o′ ⊔ r′) 
RightOrderedMonoidAction = RightAction is-right-ordered-monoid-action

module RightOrderedMonoidAction {o r o′ r′} {A : StrictOrder o r} {B : OrderedMonoid o′ r′} (α : RightOrderedMonoidAction A B) where
  open is-right-ordered-monoid-action (is-action α) public
