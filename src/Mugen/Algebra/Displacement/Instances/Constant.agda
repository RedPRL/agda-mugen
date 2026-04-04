module Mugen.Algebra.Displacement.Instances.Constant where

open import Order.Instances.Coproduct
open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Action
open import Mugen.Algebra.OrderedMonoid

import Mugen.Order.Reasoning as Reasoning

--------------------------------------------------------------------------------
-- Constant Displacements
-- Section 3.3.2
--
-- Given a strict order 'A', a displacement algebra 'B', and a right displacement
-- action 'α : A → B → A', we can construct a displacement algebra whose carrier
-- is 'A ⊎ B'. Multiplication of an 'inl a' and 'inr b' uses the 'α' to have
-- 'b' act upon 'a'.

Constant
  : ∀ {o r} {A B : Poset o r} {Y : Displacement-on B}
  → Right-displacement-action A Y
  → Displacement-on (A ⊎ᵖ B)
Constant {A = A} {B = B} {Y = Y} α = to-displacement-on mk where
  module A = Poset A
  module B = Reasoning B
  module Y = Displacement-on Y
  module α = Right-displacement-action α
  open Reasoning (A ⊎ᵖ B)

  _⊗_ : ⌞ A ⌟ ⊎ ⌞ B ⌟ → ⌞ A ⌟ ⊎ ⌞ B ⌟ → ⌞ A ⌟ ⊎ ⌞ B ⌟
  _ ⊗ inl a = inl a
  inl a ⊗ inr x = inl (⟦ α ⟧ʳ a x)
  inr x ⊗ inr y = inr (x Y.⊗ y)

  ε : ⌞ A ⌟ ⊎ ⌞ B ⌟
  ε = inr Y.ε

  associative : ∀ (x y z : ⌞ A ⌟ ⊎ ⌞ B ⌟) → (x ⊗ (y ⊗ z)) ≡ ((x ⊗ y) ⊗ z)
  associative _ _ (inl _) = refl
  associative _ (inl _) (inr _) = refl
  associative (inl a) (inr y) (inr z) = ap inl α.compatible
  associative (inr x) (inr y) (inr z) = ap inr Y.associative

  idl : ∀ (x : ⌞ A ⌟ ⊎ ⌞ B ⌟) → (ε ⊗ x) ≡ x
  idl (inl x) = refl
  idl (inr x) = ap inr Y.idl

  idr : ∀ (x : ⌞ A ⌟ ⊎ ⌞ B ⌟) → (x ⊗ ε) ≡ x
  idr (inl x) = ap inl α.identity
  idr (inr x) = ap inr Y.idr

  left-invariant : ∀ (x y z : ⌞ A ⌟ ⊎ ⌞ B ⌟) → y ≤ z → (x ⊗ y) ≤ (x ⊗ z)
  left-invariant _ (inl y) (inl z) y≤z = y≤z
  left-invariant (inl x) (inr y) (inr z) (lift y≤z) = lift $ α.invariant y≤z
  left-invariant (inr x) (inr y) (inr z) (lift y≤z) = lift $ Y.left-invariant y≤z

  injectiver-on-related : ∀ (x y z : ⌞ A ⌟ ⊎ ⌞ B ⌟) → y ≤ z → (x ⊗ y) ≡ (x ⊗ z) → y ≡ z
  injectiver-on-related _ (inl y) (inl z) _ p = p
  injectiver-on-related (inl x) (inr y) (inr z) (lift y≤z) p =
    ap inr $ α.injectiver-on-related y≤z (inl-inj p)
  injectiver-on-related (inr x) (inr y) (inr z) (lift y≤z) p =
    ap inr $ Y.injectiver-on-related y≤z (inr-inj p)

  mk : make-displacement (A ⊎ᵖ B)
  mk .make-displacement.ε = ε
  mk .make-displacement._⊗_ = _⊗_
  mk .make-displacement.idl {x} = idl x
  mk .make-displacement.idr {x} = idr x
  mk .make-displacement.associative {x} {y} {z} = associative x y z
  mk .make-displacement.left-strict-invariant {x} {y} {z} p .fst = left-invariant x y z p
  mk .make-displacement.left-strict-invariant {x} {y} {z} p .snd = injectiver-on-related x y z p

module _
  {o r} {A B : Poset o r} {Y : Displacement-on B}
  (α : Right-displacement-action A Y) where
  private
    module A = Poset A
    module B = Poset B
    module Y = Displacement-on Y
    open Reasoning (A ⊎ᵖ B)
    open Displacement-on (Constant α)

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  Constant-has-ordered-monoid
    : has-ordered-monoid Y
    → (∀ {x y : ⌞ A ⌟} {z : ⌞ B ⌟} → x A.≤ y → ⟦ α ⟧ʳ x z A.≤ ⟦ α ⟧ʳ y z)
    → has-ordered-monoid (Constant α)
  Constant-has-ordered-monoid B-ordered-monoid α-right-invariant =
    let module B-ordered-monoid = is-ordered-monoid B-ordered-monoid in
    right-invariant→has-ordered-monoid (Constant α) λ where
      {x} {y} {inl z} x≤y → ≤-refl {inl z}
      {inl x} {inl y} {inr z} (lift x≤y) → lift $ α-right-invariant x≤y
      {inr x} {inr y} {inr z} (lift x≤y) → lift $ B-ordered-monoid.right-invariant x≤y
