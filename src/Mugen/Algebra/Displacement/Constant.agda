module Mugen.Algebra.Displacement.Constant where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude hiding (Const)
open import Mugen.Order.Poset
open import Mugen.Order.Coproduct

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid

--------------------------------------------------------------------------------
-- Constant Displacements
-- Section 3.3.2
--
-- Given a strict order 'A', a displacement algebra 'B', and a right displacement
-- action 'α : A → B → A', we can construct a displacement algebra whose carrier
-- is 'A ⊎ B'. Multiplication of an 'inl a' and 'inr b' uses the 'α' to have
-- 'b' act upon 'a'.

module Constant
  {o r} {A : Poset o r} {B : Displacement-algebra o r}
  (α : Right-displacement-action A B) where
  private
    module A = Poset A
    module B = Displacement-algebra B
    module α = Right-displacement-action α
    open Poset-coproduct A B.poset

  _⊗α_ : ⌞ A ⌟ ⊎ ⌞ B ⌟ → ⌞ A ⌟ ⊎ ⌞ B ⌟ → ⌞ A ⌟ ⊎ ⌞ B ⌟
  _ ⊗α inl a = inl a
  inl a ⊗α inr x = inl (⟦ α ⟧ʳ a x)
  inr x ⊗α inr y = inr (x B.⊗ y)

  εα : ⌞ A ⌟ ⊎ ⌞ B ⌟
  εα = inr B.ε

  ⊗α-associative : ∀ (x y z : ⌞ A ⌟ ⊎ ⌞ B ⌟) → (x ⊗α (y ⊗α z)) ≡ ((x ⊗α y) ⊗α z)
  ⊗α-associative _ _ (inl _) = refl
  ⊗α-associative _ (inl _) (inr _) = refl
  ⊗α-associative (inl a) (inr y) (inr z) = ap inl (sym (α.compat a y z))
  ⊗α-associative (inr x) (inr y) (inr z) = ap inr B.associative

  ⊗α-idl : ∀ (x : ⌞ A ⌟ ⊎ ⌞ B ⌟) → (εα ⊗α x) ≡ x
  ⊗α-idl (inl x) = refl
  ⊗α-idl (inr x) = ap inr B.idl

  ⊗α-idr : ∀ (x : ⌞ A ⌟ ⊎ ⌞ B ⌟) → (x ⊗α εα) ≡ x
  ⊗α-idr (inl x) = ap inl (α.identity x)
  ⊗α-idr (inr x) = ap inr B.idr

  --------------------------------------------------------------------------------
  -- Ordering
  --
  -- This uses the coproduct of strict orders, so we can re-use proofs from there.

  _≤α_ : ⌞ A ⌟ ⊎ ⌞ B ⌟ → ⌞ A ⌟ ⊎ ⌞ B ⌟ → Type r
  x ≤α y = x ⊕≤ y

  _<α_ : ⌞ A ⌟ ⊎ ⌞ B ⌟ → ⌞ A ⌟ ⊎ ⌞ B ⌟ → Type (o ⊔ r)
  _<α_ = strict _≤α_

  --------------------------------------------------------------------------------
  -- Left Invariance

  ⊗α-left-invariant : ∀ (x y z : ⌞ A ⌟ ⊎ ⌞ B ⌟) → y ≤α z → (x ⊗α y) ≤α (x ⊗α z)
  ⊗α-left-invariant _ (inl y) (inl z) y≤z = y≤z
  ⊗α-left-invariant (inl x) (inr y) (inr z) y≤z = α.invariant x y z y≤z
  ⊗α-left-invariant (inr x) (inr y) (inr z) y≤z = B.left-invariant y≤z

  ⊗α-injr-on-≤α : ∀ (x y z : ⌞ A ⌟ ⊎ ⌞ B ⌟) → y ≤α z → (x ⊗α y) ≡ (x ⊗α z) → y ≡ z
  ⊗α-injr-on-≤α _ (inl y) (inl z) _ p = p
  ⊗α-injr-on-≤α (inl x) (inr y) (inr z) y≤z p =
    ap inr $ α.injr-on-related x y z y≤z (inl-inj p)
  ⊗α-injr-on-≤α (inr x) (inr y) (inr z) y≤z p =
    ap inr $ B.injr-on-related y≤z (inr-inj p)

Const
  : ∀ {o r} {A : Poset o r} {B : Displacement-algebra o r}
  → Right-displacement-action A B
  → Displacement-algebra o r
Const {A = A} {B = B} α = to-displacement-algebra mk where
  module A = Poset A
  module B = Displacement-algebra B
  open Constant α
  open make-displacement-algebra

  mk : make-displacement-algebra (A ⊕ B.poset)
  mk .ε = εα
  mk ._⊗_ = _⊗α_
  mk .idl {x} = ⊗α-idl x
  mk .idr {x} = ⊗α-idr x
  mk .associative {x} {y} {z} = ⊗α-associative x y z
  mk .left-strict-invariant {x} {y} {z} p =
    ⊗α-left-invariant x y z p , ⊗α-injr-on-≤α x y z p

module ConstantProperties
  {o r}
  {A : Poset o r} {B : Displacement-algebra o r}
  (α : Right-displacement-action A B) where
  private
    module A = Poset A
    module B = Displacement-algebra B
    open Poset-coproduct A B.poset
    open B using (ε; _⊗_)

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  ⊗α-is-ordered-monoid
    : has-ordered-monoid B
    → (∀ {x y : ⌞ A ⌟} {z : ⌞ B ⌟} → x A.≤ y → ⟦ α ⟧ʳ x z A.≤ ⟦ α ⟧ʳ y z)
    → has-ordered-monoid (Const α)
  ⊗α-is-ordered-monoid B-ordered-monoid α-right-invariant =
    right-invariant→has-ordered-monoid (Const α) λ {x} {y} {z} x≤y →
      ≤α-right-invariant x y z x≤y
    where
      open Constant α
      module B-ordered-monoid = is-ordered-monoid (B-ordered-monoid)

      ≤α-right-invariant : ∀ x y z → x ≤α y → (x ⊗α z) ≤α (y ⊗α z)
      ≤α-right-invariant x y (inl z) x≤y = ⊕≤-refl (inl z)
      ≤α-right-invariant (inl x) (inl y) (inr z) x≤y = α-right-invariant x≤y
      ≤α-right-invariant (inr x) (inr y) (inr z) x≤y = B-ordered-monoid.right-invariant x≤y
