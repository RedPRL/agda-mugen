module Mugen.Algebra.Displacement.Constant where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude hiding (Const)
open import Mugen.Order.StrictOrder
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

module Constant {o r} {A : StrictOrder o r} {B : DisplacementAlgebra o r} (α : RightDisplacementAction A B) where
  private
    module A = StrictOrder-on (structure A)
    module B = DisplacementAlgebra-on (structure B)
    module α = RightDisplacementAction α

    open B using (ε; _⊗_)


  _≤α_ : ⌞ A ⌟ ⊎ ⌞ B ⌟ → ⌞ A ⌟ ⊎ ⌞ B ⌟ → Type (o ⊔ r)
  x ≤α y = A ⊕ DA→SO B [ x ≤ y ]

  _⊗α_ : ⌞ A ⌟ ⊎ ⌞ B ⌟ → ⌞ A ⌟ ⊎ ⌞ B ⌟ → ⌞ A ⌟ ⊎ ⌞ B ⌟
  inr x ⊗α inr y = inr (x ⊗ y)
  inl a ⊗α inr x = inl (⟦ α ⟧ʳ a x)
  inr _ ⊗α inl a = inl a
  inl _ ⊗α inl a = inl a

  εα : ⌞ A ⌟ ⊎ ⌞ B ⌟
  εα = inr ε

  ⊗α-associative : ∀ (x y z : ⌞ A ⌟ ⊎ ⌞ B ⌟) → (x ⊗α (y ⊗α z)) ≡ ((x ⊗α y) ⊗α z)
  ⊗α-associative (inl a) (inl b) (inl c) = refl
  ⊗α-associative (inl a) (inl b) (inr z) = refl
  ⊗α-associative (inl a) (inr y) (inl c) = refl
  ⊗α-associative (inl a) (inr y) (inr z) = ap inl (sym (α.compat a y z))
  ⊗α-associative (inr x) (inl b) (inl c) = refl
  ⊗α-associative (inr x) (inl b) (inr z) = refl
  ⊗α-associative (inr x) (inr y) (inl c) = refl
  ⊗α-associative (inr x) (inr y) (inr z) = ap inr B.associative

  ⊗α-idl : ∀ (x : ⌞ A ⌟ ⊎ ⌞ B ⌟) → (εα ⊗α x) ≡ x
  ⊗α-idl (inl x) = refl
  ⊗α-idl (inr x) = ap inr B.idl

  ⊗α-idr : ∀ (x : ⌞ A ⌟ ⊎ ⌞ B ⌟) → (x ⊗α εα) ≡ x
  ⊗α-idr (inl x) = ap inl (α.identity x)
  ⊗α-idr (inr x) = ap inr B.idr

  --------------------------------------------------------------------------------
  -- Algebra

  ⊗α-is-magma : is-magma _⊗α_
  ⊗α-is-magma .has-is-set = ⊎-is-hlevel 0 ⌞ A ⌟-set ⌞ B ⌟-set

  ⊗α-is-semigroup : is-semigroup _⊗α_
  ⊗α-is-semigroup .has-is-magma = ⊗α-is-magma
  ⊗α-is-semigroup .associative {x} {y} {z} = ⊗α-associative x y z

  ⊗α-is-monoid : is-monoid εα _⊗α_
  ⊗α-is-monoid .has-is-semigroup = ⊗α-is-semigroup
  ⊗α-is-monoid .idl {x} = ⊗α-idl x
  ⊗α-is-monoid .idr {x} = ⊗α-idr x

  --------------------------------------------------------------------------------
  -- Ordering
  --
  -- This uses the coproduct of strict orders, so we can re-use proofs from there.

  _<α_ : ⌞ A ⌟ ⊎ ⌞ B ⌟ → ⌞ A ⌟ ⊎ ⌞ B ⌟ → Type r
  x <α y = A ⊕ DA→SO B [ x < y ]

  --------------------------------------------------------------------------------
  -- Left Invariance

  ⊗α-left-invariant : ∀ (x y z : ⌞ A ⌟ ⊎ ⌞ B ⌟) → y <α z → (x ⊗α y) <α (x ⊗α z)
  ⊗α-left-invariant (inl x) (inl y) (inl z) y<z = y<z
  ⊗α-left-invariant (inl x) (inr y) (inr z) y<z = α.invariant x y z y<z
  ⊗α-left-invariant (inr x) (inl y) (inl z) y<z = y<z
  ⊗α-left-invariant (inr x) (inr y) (inr z) y<z = B.left-invariant y<z

  ⊗α-is-displacement-algebra : is-displacement-algebra _<α_ εα _⊗α_
  ⊗α-is-displacement-algebra .is-displacement-algebra.has-monoid = ⊗α-is-monoid
  ⊗α-is-displacement-algebra .is-displacement-algebra.has-strict-order = ⊕-is-strict-order A (DA→SO B)
  ⊗α-is-displacement-algebra .is-displacement-algebra.left-invariant {x} {y} {z} = ⊗α-left-invariant x y z

Const : ∀ {o r} {A : StrictOrder o r} {B : DisplacementAlgebra o r} → RightDisplacementAction A B → DisplacementAlgebra o r
Const {A = A} {B = B} α = displacement
  where
    open Constant α

    displacement : DisplacementAlgebra _ _
    ⌞ displacement ⌟ =  ⌞ A ⌟ ⊎ ⌞ B ⌟
    displacement .structure .DisplacementAlgebra-on._<_ = _<α_
    displacement .structure .DisplacementAlgebra-on.ε = εα
    displacement .structure .DisplacementAlgebra-on._⊗_ = _⊗α_
    displacement .structure .DisplacementAlgebra-on.has-displacement-algebra = ⊗α-is-displacement-algebra
    ⌞ displacement ⌟-set = ⊎-is-hlevel 0 ⌞ A ⌟-set ⌞ B ⌟-set

module ConstantProperties {o r} {A : StrictOrder o r} {B : DisplacementAlgebra o r} (α : RightDisplacementAction A B) where
  private
    module A = StrictOrder A
    module B = DisplacementAlgebra B
    open B using (ε; _⊗_)

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  ⊗α-is-ordered-monoid : has-ordered-monoid B → (∀ {x y z} → A [ x ≤ y ] → A [ ⟦ α ⟧ʳ x z ≤ ⟦ α ⟧ʳ y z ]) → has-ordered-monoid (Const α)
  ⊗α-is-ordered-monoid B-ordered-monoid α-right-invariant =
    right-invariant→has-ordered-monoid (Const α) (λ x≤y → from-⊕≤ _ _ (⊗α-right-invariant _ _ _ (to-⊕≤ _ _ x≤y)))
    where
      open Constant α
      module B-ordered-monoid = is-ordered-monoid (B-ordered-monoid)

      ⊗α-right-invariant : ∀ x y z → x ≤α y → (x ⊗α z) ≤α (y ⊗α z)
      ⊗α-right-invariant (inl x) (inl y) (inl z) x≤y = inl refl
      ⊗α-right-invariant (inl x) (inl y) (inr z) x≤y = α-right-invariant x≤y
      ⊗α-right-invariant (inr x) (inr y) (inl z) x≤y = inl refl
      ⊗α-right-invariant (inr x) (inr y) (inr z) x≤y = B-ordered-monoid.right-invariant x≤y
