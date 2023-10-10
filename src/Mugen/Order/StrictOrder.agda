module Mugen.Order.StrictOrder where

open import Order.Base
open import Mugen.Prelude

--------------------------------------------------------------------------------
-- Strict Orders

non-strict : ∀ {o r} {A : Type o} (R : A → A → Type r) → A → A → Type (o ⊔ r)
non-strict R x y = x ≡ y ⊎ (R x y)

record is-strict-order {o r} {A : Type o} (_<_ : A → A → Type r) : Type (o ⊔ r) where
  no-eta-equality
  field
    <-irrefl : ∀ {x} → x < x → ⊥
    <-trans : ∀ {x y z} → x < y → y < z → x < z
    <-thin : ∀ {x y} → is-prop (x < y)
    has-set : is-set A

  <-asym : ∀ {x y} → x < y → y < x → ⊥
  <-asym x<y y<x = <-irrefl (<-trans x<y y<x)

  _≤_ : A → A → Type (o ⊔ r)
  x ≤ y = non-strict _<_ x y

  instance
    <-hlevel : ∀ {x y} {n} → H-Level (x < y) (suc n)
    <-hlevel = prop-instance <-thin

  ≡-transl : ∀ {x y z} → x ≡ y → y < z → x < z
  ≡-transl x≡y y<z = subst (λ ϕ → ϕ < _) (sym x≡y) y<z

  ≡-transr : ∀ {x y z} → x < y → y ≡ z → x < z
  ≡-transr x<y y≡z = subst (λ ϕ → _ < ϕ) y≡z x<y

  ≤-transl : ∀ {x y z} → x ≤ y → y < z → x < z
  ≤-transl (inl x≡y) y<z = ≡-transl x≡y y<z
  ≤-transl (inr x<y) y<z = <-trans x<y y<z

  ≤-transr : ∀ {x y z} → x < y → y ≤ z → x < z
  ≤-transr x<y (inl y≡z) = ≡-transr x<y y≡z
  ≤-transr x<y (inr y<z) = <-trans x<y y<z

  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans (inl p) (inl q) = inl (p ∙ q)
  ≤-trans (inl p) (inr y<z) = inr (≡-transl p y<z)
  ≤-trans (inr x<y) (inl q) = inr (≡-transr x<y q)
  ≤-trans (inr x<y) (inr y<z) = inr (<-trans x<y y<z)

  ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
  ≤-antisym (inl x≡y) y≤x = x≡y
  ≤-antisym (inr x<y) (inl y≡x) = sym y≡x
  ≤-antisym (inr x<y) (inr y<x) = absurd (<-irrefl (<-trans x<y y<x))

  <→≤ : ∀ {x y} → x < y → x ≤ y
  <→≤ x<y = inr x<y

  ≤-refl : ∀ {x} → x ≤ x
  ≤-refl = inl refl

  ≤-thin : ∀ {x y} → is-prop (x ≤ y)
  ≤-thin =
    disjoint-⊎-is-prop (has-set _ _) <-thin
      (λ (p , q) → <-irrefl (≡-transl (sym p) q))


instance
  is-strict-order-hlevel : ∀ {o r} {A : Type o} {_<_ : A → A → Type r} {n}
                           → H-Level (is-strict-order _<_) (suc n)
  is-strict-order-hlevel = prop-instance λ x →
     let open is-strict-order x in
     is-hlevel≃ 1 (Iso→Equiv eqv) hlevel! x
     where unquoteDecl eqv = declare-record-iso eqv (quote is-strict-order)

record Strict-order-on {o : Level} (r : Level) (A : Type o) : Type (o ⊔ lsuc r) where
  no-eta-equality
  field
    _<_ : A → A → Type r
    has-is-strict-order : is-strict-order _<_

  open is-strict-order has-is-strict-order public

record Strict-order (o r : Level) : Type (lsuc (o ⊔ r)) where
  no-eta-equality
  field
    Ob : Type o
    strict-order : Strict-order-on r Ob

  open Strict-order-on strict-order public

instance
  Underlying-Strict-order : ∀ {o r} → Underlying (Strict-order o r)
  Underlying-Strict-order .Underlying.ℓ-underlying = _
  Underlying.⌞ Underlying-Strict-order ⌟ = Strict-order.Ob

private variable
  o r : Level
  X Y Z : Strict-order o r

--------------------------------------------------------------------------------
-- Strictly Monotonic Maps

module _ {o r o' r'} {X : Strict-order o r} {Y : Strict-order o' r'} where
  private
    module X = Strict-order X
    module Y = Strict-order Y

  strictly-monotonic : ∀ (f : ⌞ X ⌟ → ⌞ Y ⌟) → Type (o ⊔ r ⊔ r') 
  strictly-monotonic f = ∀ {x y} →  x X.< y → f x Y.< f y

  strictly-monotonic-is-prop : ∀ (f : ⌞ X ⌟ → ⌞ Y ⌟) → is-prop (strictly-monotonic f)
  strictly-monotonic-is-prop f = hlevel!

record Strictly-monotone
  {o o' r r'}
  (X : Strict-order o r) (Y : Strict-order o' r')
  : Type (o ⊔ o' ⊔ r ⊔ r') 
  where
  no-eta-equality
  private
    module X = Strict-order X
    module Y = Strict-order Y
  field
    hom : ⌞ X ⌟ → ⌞ Y ⌟
    strict-mono : ∀ {x y} → x X.< y → hom x Y.< hom y

  mono : ∀ {x y} → x X.≤ y → hom x Y.≤ hom y
  mono (inl p) = inl (ap hom p)
  mono (inr p) = inr (strict-mono p)

module _ {o r o' r'} {X : Strict-order o r} {Y : Strict-order o' r'} where
  private
    module X = Strict-order X
    module Y = Strict-order Y

  instance
    strict-order-hlevel : ∀ {n} → H-Level (Strictly-monotone X Y) (2 + n)
    strict-order-hlevel = basic-instance 2 $
      Iso→is-hlevel 2 eqv $
      Σ-is-hlevel 2 (Π-is-hlevel 2 λ _ → Y.has-set) λ f →
      is-hlevel-suc 1 (strictly-monotonic-is-prop {X = X} {Y = Y} f)
      where unquoteDecl eqv = declare-record-iso eqv (quote Strictly-monotone) 
