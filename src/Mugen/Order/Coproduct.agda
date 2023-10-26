module Mugen.Order.Coproduct where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

-- NOTE: We require that both 'A' and 'B' live in the same universe
-- to avoid large amounts of 'Lift'. If you need to take the coproduct
-- of two strict orders that live in different universes, perform a lift
-- on the strict order before taking the coproduct.
module Strict-order-coproduct
  {o r}
  (A B : Strict-order o r)
  where
  private
    module A = Strict-order A
    module B = Strict-order B

  _⊕<_ : (⌞ A ⌟ ⊎ ⌞ B ⌟) → (⌞ A ⌟ ⊎ ⌞ B ⌟) → Type r
  inl x ⊕< inl y = x A.< y
  inl x ⊕< inr x₁ = Lift _ ⊥
  inr x ⊕< inl y = Lift _ ⊥
  inr x ⊕< inr y = x B.< y

  -- NOTE: This is equivalent to x ≡ y ⊎ x < y, but is much more convienent to work with.
  _⊕≤_ : (⌞ A ⌟ ⊎ ⌞ B ⌟) → (⌞ A ⌟ ⊎ ⌞ B ⌟) → Type (o ⊔ r)
  inl x ⊕≤ inl y = x A.≤ y
  inl x ⊕≤ inr y = Lift _ ⊥
  inr x ⊕≤ inl y = Lift _ ⊥
  inr x ⊕≤ inr y = x B.≤ y 

  from-⊕≤ : (x y : ⌞ A ⌟ ⊎ ⌞ B ⌟) → x ⊕≤ y → non-strict _⊕<_ x y
  from-⊕≤ (inl x) (inl y) (inl x≡y) = inl (ap inl x≡y)
  from-⊕≤ (inl x) (inl y) (inr x<y) = inr x<y
  from-⊕≤ (inr x) (inr y) (inl x≡y) = inl (ap inr x≡y)
  from-⊕≤ (inr x) (inr y) (inr x<y) = inr x<y

  to-⊕≤ : ∀ (x y : ⌞ A ⌟ ⊎ ⌞ B ⌟) → non-strict _⊕<_ x y → x ⊕≤ y
  to-⊕≤ (inl x) (inl y) (inl x≡y) = inl (inl-inj x≡y)
  to-⊕≤ (inl x) (inl y) (inr x<y) = inr x<y
  to-⊕≤ (inl x) (inr y) (inl x≡y) = lift (⊎-disjoint x≡y)
  to-⊕≤ (inr x) (inl y) (inl x≡y) = lift (⊎-disjoint (sym x≡y))
  to-⊕≤ (inr x) (inr y) (inl x≡y) = inl (inr-inj x≡y)
  to-⊕≤ (inr x) (inr y) (inr x<y) = inr x<y

  ⊕<-irrefl : ∀ x → x ⊕< x → ⊥
  ⊕<-irrefl (inl x) = A.<-irrefl
  ⊕<-irrefl (inr x) = B.<-irrefl

  ⊕<-trans : ∀ x y z → x ⊕< y → y ⊕< z → x ⊕< z
  ⊕<-trans (inl x) (inl y) (inl z) p q = A.<-trans p q
  ⊕<-trans (inr x) (inr y) (inr z) p q = B.<-trans p q

  ⊕<-thin : ∀ x y → is-prop (x ⊕< y)
  ⊕<-thin (inl _) (inl _) = A.<-thin
  ⊕<-thin (inl _) (inr _) = hlevel 1
  ⊕<-thin (inr x) (inl _) = hlevel 1
  ⊕<-thin (inr x) (inr _) = B.<-thin

  ⊕<-is-strict-order : is-strict-order _⊕<_
  ⊕<-is-strict-order .is-strict-order.<-irrefl {x} = ⊕<-irrefl x
  ⊕<-is-strict-order .is-strict-order.<-trans {x} {y} {z} = ⊕<-trans x y z
  ⊕<-is-strict-order .is-strict-order.<-thin {x} {y} = ⊕<-thin x y
  ⊕<-is-strict-order .is-strict-order.has-is-set = ⊎-is-hlevel 0 A.has-is-set B.has-is-set

module _ {o r} (A B : Strict-order o r) where
  private
    module A = Strict-order A
    module B = Strict-order B
  open Strict-order-coproduct A B

  _⊕_ : Strict-order o r
  _⊕_ .Strict-order.Ob =  ⌞ A ⌟ ⊎ ⌞ B ⌟
  .Strict-order.strict-order-on ⊕ .Strict-order-on._<_ = _⊕<_
  .Strict-order.strict-order-on ⊕ .Strict-order-on.has-is-strict-order = ⊕<-is-strict-order
