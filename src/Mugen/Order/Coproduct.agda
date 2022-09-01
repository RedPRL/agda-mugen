module Mugen.Order.Coproduct where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

_⊕_[_<_] : ∀ {o r} (A B : StrictOrder o r) → (x y : ⌞ A ⌟ ⊎ ⌞ B ⌟) → Type r
A ⊕ B [ inl x < inl y ] = A [ x < y ]
A ⊕ B [ inl _ < inr _ ] = Lift _ ⊥
A ⊕ B [ inr _ < inl _ ] = Lift _ ⊥
A ⊕ B [ inr x < inr y ] = B [ x < y ]

-- NOTE: This is equivalent to x ≡ y ⊎ x < y, but is much more convienent to work with.
_⊕_[_≤_] : ∀ {o r} (A B : StrictOrder o r) → (x y : ⌞ A ⌟ ⊎ ⌞ B ⌟) → Type (o ⊔ r)
A ⊕ B [ inl x ≤ inl y ] = A [ x ≤ y ]
A ⊕ B [ inl _ ≤ inr _ ] = Lift _ ⊥
A ⊕ B [ inr _ ≤ inl _ ] = Lift _ ⊥
A ⊕ B [ inr x ≤ inr y ] = B [ x ≤ y ]

from-⊕≤ : ∀ {o r} {A B : StrictOrder o r} (x y : ⌞ A ⌟ ⊎ ⌞ B ⌟) → A ⊕ B [ x ≤ y ] → (x ≡ y) ⊎ (A ⊕ B [ x < y ])
from-⊕≤ (inl x) (inl y) (inl x≡y) = inl (ap inl x≡y)
from-⊕≤ (inl x) (inl y) (inr x<y) = inr x<y
from-⊕≤ (inr x) (inr y) (inl x≡y) = inl (ap inr x≡y)
from-⊕≤ (inr x) (inr y) (inr x<y) = inr x<y

to-⊕≤ : ∀ {o r} {A B : StrictOrder o r} (x y : ⌞ A ⌟ ⊎ ⌞ B ⌟) → (x ≡ y) ⊎ (A ⊕ B [ x < y ]) → A ⊕ B [ x ≤ y ]
to-⊕≤ (inl x) (inl y) (inl x≡y) = inl (inl-inj x≡y)
to-⊕≤ (inl x) (inl y) (inr x<y) = inr x<y
to-⊕≤ (inl x) (inr y) (inl x≡y) = lift (⊎-disjoint x≡y)
to-⊕≤ (inr x) (inl y) (inl x≡y) = lift (⊎-disjoint (sym x≡y))
to-⊕≤ (inr x) (inr y) (inl x≡y) = inl (inr-inj x≡y)
to-⊕≤ (inr x) (inr y) (inr x<y) = inr x<y

module _ {o r} (A B : StrictOrder o r) where
  private
    module A = StrictOrder-on (structure A)
    module B = StrictOrder-on (structure B)

  ⊕-irrefl : ∀ (x : ⌞ A ⌟ ⊎ ⌞ B ⌟) → A ⊕ B [ x < x ] → ⊥
  ⊕-irrefl (inl x) = A.irrefl
  ⊕-irrefl (inr x) = B.irrefl

  ⊕-trans : ∀ (x y z : ⌞ A ⌟ ⊎ ⌞ B ⌟) → A ⊕ B [ x < y ] → A ⊕ B [ y < z ] → A ⊕ B [ x < z ]
  ⊕-trans (inl x) (inl y) (inl z) x<y y<z = A.trans x<y y<z
  ⊕-trans (inr x) (inr y) (inr z) x<y y<z = B.trans x<y y<z

  ⊕-is-prop : ∀ (x y : ⌞ A ⌟ ⊎ ⌞ B ⌟) → is-prop (A ⊕ B [ x < y ])
  ⊕-is-prop (inl _) (inl _) = A.has-prop
  ⊕-is-prop (inl _) (inr _) = hlevel 1
  ⊕-is-prop (inr x) (inl _) = hlevel 1
  ⊕-is-prop (inr x) (inr _) = B.has-prop

  ⊕-is-strict-order : is-strict-order (A ⊕ B [_<_])
  ⊕-is-strict-order .is-strict-order.irrefl {x} = ⊕-irrefl x
  ⊕-is-strict-order .is-strict-order.trans {x} {y} {z} = ⊕-trans x y z
  ⊕-is-strict-order .is-strict-order.has-prop {x} {y} = ⊕-is-prop x y

_⊕_ : ∀ {o r} → StrictOrder o r → StrictOrder o r → StrictOrder o r
⌞ X ⊕ Y ⌟ = ⌞ X ⌟ ⊎ ⌞ Y ⌟
(X ⊕ Y) .structure .StrictOrder-on._<_ = X ⊕ Y [_<_]
(X ⊕ Y) .structure .StrictOrder-on.has-is-strict-order = ⊕-is-strict-order X Y
⌞ X ⊕ Y ⌟-set =
  ⊎-is-hlevel 0 ⌞ X ⌟-set ⌞ Y ⌟-set
