
module Mugen.Order.LeftInvariantRightCentered where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

module _ {o r} (A B : Strict-order o r) (b : ⌞ B ⌟) where
  private
    module A = Strict-order A
    module B = Strict-order B

  data LeftInvariantRightCentered< (x y : ⌞ A ⌟ × ⌞ B ⌟) : Type (o ⊔ r) where
    biased : fst x ≡ fst y → snd x B.< snd y → LeftInvariantRightCentered< x y
    centred : fst x A.< fst y → snd x B.≤ b → b B.≤ snd y → LeftInvariantRightCentered< x y

  syntax LeftInvariantRightCentered< A B b x y = A ⋉[ b ] B [ x < y ]

module _ {o r} {A B : Strict-order o r} {b : ⌞ B ⌟} where
  private
    module A = Strict-order A
    module B = Strict-order B

  ⋉-irrefl : ∀ (x : ⌞ A ⌟ × ⌞ B ⌟) → A ⋉[ b ] B [ x < x ] → ⊥
  ⋉-irrefl (a , b1) (biased a1≡a2 b1<b1) = B.<-irrefl b1<b1
  ⋉-irrefl (a , b1) (centred a<a b1≤b b≤b2) = A.<-irrefl a<a

  ⋉-trans : ∀ (x y z : ⌞ A ⌟ × ⌞ B ⌟) → A ⋉[ b ] B [ x < y ] → A ⋉[ b ] B [ y < z ] → A ⋉[ b ] B [ x < z ]
  ⋉-trans x y z (biased a1≡a2 b1<b2) (biased a2≡a3 b2<b3) = biased (a1≡a2 ∙ a2≡a3) (B.<-trans b1<b2 b2<b3)
  ⋉-trans x y z (biased a1≡a2 b1<b2) (centred a2<a3 b2≤b b≤b3) = centred (A.≡+<→< a1≡a2 a2<a3) (B.≤-trans (B.<→≤ b1<b2) b2≤b) b≤b3
  ⋉-trans x y z (centred a1<a2 b1≤b b≤b2) (biased a2≡a3 b2<b3) = centred (A.<+≡→< a1<a2 a2≡a3) b1≤b (B.≤-trans b≤b2 (B.<→≤ b2<b3))
  ⋉-trans x y z (centred a1<a2 b1≤b b≤b2) (centred a2<a3 b2≤b b≤b3) = centred (A.<-trans a1<a2 a2<a3) b1≤b b≤b3

  ⋉-thin : ∀ (x y : ⌞ A ⌟ × ⌞ B ⌟) → is-prop (A ⋉[ b ] B [ x < y ])
  ⋉-thin x y (biased _ _) (biased _ _) = ap₂ biased (A.has-is-set _ _ _ _) (B.<-thin _ _)
  ⋉-thin x y (biased a1≡a2 _) (centred a1<a2 _ _) = absurd (A.<→≠ a1<a2 a1≡a2)
  ⋉-thin x y (centred a1<a2 _ _) (biased a1≡a2 _) = absurd (A.<→≠ a1<a2 a1≡a2)
  ⋉-thin x y (centred a1<a2 ≤b b≤) (centred a1<a2′ ≤b′ b≤′) i =
    centred (A.<-thin a1<a2 a1<a2′ i) (B.≤-thin ≤b ≤b′ i) (B.≤-thin b≤ b≤′ i)


LeftInvariantRightCentered : ∀ {o} → (A B : Strict-order o o) → ⌞ B ⌟ → Strict-order o o
LeftInvariantRightCentered A B b = to-strict-order order where
  module A = Strict-order A
  module B = Strict-order B

  order : make-strict-order _ (⌞ A ⌟ × ⌞ B ⌟)
  order .make-strict-order._<_ x y = A ⋉[ b ] B [ x < y ]
  order .make-strict-order.<-irrefl {x} = ⋉-irrefl x
  order .make-strict-order.<-trans {x} {y} {z} = ⋉-trans x y z
  order .make-strict-order.<-thin = ⋉-thin _ _
  order .make-strict-order.has-is-set = ×-is-hlevel 2 A.has-is-set B.has-is-set

syntax LeftInvariantRightCentered A B b = A ⋉[ b ] B
