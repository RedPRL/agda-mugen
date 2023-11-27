module Mugen.Order.LeftInvariantRightCentered where

open import Mugen.Prelude
open import Mugen.Order.Poset

module _ {o r} (A B : Poset o r) (b : ⌞ B ⌟) where
  private
    module A = Poset A
    module B = Poset B

  data RawLeftInvariantRightCentered≤ (x y : ⌞ A ⌟ × ⌞ B ⌟) : Type (o ⊔ r) where
    biased : fst x ≡ fst y → snd x B.≤ snd y → RawLeftInvariantRightCentered≤ x y
    centred : fst x A.≤ fst y → snd x B.≤ b → b B.≤ snd y → RawLeftInvariantRightCentered≤ x y

  syntax RawLeftInvariantRightCentered≤ A B b x y = A ⋉[ b ] B [ x raw≤ y ]

  LeftInvariantRightCentered≤ : (x y : ⌞ A ⌟ × ⌞ B ⌟) → Type (o ⊔ r)
  LeftInvariantRightCentered≤ x y = ∥ RawLeftInvariantRightCentered≤ x y ∥

  syntax LeftInvariantRightCentered≤ A B b x y = A ⋉[ b ] B [ x ≤ y ]

module _ {o r} {A B : Poset o r} {b : ⌞ B ⌟} where
  private
    module A = Poset A
    module B = Poset B

  ⋉-thin : ∀ (x y : ⌞ A ⌟ × ⌞ B ⌟) → is-prop (A ⋉[ b ] B [ x ≤ y ])
  ⋉-thin x y = squash

  ⋉-refl : ∀ (x : ⌞ A ⌟ × ⌞ B ⌟) → A ⋉[ b ] B [ x ≤ x ]
  ⋉-refl (a , b1) = pure $ biased refl B.≤-refl

  ⋉-fst-invariant : ∀ {x y : ⌞ A ⌟ × ⌞ B ⌟} → A ⋉[ b ] B [ x ≤ y ] → fst x A.≤ fst y
  ⋉-fst-invariant = ∥-∥-rec A.≤-thin λ where
    (biased a1=a2 b1≤b2) → A.=→≤ a1=a2
    (centred a1≤a2 b1≤b b≤b2) → a1≤a2

  ⋉-snd-invariant : ∀ {x y : ⌞ A ⌟ × ⌞ B ⌟} → A ⋉[ b ] B [ x ≤ y ] → snd x B.≤ snd y
  ⋉-snd-invariant = ∥-∥-rec B.≤-thin λ where
    (biased a1=a2 b1≤b2) → b1≤b2
    (centred a1≤a2 b1≤b b≤b2) → B.≤-trans b1≤b b≤b2

  ⋉-trans : ∀ (x y z : ⌞ A ⌟ × ⌞ B ⌟) → A ⋉[ b ] B [ x ≤ y ] → A ⋉[ b ] B [ y ≤ z ] → A ⋉[ b ] B [ x ≤ z ]
  ⋉-trans x y z = ∥-∥-map₂ λ where
    (biased a1=a2 b1≤b2) (biased a2=a3 b2≤b3) → biased (a1=a2 ∙ a2=a3) (B.≤-trans b1≤b2 b2≤b3)
    (biased a1=a2 b1≤b2) (centred a2≤a3 b2≤b b≤b3) → centred (A.=+≤→≤ a1=a2 a2≤a3) (B.≤-trans b1≤b2 b2≤b) b≤b3
    (centred a1≤a2 b1≤b b≤b2) (biased a2=a3 b2≤b3) → centred (A.≤+=→≤ a1≤a2 a2=a3) b1≤b (B.≤-trans b≤b2 b2≤b3)
    (centred a1≤a2 b1≤b b≤b2) (centred a2≤a3 b2≤b b≤b3) → centred (A.≤-trans a1≤a2 a2≤a3) b1≤b b≤b3

  ⋉-antisym : ∀ (x y : ⌞ A ⌟ × ⌞ B ⌟) → A ⋉[ b ] B [ x ≤ y ] → A ⋉[ b ] B [ y ≤ x ] → x ≡ y
  ⋉-antisym x y = ∥-∥-rec₂ (×-is-hlevel 2 A.has-is-set B.has-is-set _ _) λ where
    (biased a1=a2 b1≤b2) (biased a2=a1 b2≤b1) →
      ap₂ _,_ a1=a2 (B.≤-antisym b1≤b2 b2≤b1)
    (biased a1=a2 b1≤b2) (centred a2≤a1 b2≤b b≤b1) →
      ap₂ _,_ a1=a2 (B.≤-antisym b1≤b2 $ B.≤-trans b2≤b b≤b1)
    (centred a1≤a2 b1≤b b≤b2) (biased a2=a1 b2≤b1) →
      ap₂ _,_ (sym a2=a1) (B.≤-antisym (B.≤-trans b1≤b b≤b2) b2≤b1)
    (centred a1≤a2 b1≤b b≤b2) (centred a2≤a1 b2≤b b≤b1) →
      ap₂ _,_ (A.≤-antisym a1≤a2 a2≤a1) (B.≤-antisym (B.≤-trans b1≤b b≤b2) (B.≤-trans b2≤b b≤b1))

LeftInvariantRightCentered : ∀ {o} → (A B : Poset o o) → ⌞ B ⌟ → Poset o o
LeftInvariantRightCentered A B b = to-poset order where
  module A = Poset A
  module B = Poset B

  order : make-poset _ (⌞ A ⌟ × ⌞ B ⌟)
  order .make-poset._≤_ x y = A ⋉[ b ] B [ x ≤ y ]
  order .make-poset.≤-thin = ⋉-thin _ _
  order .make-poset.≤-refl {x} = ⋉-refl x
  order .make-poset.≤-trans {x} {y} {z} = ⋉-trans x y z
  order .make-poset.≤-antisym {x} {y} = ⋉-antisym x y

syntax LeftInvariantRightCentered A B b = A ⋉[ b ] B
