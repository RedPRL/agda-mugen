module Mugen.Order.Instances.LeftInvariantRightCentered where

open import Mugen.Prelude

import Mugen.Order.Reasoning as Reasoning

module _ {o o' r r'} (A : Poset o r) (B : Poset o' r') (b : ⌞ B ⌟) where
  private
    module A = Reasoning A
    module B = Reasoning B

  data RawLeftInvariantRightCentered≤ (x y : ⌞ A ⌟ × ⌞ B ⌟) : Type (o ⊔ r ⊔ r') where
    biased : fst x ≡ fst y → snd x B.≤ snd y → RawLeftInvariantRightCentered≤ x y
    centred : fst x A.≤ fst y → snd x B.≤ b → b B.≤ snd y → RawLeftInvariantRightCentered≤ x y

  LeftInvariantRightCentered≤ : (x y : ⌞ A ⌟ × ⌞ B ⌟) → Type (o ⊔ r ⊔ r')
  LeftInvariantRightCentered≤ x y = ∥ RawLeftInvariantRightCentered≤ x y ∥

  private
    ⋉-thin : ∀ (x y : ⌞ A ⌟ × ⌞ B ⌟) → is-prop (LeftInvariantRightCentered≤ x y)
    ⋉-thin x y = squash

    ⋉-refl : ∀ (x : ⌞ A ⌟ × ⌞ B ⌟) → LeftInvariantRightCentered≤ x x
    ⋉-refl (a , b1) = pure $ biased refl B.≤-refl

    ⋉-trans : ∀ (x y z : ⌞ A ⌟ × ⌞ B ⌟)
      → LeftInvariantRightCentered≤ x y
      → LeftInvariantRightCentered≤ y z
      → LeftInvariantRightCentered≤ x z
    ⋉-trans x y z = ∥-∥-map₂ λ where
      (biased a1=a2 b1≤b2) (biased a2=a3 b2≤b3) → biased (a1=a2 ∙ a2=a3) (B.≤-trans b1≤b2 b2≤b3)
      (biased a1=a2 b1≤b2) (centred a2≤a3 b2≤b b≤b3) → centred (A.=+≤→≤ a1=a2 a2≤a3) (B.≤-trans b1≤b2 b2≤b) b≤b3
      (centred a1≤a2 b1≤b b≤b2) (biased a2=a3 b2≤b3) → centred (A.≤+=→≤ a1≤a2 a2=a3) b1≤b (B.≤-trans b≤b2 b2≤b3)
      (centred a1≤a2 b1≤b b≤b2) (centred a2≤a3 b2≤b b≤b3) → centred (A.≤-trans a1≤a2 a2≤a3) b1≤b b≤b3

    ⋉-antisym : ∀ (x y : ⌞ A ⌟ × ⌞ B ⌟)
      → LeftInvariantRightCentered≤ x y
      → LeftInvariantRightCentered≤ y x
      → x ≡ y
    ⋉-antisym x y = ∥-∥-rec₂ (×-is-hlevel 2 A.Ob-is-set B.Ob-is-set _ _) λ where
      (biased a1=a2 b1≤b2) (biased a2=a1 b2≤b1) →
        ap₂ _,_ a1=a2 (B.≤-antisym b1≤b2 b2≤b1)
      (biased a1=a2 b1≤b2) (centred a2≤a1 b2≤b b≤b1) →
        ap₂ _,_ a1=a2 (B.≤-antisym b1≤b2 $ B.≤-trans b2≤b b≤b1)
      (centred a1≤a2 b1≤b b≤b2) (biased a2=a1 b2≤b1) →
        ap₂ _,_ (sym a2=a1) (B.≤-antisym (B.≤-trans b1≤b b≤b2) b2≤b1)
      (centred a1≤a2 b1≤b b≤b2) (centred a2≤a1 b2≤b b≤b1) →
        ap₂ _,_ (A.≤-antisym a1≤a2 a2≤a1) (B.≤-antisym (B.≤-trans b1≤b b≤b2) (B.≤-trans b2≤b b≤b1))

  LeftInvariantRightCentered : Poset (o ⊔ o') (o ⊔ r ⊔ r')
  LeftInvariantRightCentered .Poset.Ob = ⌞ A ⌟ × ⌞ B ⌟
  LeftInvariantRightCentered .Poset._≤_ x y = LeftInvariantRightCentered≤ x y
  LeftInvariantRightCentered .Poset.≤-thin = ⋉-thin _ _
  LeftInvariantRightCentered .Poset.≤-refl {x} = ⋉-refl x
  LeftInvariantRightCentered .Poset.≤-trans {x} {y} {z} = ⋉-trans x y z
  LeftInvariantRightCentered .Poset.≤-antisym {x} {y} = ⋉-antisym x y

  syntax RawLeftInvariantRightCentered≤ A B b x y = A ⋉[ b ] B [ x raw≤ y ]
  syntax LeftInvariantRightCentered≤ A B b x y = A ⋉[ b ] B [ x ≤ y ]
  syntax LeftInvariantRightCentered A B b = A ⋉[ b ] B

module _ {o o' r r'} {A : Poset o' r'} {B : Poset o r} {b : ⌞ B ⌟} where
  private
    module A = Reasoning A
    module B = Reasoning B
    module A⋉B = Reasoning (A ⋉[ b ] B)

  ⋉-fst-invariant : ∀ {x y : A⋉B.Ob} → A ⋉[ b ] B [ x ≤ y ] → fst x A.≤ fst y
  ⋉-fst-invariant = ∥-∥-rec A.≤-thin λ where
    (biased a1=a2 b1≤b2) → A.=→≤ a1=a2
    (centred a1≤a2 b1≤b b≤b2) → a1≤a2

  ⋉-snd-invariant : ∀ {x y : ⌞ A ⌟ × ⌞ B ⌟} → A ⋉[ b ] B [ x ≤ y ] → snd x B.≤ snd y
  ⋉-snd-invariant = ∥-∥-rec B.≤-thin λ where
    (biased a1=a2 b1≤b2) → b1≤b2
    (centred a1≤a2 b1≤b b≤b2) → B.≤-trans b1≤b b≤b2
