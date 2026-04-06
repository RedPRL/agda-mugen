open import Mugen.Prelude

import Mugen.Order.Reasoning as Reasoning

module Mugen.Order.Instances.LeftInvariantRightCentred
  {o o' r r'} (A : Poset o r) (B : Poset o' r') (b : ⌞ B ⌟) where

  private
    module A = Reasoning A
    module B = Reasoning B

  data _≤'_ (x y : ⌞ A ⌟ × ⌞ B ⌟) : Type (o ⊔ r ⊔ r') where
    biased : fst x ≡ fst y → snd x B.≤ snd y → x ≤' y
    centred : fst x A.≤ fst y → snd x B.≤ b → b B.≤ snd y → x ≤' y

  _≤_ : (x y : ⌞ A ⌟ × ⌞ B ⌟) → Type (o ⊔ r ⊔ r')
  x ≤ y = ∥ x ≤' y ∥

  private
    ≤-thin : ∀ x y → is-prop (x ≤ y)
    ≤-thin x y = squash

    ≤-refl : ∀ x → x ≤ x
    ≤-refl (a , b1) = pure $ biased refl B.≤-refl

    ≤-trans : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
    ≤-trans x y z = ∥-∥-map₂ λ where
      (biased a1=a2 b1≤b2) (biased a2=a3 b2≤b3) → biased (a1=a2 ∙ a2=a3) (B.≤-trans b1≤b2 b2≤b3)
      (biased a1=a2 b1≤b2) (centred a2≤a3 b2≤b b≤b3) → centred (A.=+≤→≤ a1=a2 a2≤a3) (B.≤-trans b1≤b2 b2≤b) b≤b3
      (centred a1≤a2 b1≤b b≤b2) (biased a2=a3 b2≤b3) → centred (A.≤+=→≤ a1≤a2 a2=a3) b1≤b (B.≤-trans b≤b2 b2≤b3)
      (centred a1≤a2 b1≤b b≤b2) (centred a2≤a3 b2≤b b≤b3) → centred (A.≤-trans a1≤a2 a2≤a3) b1≤b b≤b3

    ≤-antisym : ∀ x y → x ≤ y → y ≤ x → x ≡ y
    ≤-antisym x y = ∥-∥-rec₂ (×-is-hlevel 2 A.Ob-is-set B.Ob-is-set _ _) λ where
      (biased a1=a2 b1≤b2) (biased a2=a1 b2≤b1) →
        ap₂ _,_ a1=a2 (B.≤-antisym b1≤b2 b2≤b1)
      (biased a1=a2 b1≤b2) (centred a2≤a1 b2≤b b≤b1) →
        ap₂ _,_ a1=a2 (B.≤-antisym b1≤b2 $ B.≤-trans b2≤b b≤b1)
      (centred a1≤a2 b1≤b b≤b2) (biased a2=a1 b2≤b1) →
        ap₂ _,_ (sym a2=a1) (B.≤-antisym (B.≤-trans b1≤b b≤b2) b2≤b1)
      (centred a1≤a2 b1≤b b≤b2) (centred a2≤a1 b2≤b b≤b1) →
        ap₂ _,_ (A.≤-antisym a1≤a2 a2≤a1) (B.≤-antisym (B.≤-trans b1≤b b≤b2) (B.≤-trans b2≤b b≤b1))

  poset : Poset (o ⊔ o') (o ⊔ r ⊔ r')
  poset .Poset.Ob = ⌞ A ⌟ × ⌞ B ⌟
  poset .Poset._≤_ x y = x ≤ y
  poset .Poset.≤-thin = ≤-thin _ _
  poset .Poset.≤-refl {x} = ≤-refl x
  poset .Poset.≤-trans {x} {y} {z} = ≤-trans x y z
  poset .Poset.≤-antisym {x} {y} = ≤-antisym x y

  ≤-fst-invariant : ∀ {x y : ⌞ A ⌟ × ⌞ B ⌟} → x ≤ y → fst x A.≤ fst y
  ≤-fst-invariant = ∥-∥-rec A.≤-thin λ where
    (biased a1=a2 b1≤b2) → A.=→≤ a1=a2
    (centred a1≤a2 b1≤b b≤b2) → a1≤a2

  ≤-snd-invariant : ∀ {x y : ⌞ A ⌟ × ⌞ B ⌟} → x ≤ y → snd x B.≤ snd y
  ≤-snd-invariant = ∥-∥-rec B.≤-thin λ where
    (biased a1=a2 b1≤b2) → b1≤b2
    (centred a1≤a2 b1≤b b≤b2) → B.≤-trans b1≤b b≤b2
