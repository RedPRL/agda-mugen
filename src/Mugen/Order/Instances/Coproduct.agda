module Mugen.Order.Instances.Coproduct where

open import Mugen.Prelude

-- NOTE: We require that both 'A' and 'B' live in the same universe
-- to avoid large amounts of 'Lift'. If you need to take the coproduct
-- of two partial orders that live in different universes, perform a lift
-- on the partial order before taking the coproduct.
module _ {o r} (A B : Poset o r) where
  private
    module A = Poset A
    module B = Poset B

    _≤_ : (⌞ A ⌟ ⊎ ⌞ B ⌟) → (⌞ A ⌟ ⊎ ⌞ B ⌟) → Type r
    inl x ≤ inl y = x A.≤ y
    inl x ≤ inr y = Lift _ ⊥
    inr x ≤ inl y = Lift _ ⊥
    inr x ≤ inr y = x B.≤ y

    ≤-thin : ∀ x y → is-prop (x ≤ y)
    ≤-thin (inl _) (inl _) = A.≤-thin
    ≤-thin (inl _) (inr _) = hlevel 1
    ≤-thin (inr _) (inl _) = hlevel 1
    ≤-thin (inr _) (inr _) = B.≤-thin

    ≤-refl : ∀ x → x ≤ x
    ≤-refl (inl x) = A.≤-refl
    ≤-refl (inr x) = B.≤-refl

    ≤-trans : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
    ≤-trans (inl x) (inl y) (inl z) p q = A.≤-trans p q
    ≤-trans (inr x) (inr y) (inr z) p q = B.≤-trans p q

    ≤-antisym : ∀ x y → x ≤ y → y ≤ x → x ≡ y
    ≤-antisym (inl _) (inl _) p q = ap inl $ A.≤-antisym p q
    ≤-antisym (inl _) (inr _) ()
    ≤-antisym (inr _) (inl _) ()
    ≤-antisym (inr _) (inr _) p q = ap inr $ B.≤-antisym p q

  Coproduct : Poset o r
  Coproduct .Poset.Ob =  ⌞ A ⌟ ⊎ ⌞ B ⌟
  Coproduct .Poset._≤_ = _≤_
  Coproduct .Poset.≤-thin {x} {y} = ≤-thin x y
  Coproduct .Poset.≤-refl {x} = ≤-refl x
  Coproduct .Poset.≤-trans {x} {y} {z} = ≤-trans x y z
  Coproduct .Poset.≤-antisym {x} {y} = ≤-antisym x y
