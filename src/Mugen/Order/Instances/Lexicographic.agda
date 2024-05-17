module Mugen.Order.Instances.Lexicographic where

open import Mugen.Prelude
open import Mugen.Order.Lattice

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- Lexicographic Products
-- Section 3.3.4
--
-- The lexicographic product of 2 posets consists of their product
-- as monoids, as well as their lexicographic product as orders.

module _ (A : Poset o r) (B : Poset o' r') where
  private
    module A = Reasoning A
    module B = Reasoning B

  Lexicographic : Poset (o ⊔ o') (o ⊔ r ⊔ r')
  Lexicographic = poset where

    _≤_ : ∀ (x y : ⌞ A ⌟ × ⌞ B ⌟) → Type (o ⊔ r ⊔ r')
    _≤_ x y = x .fst A.≤[ x .snd B.≤ y .snd ] y .fst

    abstract
      ≤-thin : ∀ x y → is-prop (x ≤ y)
      ≤-thin x y = hlevel 1

      ≤-refl : ∀ x → x ≤ x
      ≤-refl x = A.≤-refl , λ _ → B.≤-refl

      ≤-trans : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
      ≤-trans x y z (x1≤y1 , x2≤y2) (y1≤z1 , y2≤z2) =
        A.≤-trans x1≤y1 y1≤z1 , λ x1=z1 →
        B.≤-trans
          (x2≤y2 (A.≤-antisym'-l x1≤y1 y1≤z1 x1=z1))
          (y2≤z2 (A.≤-antisym'-r x1≤y1 y1≤z1 x1=z1))

      ≤-antisym : ∀ x y → x ≤ y → y ≤ x → x ≡ y
      ≤-antisym x y (x1≤y1 , x2≤y2) (y1≤x1 , y2≤x2) i =
        let x1=y1 = A.≤-antisym x1≤y1 y1≤x1 in
        x1=y1 i , B.≤-antisym (x2≤y2 x1=y1) (y2≤x2 (sym x1=y1)) i

    poset : Poset (o ⊔ o') (o ⊔ r ⊔ r')
    poset .Poset.Ob = ⌞ A ⌟ × ⌞ B ⌟
    poset .Poset._≤_ = _≤_
    poset .Poset.≤-thin = ≤-thin _ _
    poset .Poset.≤-refl = ≤-refl _
    poset .Poset.≤-trans = ≤-trans _ _ _
    poset .Poset.≤-antisym = ≤-antisym _ _

module _ {A : Poset o r} {B : Poset o' r'} where
  private
    module A = Reasoning A
    module B = Reasoning B

  --------------------------------------------------------------------------------
  -- Joins

  -- If the following conditions are true, then 'Lex 𝒟₁ 𝒟₂' has joins:
  -- (1) Both 𝒟₁ and 𝒟₂ have joins.
  -- (2) 𝒟₂ has a bottom.
  -- (3) It's decidable in 𝒟₁ whether an element is equal to its join with another element.
  lex-has-joins
    : (A-joins : has-joins A) (let module A-joins = has-joins A-joins)
    → (∀ x y → Dec (x ≡ A-joins.join x y) × Dec (y ≡ A-joins.join x y))
    → (B-joins : has-joins B) → has-bottom B
    → has-joins (Lexicographic A B)

  lex-has-joins A-joins _≡∨₁?_ B-joins B-bottom = joins
    where
      module A-joins = has-joins A-joins
      module B-joins = has-joins B-joins
      module B-bottom = has-bottom B-bottom

      joins : has-joins (Lexicographic A B)
      joins .has-joins.join (x1 , x2) (y1 , y2) with x1 ≡∨₁? y1
      ... | yes _ , yes _ = A-joins.join x1 y1 , B-joins.join x2 y2
      ... | yes _ , no  _ = A-joins.join x1 y1 , x2
      ... | no  _ , yes _ = A-joins.join x1 y1 , y2
      ... | no  _ , no  _ = A-joins.join x1 y1 , B-bottom.bot
      joins .has-joins.joinl {x1 , _} {y1 , _} with x1 ≡∨₁? y1
      ... | yes x1=x1∨y1 , yes _ = A-joins.joinl , λ _ → B-joins.joinl
      ... | yes x1=x1∨y1 , no  _ = A-joins.joinl , λ _ → B.≤-refl
      ... | no  x1≠x1∨y1 , yes _ = A-joins.joinl , λ x1≡x1∨y1 → absurd (x1≠x1∨y1 x1≡x1∨y1)
      ... | no  x1≠x1∨y1 , no  _ = A-joins.joinl , λ x1≡x1∨y1 → absurd (x1≠x1∨y1 x1≡x1∨y1)
      joins .has-joins.joinr {x1 , _} {y1 , _} with x1 ≡∨₁? y1
      ... | yes _ , yes y1=x1∨y1 = A-joins.joinr , λ _ → B-joins.joinr
      ... | yes _ , no  y1≠x1∨y1 = A-joins.joinr , λ y1≡x1∨y1 → absurd (y1≠x1∨y1 y1≡x1∨y1)
      ... | no  _ , yes y1=x1∨y1 = A-joins.joinr , λ _ → B.≤-refl
      ... | no  _ , no  y1≠x1∨y1 = A-joins.joinr , λ y1≡x1∨y1 → absurd (y1≠x1∨y1 y1≡x1∨y1)
      joins .has-joins.universal {x1 , _} {y1 , _} {_ , z2} x≤z y≤z with x1 ≡∨₁? y1
      ... | yes x1=x1∨y1 , yes y1=x1∨y1 =
        A-joins.universal (x≤z .fst) (y≤z .fst) , λ x1vy1=z1 →
        B-joins.universal (x≤z .snd (x1=x1∨y1 ∙ x1vy1=z1)) (y≤z .snd (y1=x1∨y1 ∙ x1vy1=z1))
      ... | yes x1=x1∨y1 , no  y1≠x1∨y1 =
        A-joins.universal (x≤z .fst) (y≤z .fst) , λ x1vy1=z1 → x≤z .snd (x1=x1∨y1 ∙ x1vy1=z1)
      ... | no  x1≠x1∨y1 , yes y1=x1∨y1 =
        A-joins.universal (x≤z .fst) (y≤z .fst) , λ x1vy1=z1 → y≤z .snd (y1=x1∨y1 ∙ x1vy1=z1)
      ... | no  x1≠x1∨y1 , no  y1≠x1∨y1 =
        A-joins.universal (x≤z .fst) (y≤z .fst) , λ x1vy1=z1 → B-bottom.is-bottom

  --------------------------------------------------------------------------------
  -- Bottoms

  lex-has-bottom : has-bottom A → has-bottom B → has-bottom (Lexicographic A B)
  lex-has-bottom A-bottom B-bottom = bottom
    where
      module A-bottom = has-bottom (A-bottom)
      module B-bottom = has-bottom (B-bottom)

      bottom : has-bottom (Lexicographic A B)
      bottom .has-bottom.bot = A-bottom.bot , B-bottom.bot
      bottom .has-bottom.is-bottom = A-bottom.is-bottom , λ _ → B-bottom.is-bottom
