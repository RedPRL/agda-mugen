module Mugen.Order.Instances.Product where

open import Mugen.Prelude
open import Mugen.Order.Lattice

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- Binary Products
-- Section 3.3.3

module _ (A : Poset o r) (B : Poset o' r') where
  private
    module A = Reasoning A
    module B = Reasoning B

  Product : Poset (o ⊔ o') (r ⊔ r')
  Product = poset where

    _≤_ : ∀ (x y :  ⌞ A ⌟ × ⌞ B ⌟) → Type (r ⊔ r')
    _≤_ x y = (x .fst A.≤ y .fst) × (x .snd B.≤ y .snd)

    abstract
      ≤-thin : ∀ x y → is-prop (x ≤ y)
      ≤-thin x y = hlevel 1

      ≤-refl : ∀ x → x ≤ x
      ≤-refl x = A.≤-refl , B.≤-refl

      ≤-trans : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
      ≤-trans _ _ _ (x1≤y1 , x2≤y2) (y1≤z1 , y2≤z2) = A.≤-trans x1≤y1 y1≤z1 , B.≤-trans x2≤y2 y2≤z2

      ≤-antisym : ∀ x y → x ≤ y → y ≤ x → x ≡ y
      ≤-antisym _ _ (x1≤y1 , x2≤y2) (y1≤z1 , y2≤z2) i = A.≤-antisym x1≤y1 y1≤z1 i , B.≤-antisym x2≤y2 y2≤z2 i

    poset : Poset _ _
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
    open Reasoning (Product A B)

  --------------------------------------------------------------------------------
  -- Joins

  Product-has-joins : has-joins A → has-joins B → has-joins (Product A B)
  Product-has-joins A-joins B-joins = joins
    where
      module A-joins = has-joins A-joins
      module B-joins = has-joins B-joins

      joins : has-joins (Product A B)
      joins .has-joins.join (x1 , x2) (y1 , y2) = A-joins.join x1 y1 , B-joins.join x2 y2
      joins .has-joins.joinl = A-joins.joinl , B-joins.joinl
      joins .has-joins.joinr = A-joins.joinr , B-joins.joinr
      joins .has-joins.universal x≤z y≤z =
        A-joins.universal (x≤z .fst) (y≤z .fst) ,
        B-joins.universal (x≤z .snd) (y≤z .snd)

  --------------------------------------------------------------------------------
  -- Bottoms

  Product-has-bottom : has-bottom A → has-bottom B → has-bottom (Product A B)
  Product-has-bottom A-bottom B-bottom = bottom
    where
      module A-bottom = has-bottom A-bottom
      module B-bottom = has-bottom B-bottom

      bottom : has-bottom (Product A B)
      bottom .has-bottom.bot = A-bottom.bot , B-bottom.bot
      bottom .has-bottom.is-bottom = A-bottom.is-bottom , B-bottom.is-bottom
