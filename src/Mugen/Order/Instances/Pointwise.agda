module Mugen.Order.Instances.Pointwise where

open import Order.Instances.Pointwise using (Pointwise) public

open import Mugen.Prelude
open import Mugen.Order.Lattice

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' o'' o''' r r' r'' r''' : Level

--------------------------------------------------------------------------------
-- Product of Indexed Posets
-- POPL 2023 Section 3.3.5 discussed the special case where I = Nat and A is a constant family

pointwise-map₂
  : {A : Type o} {B : A → Type o'} {C : A → Type o''} {D : A → Type o'''}
  → (∀ (x : A) → B x → C x → D x) → (∀ x → B x) → (∀ x → C x) → (∀ x → D x)
pointwise-map₂ m f g i = m i (f i) (g i)

module _ (I : Type o) {A : I → Poset o' r'} where
  private
    module A (i : I) = Poset (A i)

  --------------------------------------------------------------------------------
  -- Joins

  Pointwise-has-joins : (∀ i → has-joins (A i)) → has-joins (Pointwise I A)
  Pointwise-has-joins 𝒟-joins = joins
    where
      open module J (i : I) = has-joins (𝒟-joins i)

      joins : has-joins (Pointwise I A)
      joins .has-joins.join = pointwise-map₂ join
      joins .has-joins.joinl i = joinl i
      joins .has-joins.joinr i = joinr i
      joins .has-joins.universal f≤h g≤h = λ i → universal i (f≤h i) (g≤h i)

  --------------------------------------------------------------------------------
  -- Bottom

  Pointwise-has-bottom : (∀ i → has-bottom (A i)) → has-bottom (Pointwise I A)
  Pointwise-has-bottom A-bottom = bottom
    where
      open module B (i : I) = has-bottom (A-bottom i)

      bottom : has-bottom (Pointwise I A)
      bottom .has-bottom.bot i = bot i
      bottom .has-bottom.is-bottom i = is-bottom i
