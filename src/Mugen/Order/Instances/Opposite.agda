module Mugen.Order.Instances.Opposite where

open import Mugen.Prelude

module _ {o r} (A : Poset o r) where
  open Poset A

  Opposite : Poset o r
  Opposite .Poset.Ob = Ob
  Opposite .Poset._≤_ x y = y ≤ x
  Opposite .Poset.≤-refl = ≤-refl
  Opposite .Poset.≤-trans p q = ≤-trans q p
  Opposite .Poset.≤-thin = ≤-thin
  Opposite .Poset.≤-antisym p q = ≤-antisym q p
