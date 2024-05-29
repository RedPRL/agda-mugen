module Mugen.Order.Instances.Lift where

open import Order.Instances.Lift using (Liftᵖ) public

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

lift-strictly-monotone
  : ∀ {bo br o r} {X : Poset o r}
  → Strictly-monotone X (Liftᵖ bo br X)
lift-strictly-monotone = F where
  open Strictly-monotone
  F : Strictly-monotone _ _
  F .hom              = lift
  F .pres-≤[]-equal α = lift α , ap Lift.lower

lower-strictly-monotone
  : ∀ {bo br o r} {X : Poset o r}
  → Strictly-monotone (Liftᵖ bo br X) X
lower-strictly-monotone = F where
  open Strictly-monotone
  F : Strictly-monotone _ _
  F .hom                     = Lift.lower
  F .pres-≤[]-equal (lift α) = α , ap lift
