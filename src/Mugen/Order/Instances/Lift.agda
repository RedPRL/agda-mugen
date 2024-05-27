open import Order.Base

open import Mugen.Prelude
open import Mugen.Order.StrictOrder
import Mugen.Order.Reasoning as Reasoning

module Mugen.Order.Instances.Lift where

Liftᵖ : ∀ {o r} o′ r′ → Poset o r → Poset (o ⊔ o′) (r ⊔ r′)
Liftᵖ o' r' X .Poset.Ob      = Lift o' ⌞ X ⌟
Liftᵖ o' r' X .Poset._≤_ x y = Lift r' $ (X .Poset._≤_) (Lift.lower x) (Lift.lower y)
Liftᵖ o' r' X .Poset.≤-thin  = Lift-is-hlevel 1 $ X .Poset.≤-thin
Liftᵖ o' r' X .Poset.≤-refl  = lift $ X .Poset.≤-refl
Liftᵖ o' r' X .Poset.≤-trans (lift p) (lift q)   = lift (X .Poset.≤-trans p q)
Liftᵖ o' r' X .Poset.≤-antisym (lift p) (lift q) = ap lift (X .Poset.≤-antisym p q)

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
