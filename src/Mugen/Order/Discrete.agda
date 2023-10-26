module Mugen.Order.Discrete where

open import Data.Fin

open import Mugen.Prelude

open import Mugen.Order.StrictOrder

-- We do this entirely with copatterns for performance reasons.
Disc : ∀ {o r} → (A : Set o) → Strict-order o r
Disc A .Strict-order.Ob = ⌞ A ⌟
Disc A .Strict-order.strict-order-on .Strict-order-on._<_ _ _ = Lift _ ⊥
Disc A .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.<-irrefl = Lift.lower
Disc A .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.<-trans p q = p
Disc A .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.<-thin = hlevel!
Disc A .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.has-is-set = hlevel!
