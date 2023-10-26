module Mugen.Order.Singleton where

open import Mugen.Prelude

open import Mugen.Order.StrictOrder

-- We do this entirely with copatterns for performance reasons.
◆ : ∀ {o r} → Strict-order o r
◆ .Strict-order.Ob = Lift _ ⊤
◆ .Strict-order.strict-order-on .Strict-order-on._<_ _ _ = Lift _ ⊥
◆ .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.<-irrefl = Lift.lower
◆ .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.<-trans p q = p
◆ .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.<-thin = hlevel!
◆ .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.has-is-set = hlevel!
