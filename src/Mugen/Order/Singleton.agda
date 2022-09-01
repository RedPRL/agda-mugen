module Mugen.Order.Singleton where

open import Mugen.Prelude

open import Mugen.Order.StrictOrder

◆ : ∀ {o r} → StrictOrder o r
⌞ ◆ ⌟ = Lift _ ⊤
◆ .structure .StrictOrder-on._<_ _ _ = Lift _ ⊥
◆ .structure .StrictOrder-on.has-is-strict-order .is-strict-order.irrefl (lift bot) = bot
◆ .structure .StrictOrder-on.has-is-strict-order .is-strict-order.trans (lift bot) _ = lift bot
◆ .structure .StrictOrder-on.has-is-strict-order .is-strict-order.has-prop = hlevel 1
⌞ ◆ ⌟-set = hlevel 2
