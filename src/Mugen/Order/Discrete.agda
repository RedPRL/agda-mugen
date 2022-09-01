module Mugen.Order.Discrete where

open import Data.Fin

open import Mugen.Prelude

open import Mugen.Order.StrictOrder

Disc : ∀ {o r} → (A : Set o) → StrictOrder o r
⌞ Disc A ⌟ = ∣ A ∣
Disc n .structure .StrictOrder-on._<_ _ _ = Lift _ ⊥
Disc n .structure .StrictOrder-on.has-is-strict-order .is-strict-order.irrefl (lift ff) = ff
Disc n .structure .StrictOrder-on.has-is-strict-order .is-strict-order.trans p _ = p
Disc n .structure .StrictOrder-on.has-is-strict-order .is-strict-order.has-prop = hlevel 1
⌞ Disc A ⌟-set = is-tr A
