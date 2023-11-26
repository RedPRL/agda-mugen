module Mugen.Order.Singleton where

open import Mugen.Prelude
open import Mugen.Order.Poset

-- We do this entirely with copatterns for performance reasons.
◆ : ∀ {o r} → Poset o r
◆ .Poset.Ob = Lift _ ⊤
◆ .Poset.poset-on .Poset-on._≤_ _ _ = Lift _ ⊤
◆ .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-thin = hlevel!
◆ .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-refl = lift tt
◆ .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-trans p q = p
◆ .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-antisym _ _ = refl
