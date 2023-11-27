module Mugen.Order.Discrete where

open import Mugen.Prelude

open import Mugen.Order.Poset

-- We do this entirely with copatterns for performance reasons.
Disc : ∀ {o} → (A : Set o) → Poset o o
Disc A .Poset.Ob = ⌞ A ⌟
Disc {o = o} A .Poset.poset-on .Poset-on._≤_ x y = (x ≡ y)
Disc A .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-thin = hlevel!
Disc A .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-refl = refl
Disc A .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-trans = _∙_
Disc A .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-antisym p _ = p
