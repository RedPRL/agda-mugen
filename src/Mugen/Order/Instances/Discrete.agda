module Mugen.Order.Instances.Discrete where

open import Mugen.Prelude

Disc : ∀ {o} (A : Set o) → Poset o o
Disc A .Poset.Ob = ⌞ A ⌟
Disc A .Poset._≤_ x y = x ≡ y
Disc A .Poset.≤-thin = hlevel!
Disc A .Poset.≤-refl = refl
Disc A .Poset.≤-trans = _∙_
Disc A .Poset.≤-antisym p _ = p
