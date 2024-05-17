open import Mugen.Prelude

module Mugen.Order.Instances.Lift where

private variable
  o r : Level

Lift≤
  : ∀ {o r}
  → (o′ r′ : Level)
  → Poset o r
  → Poset (o ⊔ o′) (r ⊔ r′)
Lift≤ o' r' X .Poset.Ob = Lift o' ⌞ X ⌟
Lift≤ o' r' X .Poset._≤_ x y = Lift r' $ (X .Poset._≤_) (Lift.lower x) (Lift.lower y)
Lift≤ o' r' X .Poset.≤-thin = Lift-is-hlevel 1 $ X .Poset.≤-thin
Lift≤ o' r' X .Poset.≤-refl = lift $ X .Poset.≤-refl
Lift≤ o' r' X .Poset.≤-trans (lift p) (lift q) = lift (X .Poset.≤-trans p q)
Lift≤ o' r' X .Poset.≤-antisym (lift p) (lift q) = ap lift (X .Poset.≤-antisym p q)
