module Mugen.Cat.StrictOrders where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

private variable
  o r : Level
  X Y Z : Poset o r

--------------------------------------------------------------------------------
-- The Category of Strict Orders

open Precategory

Strict-orders : ∀ (o r : Level) → Precategory (lsuc o ⊔ lsuc r) (o ⊔ r)
Strict-orders o r .Ob = Poset o r
Strict-orders o r .Hom = Strictly-monotone
Strict-orders o r .Hom-set X Y = hlevel 2
Strict-orders o r .id = strictly-monotone-id
Strict-orders o r ._∘_ = strictly-monotone-∘
Strict-orders o r .idr f = ext λ _ → refl
Strict-orders o r .idl f = ext λ _ → refl
Strict-orders o r .assoc f g h = ext λ _ → refl

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
