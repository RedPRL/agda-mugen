module Mugen.Cat.StrictOrders where

open import Mugen.Prelude
open import Mugen.Order.Poset

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
Strict-orders o r .idr f = ext (λ _ → refl)
Strict-orders o r .idl f = ext (λ _ → refl)
Strict-orders o r .assoc f g h = ext (λ _ → refl)

Lift<
  : ∀ {o r}
  → (o′ r′ : Level)
  → Poset o r
  → Poset (o ⊔ o′) (r ⊔ r′)
Lift< o' r' X = to-poset mk where
  open Poset X

  mk : make-poset _ (Lift o' ⌞ X ⌟)
  mk .make-poset._≤_ x y = Lift r' (Lift.lower x ≤ Lift.lower y)
  mk .make-poset.≤-refl = lift ≤-refl
  mk .make-poset.≤-trans (lift p) (lift q) = lift (≤-trans p q)
  mk .make-poset.≤-thin = Lift-is-hlevel 1 ≤-thin
  mk .make-poset.≤-antisym (lift p) (lift q) = ap lift (≤-antisym p q)
