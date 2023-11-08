module Mugen.Cat.StrictOrders where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

private variable
  o r : Level
  X Y Z : Strict-order o r

--------------------------------------------------------------------------------
-- The Category of Strict Orders

open Precategory

Strict-orders : ∀ (o r : Level) → Precategory (lsuc o ⊔ lsuc r) (o ⊔ r)
Strict-orders o r .Ob = Strict-order o r
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
  → Strict-order o r
  → Strict-order (o ⊔ o′) (r ⊔ r′)
Lift< o' r' X = to-strict-order mk where
  open Strict-order X

  mk : make-strict-order _ (Lift o' ⌞ X ⌟)
  mk .make-strict-order._<_ x y = Lift r' (Lift.lower x < Lift.lower y)
  mk .make-strict-order.<-irrefl (lift p) = <-irrefl p
  mk .make-strict-order.<-trans (lift p) (lift q) = lift (<-trans p q)
  mk .make-strict-order.<-thin = Lift-is-hlevel 1 <-thin
  mk .make-strict-order.has-is-set = Lift-is-hlevel 2 has-is-set
