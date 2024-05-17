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
