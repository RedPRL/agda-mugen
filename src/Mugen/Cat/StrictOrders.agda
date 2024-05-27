module Mugen.Cat.StrictOrders where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder
open import Mugen.Order.Instances.Lift

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

liftᶠ-strict-orders : ∀ {o r o' r' : Level} → Functor (Strict-orders o r) (Strict-orders (o ⊔ o') (r ⊔ r'))
liftᶠ-strict-orders {o' = o'} {r'} .Functor.F₀ X    = Liftᵖ o' r' X
liftᶠ-strict-orders .Functor.F₁ f    = strictly-monotone-∘ (strictly-monotone-∘ lift-strictly-monotone f) lower-strictly-monotone
liftᶠ-strict-orders .Functor.F-id    = ext λ _ → refl
liftᶠ-strict-orders .Functor.F-∘ _ _ = ext λ _ → refl
