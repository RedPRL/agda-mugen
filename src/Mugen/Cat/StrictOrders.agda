module Mugen.Cat.StrictOrders where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

private variable
  o r : Level
  X Y Z : StrictOrder o r

--------------------------------------------------------------------------------
-- The Category of Strict Orders

open Precategory
open StrictOrder-on
open is-strict-order

strict-order-id : StrictOrder-Hom X X
strict-order-id {X = X} = homomorphism (λ x → x) (λ x<y → x<y)

strict-order-∘ : StrictOrder-Hom Y Z → StrictOrder-Hom X Y → StrictOrder-Hom X Z
strict-order-∘ f g = homomorphism (λ x → f ⟨$⟩ g ⟨$⟩ x) (λ x<y → homo f $ homo g x<y)

strict-order-path : {f g : StrictOrder-Hom X Y} → (∀ x → f ⟨$⟩ x ≡ g ⟨$⟩ x) → f ≡ g
strict-order-path = homomorphism-path strictly-monotonic-is-prop

strict-order-happly : {f g : StrictOrder-Hom X Y} → f ≡ g → (∀ x → f ⟨$⟩ x ≡ g ⟨$⟩ x)
strict-order-happly p x i = p i ⟨$⟩ x

StrictOrders : ∀ (o r : Level) → Precategory (lsuc o ⊔ lsuc r) (o ⊔ r)
StrictOrders o r .Ob = StrictOrder o r
StrictOrders o r .Hom = StrictOrder-Hom
StrictOrders o r .Hom-set X Y = hlevel 2
StrictOrders o r .id = strict-order-id
StrictOrders o r ._∘_ = strict-order-∘
StrictOrders o r .idr f = strict-order-path λ _ → refl
StrictOrders o r .idl f = strict-order-path λ _ → refl
StrictOrders o r .assoc f g h = strict-order-path λ _ → refl

Lift< : ∀ {o r} → (o′ r′ : Level) → StrictOrder o r → StrictOrder (o ⊔ o′) (r ⊔ r′)
⌞ Lift< o′ r′ X ⌟ = Lift o′ ⌞ X ⌟
Lift< o′ r′ X .structure ._<_ (lift x) (lift y) = Lift r′ (X [ x < y ])
Lift< o′ r′ X .structure .has-is-strict-order .irrefl (lift x<x) = X .structure .irrefl x<x
Lift< o′ r′ X .structure .has-is-strict-order .trans (lift x<y) (lift y<z) = lift (X .structure .trans x<y y<z) 
Lift< o′ r′ X .structure .has-is-strict-order .has-prop =
  let open is-strict-order (X .structure .has-is-strict-order)
  in hlevel 1
⌞ Lift< o′ r′ X ⌟-set =
  let open SetStructure X
  in hlevel 2
