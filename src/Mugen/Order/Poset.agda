open import Mugen.Prelude

import Order.Base

module Mugen.Order.Poset where


--------------------------------------------------------------------------------
-- Partial Orders
--
-- We opt not to use the 1labs definition of partial order,
-- as it is defined as a structure on sets.
--
-- As this development is heavily focused on order theory,
-- it is much nicer to view partial orders/strict orders as
-- the primitive objects, and everything else as structures
-- atop that.

open Order.Base using
  ( is-partial-order
  ; is-partial-order-is-prop
  ; Poset-on
  ; Poset-on-pathp
  ; Poset-on-path
  ) public

record Poset o r : Type (lsuc (o ⊔ r)) where
  field
    Ob       : Type o
    poset-on : Poset-on r Ob
  open Poset-on poset-on public

instance
  Underlying-Poset : ∀ {o r} → Underlying (Poset o r)
  Underlying-Poset = record { ⌞_⌟ = Poset.Ob }

--------------------------------------------------------------------------------
-- Monotonic Maps

module _ {o o' r r'} (X : Poset o r) (Y : Poset o' r') where
  private
    module X = Poset X
    module Y = Poset Y

  is-monotone : ∀ (f : ⌞ X ⌟ → ⌞ Y ⌟) → Type _
  is-monotone f = ∀ {x y} → x X.≤ y → f x Y.≤ f y

  is-monotone-is-prop : ∀ (f : ⌞ X ⌟ → ⌞ Y ⌟) → is-prop (is-monotone f)
  is-monotone-is-prop f =
    Π-is-hlevel′ 1 λ _ → Π-is-hlevel′ 1 λ _ →
    Π-is-hlevel 1 λ _ → Y.≤-thin

record Monotone
  {o o' r r'}
  (X : Poset o r) (Y : Poset o' r')
  : Type (o ⊔ o' ⊔ r ⊔ r')
  where
  no-eta-equality
  field
    hom : ⌞ X ⌟ → ⌞ Y ⌟
    mono : is-monotone X Y hom
