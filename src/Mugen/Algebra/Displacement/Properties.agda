module Mugen.Algebra.Displacement.Properties where

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid

open import Mugen.Order.PartialOrder
open import Mugen.Order.StrictOrder


private variable
  o r : Level
  A : Type o

--------------------------------------------------------------------------------
-- A displacement algebra 𝒟 is right-invariant with respect to ≤
-- if and only if (𝒟, ≤) is also an ordered monoid.

module _ {o r} {A : Type o} {_<_ : A → A → Type r} {ε : A} {_⊗_ : A → A → A}
         (A-set : is-set A)
         (𝒟 : is-displacement-algebra _<_ ε _⊗_) where

  private
    module 𝒟 = is-displacement-algebra 𝒟
    open 𝒟 using (_≤_)

