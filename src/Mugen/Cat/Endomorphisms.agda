open import Cat.Prelude

module Mugen.Cat.Endomorphisms {o ℓ} (𝒞 : Precategory o ℓ) (X : 𝒞 .Precategory.Ob) where

--------------------------------------------------------------------------------
-- The category of endomorphisms on an object.
--
-- /Technically/ this is a monoid, but it's easier to work with
-- in this form w/o having to introduce a delooping.

open import Mugen.Cat.Indexed

Endos = Indexed 𝒞 {I = ⊤} λ _ → X
Endos-include = Indexed-include 𝒞 {I = ⊤} λ _ → X
