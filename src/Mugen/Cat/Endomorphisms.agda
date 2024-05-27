open import Cat.Prelude

module Mugen.Cat.Endomorphisms {o ℓ} where

--------------------------------------------------------------------------------
-- The category of endomorphisms on an object.
--
-- /Technically/ this is a monoid, but it's easier to work with
-- in this form w/o having to introduce a delooping.

open import Mugen.Cat.Indexed

Endos : (𝒞 : Precategory o ℓ) (X : 𝒞 .Precategory.Ob) → Precategory lzero ℓ
Endos 𝒞 X = Indexed {I = ⊤} 𝒞 λ _ → X

Endos-include : {𝒞 : Precategory o ℓ} {X : 𝒞 .Precategory.Ob} → Functor (Endos 𝒞 X) 𝒞
Endos-include = Indexed-include
