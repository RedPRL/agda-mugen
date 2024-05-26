open import Cat.Prelude

module Mugen.Cat.Indexed {o o' ℓ} (𝒞 : Precategory o ℓ) {I : Type o'} (F : I → 𝒞 .Precategory.Ob) where

import Cat.Reasoning as Cat

open Cat 𝒞

Indexed : Precategory o' ℓ
Indexed .Precategory.Ob          = I
Indexed .Precategory.Hom i j     = Hom (F i) (F j)
Indexed .Precategory.Hom-set _ _ = Hom-set _ _
Indexed .Precategory.id          = id
Indexed .Precategory._∘_         = _∘_
Indexed .Precategory.idr         = idr
Indexed .Precategory.idl         = idl
Indexed .Precategory.assoc       = assoc

Indexed-include : Functor Indexed 𝒞
Indexed-include .Functor.F₀ = F
Indexed-include .Functor.F₁ σ = σ
Indexed-include .Functor.F-id = refl
Indexed-include .Functor.F-∘ _ _ = refl
