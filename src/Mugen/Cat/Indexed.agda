open import Cat.Prelude

module Mugen.Cat.Indexed {o o' ℓ} {I : Type o'} where

import Cat.Reasoning as Cat

Indexed : (𝒞 : Precategory o ℓ) (F : I → 𝒞 .Precategory.Ob) → Precategory o' ℓ
Indexed 𝒞 F = C where
  open Cat 𝒞
  C : Precategory o' ℓ
  C .Precategory.Ob          = I
  C .Precategory.Hom i j     = Hom (F i) (F j)
  C .Precategory.Hom-set _ _ = Hom-set _ _
  C .Precategory.id          = id
  C .Precategory._∘_         = _∘_
  C .Precategory.idr         = idr
  C .Precategory.idl         = idl
  C .Precategory.assoc       = assoc

Indexed-include : ∀ {𝒞} {F : I → 𝒞 .Precategory.Ob} → Functor (Indexed 𝒞 F) 𝒞
Indexed-include {F = F} .Functor.F₀ = F
Indexed-include .Functor.F₁ σ = σ
Indexed-include .Functor.F-id = refl
Indexed-include .Functor.F-∘ _ _ = refl
