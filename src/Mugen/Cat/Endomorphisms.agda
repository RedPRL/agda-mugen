open import Cat.Prelude

module Mugen.Cat.Endomorphisms {o ℓ} (𝒞 : Precategory o ℓ) where

import Cat.Reasoning as Cat

open Cat 𝒞

Endos : Ob → Precategory lzero ℓ
Endos X .Precategory.Ob = ⊤
Endos X .Precategory.Hom _ _ = Hom X X
Endos X .Precategory.Hom-set _ _ = Hom-set X X
Endos X .Precategory.id = id
Endos X .Precategory._∘_ = _∘_
Endos X .Precategory.idr = idr
Endos X .Precategory.idl = idl
Endos X .Precategory.assoc = assoc
