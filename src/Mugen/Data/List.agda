module Mugen.Data.List where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

-- The version of reverse in the 1Lab is difficult to reason about,
-- due to a where-bound recursive helper. Instead, we define our own.
open import Data.List hiding (reverse) public

open import Mugen.Prelude

private variable
  ℓ : Level
  A : Type ℓ

++-injr : (xs ys zs : List A) → xs ++ ys ≡ xs ++ zs → ys ≡ zs
++-injr [] _ _ p = p
++-injr (x ∷ xs) _ _ p = ++-injr xs _ _ $ ∷-tail-inj p

module _ (aset : is-set A) where

  ++-is-magma : is-magma {A = List A} _++_
  ++-is-magma .has-is-set = ListPath.List-is-hlevel 0 aset

  ++-is-semigroup : is-semigroup {A = List A} _++_
  ++-is-semigroup .has-is-magma = ++-is-magma
  ++-is-semigroup .associative {x} {y} {z} = sym (++-assoc x y z)

  ++-is-monoid : is-monoid {A = List A} [] _++_
  ++-is-monoid .has-is-semigroup = ++-is-semigroup
  ++-is-monoid .idl {x} = ++-idl x
  ++-is-monoid .idr {x} = ++-idr x
