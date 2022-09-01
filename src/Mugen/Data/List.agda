module Mugen.Data.List where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Data.List public

open import Mugen.Prelude

module _ {ℓ} {A : Type ℓ} (aset : is-set A) where

  ++-is-magma : is-magma {A = List A} _++_
  ++-is-magma .has-is-set = ListPath.List-is-hlevel 0 aset
  
  ++-is-semigroup : is-semigroup {A = List A} _++_
  ++-is-semigroup .has-is-magma = ++-is-magma
  ++-is-semigroup .associative {x} {y} {z} = sym (++-assoc x y z)

  ++-is-monoid : is-monoid {A = List A} [] _++_
  ++-is-monoid .has-is-semigroup = ++-is-semigroup
  ++-is-monoid .idl {x} = ++-idl x
  ++-is-monoid .idr {x} = ++-idr x


