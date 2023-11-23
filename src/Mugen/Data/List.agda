module Mugen.Data.List where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

-- The version of reverse in the 1Lab is difficult to reason about,
-- due to a where-bound recursive helper. Instead, we define our own.
open import Data.List hiding (reverse) public

open import Mugen.Prelude

private variable
  ℓ ℓ′ : Level
  A B : Type ℓ

replicate : Nat → A → List A
replicate zero x = []
replicate (suc n) x = x ∷ (replicate n x)

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

All₂ : (P : A → A → Type ℓ′) → A → List A → A → List A → Type ℓ′
All₂ P b1 [] b2 [] = P b1 b2
All₂ P b1 [] b2 (y ∷ ys) = P b1 y × All₂ P b1 [] b2 ys
All₂ P b1 (x ∷ xs) b2 [] = P x b2 × All₂ P b1 xs b2 []
All₂ P b1 (x ∷ xs) b2 (y ∷ ys) = P x y × All₂ P b1 xs b2 ys

Some₂ : (P : A → A → Type ℓ′) → A → List A → A → List A → Type ℓ′
Some₂ P b1 [] b2 [] = P b1 b2
Some₂ P b1 [] b2 (y ∷ ys) = P b1 y ⊎ Some₂ P b1 [] b2 ys
Some₂ P b1 (x ∷ xs) b2 [] = P x b2 ⊎ Some₂ P b1 xs b2 []
Some₂ P b1 (x ∷ xs) b2 (y ∷ ys) = P x y ⊎ Some₂ P b1 xs b2 ys
