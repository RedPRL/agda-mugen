module Mugen.Algebra.Displacement.Instances.Prefix where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Data.List
open import Mugen.Order.StrictOrder
open import Mugen.Order.Lattice
open import Mugen.Order.Instances.Prefix renaming (Prefix to Prefix-poset)
open import Mugen.Algebra.Displacement

private variable
  o r : Level

--------------------------------------------------------------------------------
-- Prefix Displacements
-- Section 3.3.6
--
-- Given a set 'A', we can define a displacement algebra on 'List A',
-- where 'xs ≤ ys' if 'xs' is a prefix of 'ys'.

private
  --------------------------------------------------------------------------------
  -- Left Invariance

  ++-left-invariant : ∀ {ℓ} {A : Type ℓ} (xs ys zs : List A) → Prefix[ ys ≤ zs ] → Prefix[ (xs ++ ys) ≤ (xs ++ zs) ]
  ++-left-invariant [] ys zs ys≤zs = ys≤zs
  ++-left-invariant (x ∷ xs) ys zs ys<zs = refl pre∷ (++-left-invariant xs ys zs ys<zs)

-- Most of the order theoretic properties come from 'Mugen.Order.Instances.Prefix'.
Prefix : ∀ (A : Set o) → Displacement-on (Prefix-poset A)
Prefix A = to-displacement-on displacement where
  displacement : make-displacement (Prefix-poset A)
  displacement .make-displacement.ε = []
  displacement .make-displacement._⊗_ = _++_
  displacement .make-displacement.idl = ++-idl _
  displacement .make-displacement.idr = ++-idr _
  displacement .make-displacement.associative {xs} {ys} {zs} = sym $ ++-assoc xs ys zs
  displacement .make-displacement.left-strict-invariant p =
    ++-left-invariant _ _ _ p , ++-injr _ _ _
