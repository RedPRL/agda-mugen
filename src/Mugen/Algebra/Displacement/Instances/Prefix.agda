open import Mugen.Prelude
open import Mugen.Data.List
open import Mugen.Order.StrictOrder
open import Mugen.Order.Lattice
import Mugen.Order.Instances.LexicalList as LexicalList
open import Mugen.Algebra.Displacement

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

import Mugen.Order.Reasoning as Reasoning

import Mugen.Order.Instances.LexicalList as LexicalList

--------------------------------------------------------------------------------
-- Prefix Displacements
-- Section 3.3.6
--
-- Given a poset 'A', we can define a displacement algebra on lexicographical lists over 'A'.

module Mugen.Algebra.Displacement.Instances.Prefix {o r} (A : Poset o r) where

private
  module A = Reasoning A
  module L where
    open LexicalList A public
    open Reasoning poset hiding (_≤_) public

  --------------------------------------------------------------------------------
  -- Left Invariance

  ++-left-invariant : (xs ys zs : List _) → ys L.≤ zs → (xs ++ ys) L.≤ (xs ++ zs)
  ++-left-invariant [] ys zs ys≤zs = ys≤zs
  ++-left-invariant (x ∷ xs) ys zs ys≤zs = A.≤-refl L.∷≤ (λ _ → ++-left-invariant xs ys zs ys≤zs)

-- Most of the order theoretic properties come from 'Mugen.Order.Instances.Prefix'.
Prefix : Displacement-on L.poset
Prefix = to-displacement-on displacement where
  displacement : make-displacement L.poset
  displacement .make-displacement.ε = []
  displacement .make-displacement._⊗_ = _++_
  displacement .make-displacement.idl = ++-idl _
  displacement .make-displacement.idr = ++-idr _
  displacement .make-displacement.associative {xs} {ys} {zs} = sym $ ++-assoc xs ys zs
  displacement .make-displacement.left-strict-invariant p =
    ++-left-invariant _ _ _ p , ++-injr _ _ _
