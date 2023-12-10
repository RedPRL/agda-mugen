module Mugen.Algebra.Displacement.Instances.IndexedProduct where

open import Order.Instances.Pointwise

open import Mugen.Prelude
open import Mugen.Order.Instances.Pointwise
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- Product of Indexed Displacements
-- POPL 2023 Section 3.3.5 discussed the special case where I = Nat and 𝒟 is a constant family
--
-- The product of indexed displacement algebras consists
-- of functions '(i : I) → 𝒟 i'. Multiplication is performed pointwise,
-- and ordering is given by 'f ≤ g' if '∀ i. f i ≤ g i'.

--------------------------------------------------------------------------------
-- Displacement Algebra

module _ (I : Type o) {A : I → Poset o' r'} (𝒟 : (i : I) → Displacement-on (A i)) where
  private
    module 𝒟 (i : I) = Displacement-on (𝒟 i)

  IndexedProduct : Displacement-on (Pointwise I A)
  IndexedProduct = to-displacement-on mk where
    mk : make-displacement (Pointwise I A)
    mk .make-displacement.ε = 𝒟.ε
    mk .make-displacement._⊗_ = pointwise-map₂ 𝒟._⊗_
    mk .make-displacement.idl = funext λ i → 𝒟.idl i
    mk .make-displacement.idr = funext λ i → 𝒟.idr i
    mk .make-displacement.associative = funext λ i → 𝒟.associative i
    mk .make-displacement.left-strict-invariant g≤h .fst i = 𝒟.left-invariant i (g≤h i)
    mk .make-displacement.left-strict-invariant g≤h .snd fg=fh =
      funext λ i → 𝒟.injectiver-on-related i (g≤h i) (happly fg=fh i)

--------------------------------------------------------------------------------
-- Additional properties

module _ (I : Type o) {A : I → Poset o' r'} (𝒟 : (i : I) → Displacement-on (A i)) where
  private module A = Reasoning (Pointwise I A)
  private module 𝒟 = Displacement-on (IndexedProduct I 𝒟)

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  IndexedProduct-has-ordered-monoid
    : (∀ i → has-ordered-monoid (𝒟 i)) → has-ordered-monoid (IndexedProduct I 𝒟)
  IndexedProduct-has-ordered-monoid 𝒟-om =
    let open module M (i : I) = is-ordered-monoid (𝒟-om i) in
    right-invariant→has-ordered-monoid (IndexedProduct I 𝒟) λ f≤g i → right-invariant i (f≤g i)
