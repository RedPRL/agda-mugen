module Mugen.Algebra.Displacement.Prefix where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Data.List
open import Mugen.Order.Poset
open import Mugen.Order.Prefix
open import Mugen.Algebra.Displacement

--------------------------------------------------------------------------------
-- Prefix Displacements
-- Section 3.3.6
--
-- Given a set 'A', we can define a displacement algebra on 'List A',
-- where 'xs ≤ ys' if 'xs' is a prefix of 'ys'.

 --------------------------------------------------------------------------------
 -- Left Invariance

++-left-invariant : ∀ {ℓ} {A : Type ℓ} (xs ys zs : List A) → Prefix[ ys ≤ zs ] → Prefix[ (xs ++ ys) ≤ (xs ++ zs) ]
++-left-invariant [] ys zs ys≤zs = ys≤zs
++-left-invariant (x ∷ xs) ys zs ys<zs = refl pre∷ (++-left-invariant xs ys zs ys<zs)

-- Most of the order theoretic properties come from 'Mugen.Order.Prefix'.

Prefix++ : ∀ {ℓ} (A : Set ℓ) → Displacement-algebra _ _
Prefix++ A = to-displacement-algebra displacement where
  displacement : make-displacement-algebra (Prefix≤ A)
  displacement .make-displacement-algebra.ε = []
  displacement .make-displacement-algebra._⊗_ = _++_
  displacement .make-displacement-algebra.idl = ++-idl _
  displacement .make-displacement-algebra.idr = ++-idr _
  displacement .make-displacement-algebra.associative {xs} {ys} {zs} = sym $ ++-assoc xs ys zs
  displacement .make-displacement-algebra.left-strict-invariant p =
    ++-left-invariant _ _ _ p , ++-injr _ _ _

module PreProperties {ℓ} {A : Set ℓ} where

  --------------------------------------------------------------------------------
  -- Bottoms

  prefix-has-bottom : has-bottom (Prefix++ A)
  prefix-has-bottom .has-bottom.bot = []
  prefix-has-bottom .has-bottom.is-bottom [] = pre[]
  prefix-has-bottom .has-bottom.is-bottom (_ ∷ _) = pre[]
