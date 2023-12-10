module Mugen.Algebra.Displacement.Instances.Lexicographic where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Instances.Product
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.Instances.Lexicographic

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- Lexicographic Products
-- Section 3.3.4
--
-- The lexicographic product of 2 displacement algebras consists of their product
-- as monoids, as well as their lexicographic product as orders.
--
-- As noted earlier, algebraic structure is given by the product of monoids, so we don't need
-- to prove that here.

module _
  {A : Poset o r} {B : Poset o' r'}
  (𝒟₁ : Displacement-on A) (𝒟₂ : Displacement-on B)
  where
  private
    module 𝒟₁ = Displacement-on 𝒟₁
    module 𝒟₂ = Displacement-on 𝒟₂
    module P = Displacement-on (Product 𝒟₁ 𝒟₂)
    module L = Reasoning (Lexicographic A B)

    --------------------------------------------------------------------------------
    -- Left Invariance

    abstract
      left-strict-invariant : ∀ x y z → y L.≤ z → (x P.⊗ y) L.≤[ y ≡ z ] (x P.⊗ z)
      left-strict-invariant x y z (y1≤z1 , y2≤z2) =
        (𝒟₁.left-invariant y1≤z1 , λ p → 𝒟₂.left-invariant (y2≤z2 (𝒟₁.injectiver-on-related y1≤z1 p))) ,
        λ p i →
        let y1=z1 = 𝒟₁.injectiver-on-related y1≤z1 (ap fst p) in
        y1=z1 i , 𝒟₂.injectiver-on-related (y2≤z2 y1=z1) (ap snd p) i

  -- TODO: refactor with Product
  LexicographicProduct : Displacement-on (Lexicographic A B)
  LexicographicProduct = to-displacement-on mk
    where
      mk : make-displacement (Lexicographic A B)
      mk .make-displacement.ε = P.ε
      mk .make-displacement._⊗_ = P._⊗_
      mk .make-displacement.idl = P.idl
      mk .make-displacement.idr = P.idr
      mk .make-displacement.associative = P.associative
      mk .make-displacement.left-strict-invariant = left-strict-invariant _ _ _

module _
  {A : Poset o r} {B : Poset o' r'}
  {𝒟₁ : Displacement-on A} {𝒟₂ : Displacement-on B}
  where
  private
    module A = Reasoning A
    module 𝒟₁ = Displacement-on 𝒟₁
    module 𝒟₂ = Displacement-on 𝒟₂
    module L = Reasoning (Lexicographic A B)
    open Displacement-on (LexicographicProduct 𝒟₁ 𝒟₂)

  --------------------------------------------------------------------------------
  -- Ordered Monoids

  -- When 𝒟₁ is /strictly/ right invariant and 𝒟₂ is an ordered monoid,
  -- then 'Lex 𝒟₁ 𝒟₂' is also an ordered monoid.
  lex-has-ordered-monoid
    : has-ordered-monoid 𝒟₁
    → (∀ {x y z} → x A.≤ y → (x 𝒟₁.⊗ z) ≡ (y 𝒟₁.⊗ z) → x ≡ y)
    → has-ordered-monoid 𝒟₂
    → has-ordered-monoid (LexicographicProduct 𝒟₁ 𝒟₂)
  lex-has-ordered-monoid 𝒟₁-ordered-monoid 𝒟₁-injl-on-related 𝒟₂-ordered-monoid =
    right-invariant→has-ordered-monoid (LexicographicProduct 𝒟₁ 𝒟₂) lex-right-invariant
    where
      module 𝒟₁-ordered-monoid = is-ordered-monoid 𝒟₁-ordered-monoid
      module 𝒟₂-ordered-monoid = is-ordered-monoid 𝒟₂-ordered-monoid

      lex-right-invariant : ∀ {x y z} → x L.≤ y → (x ⊗ z) L.≤ (y ⊗ z)
      lex-right-invariant (y1≤z1 , y2≤z2) =
        𝒟₁-ordered-monoid.right-invariant y1≤z1 , λ p →
        𝒟₂-ordered-monoid.right-invariant (y2≤z2 (𝒟₁-injl-on-related y1≤z1 p))
