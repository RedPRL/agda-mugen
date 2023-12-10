module Mugen.Algebra.Displacement.Instances.Product where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.Instances.Product renaming (Product to Product-poset)

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- Products
-- Section 3.3.3
--
-- We can take the product of 2 displacement algebras. Algebraic structure
-- is given by the product of monoids, and ordering is given by the product of the
-- orders.

module _
  {A : Poset o r} {B : Poset o' r'}
  (𝒟₁ : Displacement-on A) (𝒟₂ : Displacement-on B)
  where
  private
    module A = Reasoning A
    module B = Reasoning B
    module 𝒟₁ = Displacement-on 𝒟₁
    module 𝒟₂ = Displacement-on 𝒟₂
    module P = Reasoning (Product-poset A B)

    --------------------------------------------------------------------------------
    -- Algebra

    _⊗_ : P.Ob → P.Ob → P.Ob
    (d1 , d2) ⊗ (d1′ , d2′) = (d1 𝒟₁.⊗ d1′) , (d2 𝒟₂.⊗ d2′)

    ε : P.Ob
    ε = 𝒟₁.ε , 𝒟₂.ε

    idl : ∀ (x : P.Ob) → (ε ⊗ x) ≡ x
    idl (d1 , d2) i = 𝒟₁.idl {d1} i , 𝒟₂.idl {d2} i

    idr : ∀ (x : P.Ob) → (x ⊗ ε) ≡ x
    idr (d1 , d2) i = 𝒟₁.idr {d1} i , 𝒟₂.idr {d2} i

    associative : ∀ (x y z : P.Ob) → (x ⊗ (y ⊗ z)) ≡ ((x ⊗ y) ⊗ z)
    associative (d1 , d2) (d1′ , d2′) (d1″ , d2″) i =
      𝒟₁.associative {d1} {d1′} {d1″} i , 𝒟₂.associative {d2} {d2′} {d2″} i

    --------------------------------------------------------------------------------
    -- Left Invariance

    left-strict-invariant : ∀ (x y z : P.Ob) → y P.≤ z → (x ⊗ y) P.≤[ y ≡ z ] (x ⊗ z)
    left-strict-invariant _ _ _ (y1≤z1 , y2≤z2) =
      (𝒟₁.left-invariant y1≤z1 , 𝒟₂.left-invariant y2≤z2) ,
      λ p i → 𝒟₁.injectiver-on-related y1≤z1 (ap fst p) i , 𝒟₂.injectiver-on-related y2≤z2 (ap snd p) i

  Product : Displacement-on (Product-poset A B)
  Product = to-displacement-on mk where
    mk : make-displacement (Product-poset A B)
    mk .make-displacement.ε = ε
    mk .make-displacement._⊗_ = _⊗_
    mk .make-displacement.idl = idl _
    mk .make-displacement.idr = idr _
    mk .make-displacement.associative = associative _ _ _
    mk .make-displacement.left-strict-invariant = left-strict-invariant _ _ _

module _
  {A : Poset o r} {B : Poset o' r'}
  {𝒟₁ : Displacement-on A} {𝒟₂ : Displacement-on B}
  where
  private
    module A = Reasoning A
    module B = Reasoning B
    module 𝒟₁ = Displacement-on 𝒟₁
    module 𝒟₂ = Displacement-on 𝒟₂
    module P = Reasoning (Product-poset A B)
    open Displacement-on (Product 𝒟₁ 𝒟₂)

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  Product-has-ordered-monoid : has-ordered-monoid 𝒟₁ → has-ordered-monoid 𝒟₂ → has-ordered-monoid (Product 𝒟₁ 𝒟₂)
  Product-has-ordered-monoid 𝒟₁-ordered-monoid 𝒟₂-ordered-monoid =
    right-invariant→has-ordered-monoid (Product 𝒟₁ 𝒟₂) ⊗×-right-invariant
    where
      module 𝒟₁-ordered-monoid = is-ordered-monoid 𝒟₁-ordered-monoid
      module 𝒟₂-ordered-monoid = is-ordered-monoid 𝒟₂-ordered-monoid

      ⊗×-right-invariant : ∀ {x y z} → x P.≤ y → (x ⊗ z) P.≤ (y ⊗ z)
      ⊗×-right-invariant (x1≤y1 , x2≤y2) =
        𝒟₁-ordered-monoid.right-invariant x1≤y1 , 𝒟₂-ordered-monoid.right-invariant x2≤y2
