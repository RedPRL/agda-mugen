module Mugen.Algebra.Displacement.Instances.LexicalProduct where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Instances.Product
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.Instances.LexicalSum
  renaming (Lexical-sum to Lexical-sum-poset)

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

private
  substᵢ-const : ∀ {ℓ ℓ'} {I : Type ℓ} {T : Type ℓ'} {a b : I}
    → (p : a ≡ᵢ b) → (x : T)
    → substᵢ (λ (_ : I) → T) p x ≡ x
  substᵢ-const reflᵢ _ = refl

--------------------------------------------------------------------------------
-- Lexical Products
-- Section 3.3.4
--
-- The lexical product of 2 displacement algebras consists of their product
-- as monoids, as well as the lexical product as orders (a special case of
-- the lexical sum where the fiber is constant).
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
    module B = Reasoning B
    module P = Displacement-on (Product 𝒟₁ 𝒟₂)
    module L = Reasoning (Lexical-sum-poset A (λ _ → B))

    lex-from : ∀ {x y : ⌞ A ⌟} {x' y' : ⌞ B ⌟}
      → ((p : x ≡ᵢ y) → substᵢ (λ _ → ⌞ B ⌟) p x' B.≤ y')
      → (x ≡ᵢ y → x' B.≤ y')
    lex-from {x = x} {y} f x≡ᵢy = B.=+≤→≤ (sym (substᵢ-const x≡ᵢy _)) (f x≡ᵢy)

    lex-into : ∀ {x y : ⌞ A ⌟} {x' y' : ⌞ B ⌟}
      → (x ≡ᵢ y → x' B.≤ y')
      → ((p : x ≡ᵢ y) → substᵢ (λ _ → ⌞ B ⌟) p x' B.≤ y')
    lex-into {x = x} {y} f x≡ᵢy = B.=+≤→≤ (substᵢ-const x≡ᵢy _) (f x≡ᵢy)

    --------------------------------------------------------------------------------
    -- Left Invariance

    abstract
      left-strict-invariant : ∀ x y z → y L.≤ z → (x P.⊗ y) L.≤[ y ≡ z ] (x P.⊗ z)
      left-strict-invariant x y z (y≤z1 , y'≤z2) =
        (𝒟₁.left-invariant y≤z1 ,
          lex-into λ p → 𝒟₂.left-invariant (lex-from y'≤z2 (Id≃path.from (𝒟₁.injectiver-on-related y≤z1 (Id≃path.to p))))) ,
        λ p i →
        let y=z1 = 𝒟₁.injectiver-on-related y≤z1 (ap fst p) in
        y=z1 i , 𝒟₂.injectiver-on-related (lex-from y'≤z2 (Id≃path.from y=z1)) (ap snd p) i

  Lexical-product : Displacement-on (Lexical-sum-poset A (λ _ → B))
  Lexical-product = to-displacement-on mk
    where
      mk : make-displacement (Lexical-sum-poset A (λ _ → B))
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
    module B = Reasoning B
    module 𝒟₁ = Displacement-on 𝒟₁
    module 𝒟₂ = Displacement-on 𝒟₂
    module L = Reasoning (Lexical-sum-poset A (λ _ → B))
    open Displacement-on (Lexical-product 𝒟₁ 𝒟₂)

    lex-from : ∀ {a b : ⌞ A ⌟} {x y : ⌞ B ⌟}
      → ((p : a ≡ᵢ b) → substᵢ (λ (_ : ⌞ A ⌟) → ⌞ B ⌟) p x B.≤ y)
      → (a ≡ᵢ b → x B.≤ y)
    lex-from {x = x} {y} f q = subst (λ z → z B.≤ y) (substᵢ-const q x) (f q)

    lex-into : ∀ {a b : ⌞ A ⌟} {x y : ⌞ B ⌟}
      → (a ≡ᵢ b → x B.≤ y)
      → ((p : a ≡ᵢ b) → substᵢ (λ (_ : ⌞ A ⌟) → ⌞ B ⌟) p x B.≤ y)
    lex-into {x = x} {y} f q = subst (λ z → z B.≤ y) (sym (substᵢ-const q x)) (f q)

  --------------------------------------------------------------------------------
  -- Ordered Monoids

  -- When 𝒟₁ is /strictly/ right invariant and 𝒟₂ is an ordered monoid,
  -- then 'Lexical-product 𝒟₁ 𝒟₂' is also an ordered monoid.
  lex-has-ordered-monoid
    : has-ordered-monoid 𝒟₁
    → (∀ {x y z} → x A.≤ y → (x 𝒟₁.⊗ z) ≡ (y 𝒟₁.⊗ z) → x ≡ y)
    → has-ordered-monoid 𝒟₂
    → has-ordered-monoid (Lexical-product 𝒟₁ 𝒟₂)
  lex-has-ordered-monoid 𝒟₁-ordered-monoid 𝒟₁-injl-on-related 𝒟₂-ordered-monoid =
    right-invariant→has-ordered-monoid (Lexical-product 𝒟₁ 𝒟₂) lex-right-invariant
    where
      module 𝒟₁-ordered-monoid = is-ordered-monoid 𝒟₁-ordered-monoid
      module 𝒟₂-ordered-monoid = is-ordered-monoid 𝒟₂-ordered-monoid

      lex-right-invariant : ∀ {x y z} → x L.≤ y → (x ⊗ z) L.≤ (y ⊗ z)
      lex-right-invariant (y≤z1 , y'≤z2) =
        𝒟₁-ordered-monoid.right-invariant y≤z1 ,
        lex-into λ p → 𝒟₂-ordered-monoid.right-invariant
          (lex-from y'≤z2 (Id≃path.from (𝒟₁-injl-on-related y≤z1 (Id≃path.to p))))
