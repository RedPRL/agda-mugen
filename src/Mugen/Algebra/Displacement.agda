module Mugen.Algebra.Displacement where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' o'' r r' r'' : Level

--------------------------------------------------------------------------------
-- Displacement Algebras
--
-- Like ordered monoids, we view displacement algebras as structures
-- over an order.

record is-displacement
  (A : Poset o r)
  (ε : ⌞ A ⌟) (_⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟)
  : Type (o ⊔ r)
  where
  no-eta-equality
  open Reasoning A
  field
    has-is-monoid : is-monoid ε _⊗_

    -- This formulation is constructively MUCH NICER than
    --   ∀ {x y z} → y < z → (x ⊗ y) < (x ⊗ z)
    -- The reason is that the second part of '_<_' is a negation,
    -- and a function between two negated types '(A → ⊥) → (B → ⊥)'
    -- is not constructively sufficient for proving that an indexed
    -- product is a displacement algebra. What will work is the
    -- slightly more "constructive" version, 'B → A'.
    --
    -- Note: we did not /prove/ that the naive formulation is not
    -- constructively working.
    left-strict-invariant : ∀ {x y z} → y ≤ z → (x ⊗ y) ≤[ y ≡ z ] (x ⊗ z)

  abstract
    left-invariant : ∀ {x y z} → y ≤ z → (x ⊗ y) ≤ (x ⊗ z)
    left-invariant y≤z = left-strict-invariant y≤z .fst

    injectiver-on-related : ∀ {x y z} → y ≤ z → (x ⊗ y) ≡ (x ⊗ z) → y ≡ z
    injectiver-on-related y≤z = left-strict-invariant y≤z .snd

  open is-monoid has-is-monoid hiding (has-is-set) public

  abstract
    right-contract : ∀ {x e} → e ≤ ε → (x ⊗ e) ≤ x
    right-contract e≤ε = ≤+=→≤ (left-invariant e≤ε) idr

    right-expand : ∀ {x e} → ε ≤ e → x ≤ (x ⊗ e)
    right-expand ε≤e = =+≤→≤ (sym idr) (left-invariant ε≤e)

record Displacement-on (A : Poset o r) : Type (o ⊔ lsuc r) where
  field
    ε : ⌞ A ⌟
    _⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟
    has-is-displacement : is-displacement A ε _⊗_

  open is-displacement has-is-displacement public

--------------------------------------------------------------------------------
-- Homomorphisms of Displacement Algebras

module _
  {A : Poset o r} {B : Poset o' r'}
  (X : Displacement-on A) (Y : Displacement-on B)
  where

  private
    module A = Reasoning A
    module B = Reasoning B
    module X = Displacement-on X
    module Y = Displacement-on Y

  record is-displacement-hom (f : Strictly-monotone A B) : Type (o ⊔ o') where
    no-eta-equality
    open Strictly-monotone f
    field
      pres-ε : hom X.ε ≡ Y.ε
      pres-⊗ : ∀ {x y : ⌞ A ⌟} → hom (x X.⊗ y) ≡ (hom x Y.⊗ hom y)

  abstract
    is-displacement-hom-is-prop
      : (f : Strictly-monotone A B)
      → is-prop (is-displacement-hom f)
    is-displacement-hom-is-prop f =
      Iso→is-hlevel 1 eqv $
      Σ-is-hlevel 1 (B.Ob-is-set _ _) λ _ →
      Π-is-hlevel' 1 λ _ → Π-is-hlevel' 1 λ _ → B.Ob-is-set _ _
      where unquoteDecl eqv = declare-record-iso eqv (quote is-displacement-hom)

abstract instance
  H-Level-is-displacement : ∀ {n}
    {A : Poset o r} {B : Poset o' r'}
    {X : Displacement-on A} {Y : Displacement-on B}
    {f : Strictly-monotone A B} →
    H-Level (is-displacement-hom X Y f) (suc n)
  H-Level-is-displacement {X = X} {Y} {f} = prop-instance (is-displacement-hom-is-prop X Y f)

id-is-displacement-hom
  : {A : Poset o r} (X : Displacement-on A)
  → is-displacement-hom X X strictly-monotone-id
id-is-displacement-hom X .is-displacement-hom.pres-ε = refl
id-is-displacement-hom X .is-displacement-hom.pres-⊗ = refl

∘-is-displacement-hom
  : {A : Poset o r} {B : Poset o' r'} {C : Poset o'' r''}
  {X : Displacement-on A} {Y : Displacement-on B} {Z : Displacement-on C}
  {f : Strictly-monotone B C} {g : Strictly-monotone A B}
  → is-displacement-hom Y Z f
  → is-displacement-hom X Y g
  → is-displacement-hom X Z (strictly-monotone-∘ f g)
∘-is-displacement-hom {f = f} f-disp g-disp .is-displacement-hom.pres-ε =
  ap· f (g-disp .is-displacement-hom.pres-ε) ∙ f-disp .is-displacement-hom.pres-ε
∘-is-displacement-hom {f = f} {g = g} f-disp g-disp .is-displacement-hom.pres-⊗ {x} {y} =
  ap· f (g-disp .is-displacement-hom.pres-⊗ {x} {y}) ∙ f-disp .is-displacement-hom.pres-⊗ {g · x} {g · y}

--------------------------------------------------------------------------------
-- Some Properties of Displacement Algebras

module _
  (A : Poset o r)
  {ε : ⌞ A ⌟} {_⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟}
  (𝒟 : is-displacement A ε _⊗_)
  where
  private
    module A = Poset A
    module 𝒟 = is-displacement 𝒟

  is-right-invariant-displacement→is-ordered-monoid
    : (∀ {x y z} → x A.≤ y → (x ⊗ z) A.≤ (y ⊗ z))
    → is-ordered-monoid A ε _⊗_
  is-right-invariant-displacement→is-ordered-monoid right-invariant = om where
    om : is-ordered-monoid A ε _⊗_
    om .is-ordered-monoid.has-is-monoid = 𝒟.has-is-monoid
    om .is-ordered-monoid.invariant w≤y x≤z =
      A.≤-trans (right-invariant w≤y) (𝒟.left-invariant x≤z)

module _ {A : Poset o r} (𝒟 : Displacement-on A) where
  open Reasoning A
  open Displacement-on 𝒟

  -- Ordered Monoids
  has-ordered-monoid : Type (o ⊔ r)
  has-ordered-monoid = is-ordered-monoid A ε _⊗_

  right-invariant→has-ordered-monoid : (∀ {x y z} → x ≤ y → (x ⊗ z) ≤ (y ⊗ z)) → has-ordered-monoid
  right-invariant→has-ordered-monoid =
    is-right-invariant-displacement→is-ordered-monoid A has-is-displacement

--------------------------------------------------------------------------------
-- Builders

record make-displacement (A : Poset o r) : Type (o ⊔ r) where
  no-eta-equality
  open Reasoning A
  field
    ε : ⌞ A ⌟
    _⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟
    idl : ∀ {x} → ε ⊗ x ≡ x
    idr : ∀ {x} → x ⊗ ε ≡ x
    associative : ∀ {x y z} → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
    left-strict-invariant : ∀ {x y z} → y ≤ z → (x ⊗ y) ≤[ y ≡ z ] (x ⊗ z)

module _ {A : Poset o r} where
  open Displacement-on
  open is-displacement
  open make-displacement

  to-displacement-on : make-displacement A → Displacement-on A
  to-displacement-on mk .ε = mk .ε
  to-displacement-on mk ._⊗_ = mk ._⊗_
  to-displacement-on mk .has-is-displacement .is-displacement.has-is-monoid .is-monoid.has-is-semigroup .is-semigroup.has-is-magma .is-magma.has-is-set = Poset.Ob-is-set A
  to-displacement-on mk .has-is-displacement .is-displacement.has-is-monoid .is-monoid.has-is-semigroup .is-semigroup.associative = mk .associative
  to-displacement-on mk .has-is-displacement .is-displacement.has-is-monoid .is-monoid.idl = mk .idl
  to-displacement-on mk .has-is-displacement .is-displacement.has-is-monoid .is-monoid.idr = mk .idr
  to-displacement-on mk .has-is-displacement .is-displacement.left-strict-invariant = mk .left-strict-invariant
