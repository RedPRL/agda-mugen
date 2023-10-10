module Mugen.Algebra.Displacement where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

import Mugen.Data.Nat as Nat


private variable
  o r o' r' : Level
  A : Type o

--------------------------------------------------------------------------------
-- Displacement Algebras
--
-- Like ordered monoids, we view displacement algebras as structures
-- over an order.

record is-displacement-algebra
  {o r} (A : Strict-order o r)
  (ε : ⌞ A ⌟) (_⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟)
  : Type (o ⊔ r)
  where
  no-eta-equality
  open Strict-order A
  field
    has-is-monoid : is-monoid ε _⊗_
    left-invariant : ∀ {x y z} → y < z → (x ⊗ y) < (x ⊗ z)

  open is-monoid has-is-monoid hiding (has-is-set) public

  left-invariant-≤ : ∀ {x y z} → y ≤ z → (x ⊗ y) ≤ (x ⊗ z)
  left-invariant-≤ {x = x} (inl p) = inl (ap (x ⊗_) p)
  left-invariant-≤ (inr y<z) = inr (left-invariant y<z)

record Displacement-algebra-on
  {o r : Level} (A : Strict-order o r)
  : Type (o ⊔ lsuc r)
  where
  field
    ε : ⌞ A ⌟
    _⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟
    has-is-displacement-algebra : is-displacement-algebra A ε _⊗_

  open is-displacement-algebra has-is-displacement-algebra public

record Displacement-algebra (o r : Level) : Type (lsuc (o ⊔ r)) where
  no-eta-equality
  field
    strict-order : Strict-order o r
    displacement-algebra-on : Displacement-algebra-on strict-order

  open Strict-order strict-order public
  open Displacement-algebra-on displacement-algebra-on public

instance
  Underlying-displacement-algebra : ∀ {o r} → Underlying (Displacement-algebra o r)
  Underlying-displacement-algebra .Underlying.ℓ-underlying = _
  Underlying.⌞ Underlying-displacement-algebra ⌟ D = ⌞ Displacement-algebra.strict-order D ⌟

private
  variable
    X Y Z : Displacement-algebra o r

--------------------------------------------------------------------------------
-- Homomorphisms of Displacement Algebras

module _
  {o o' r r'}
  (X : Displacement-algebra o r) (Y : Displacement-algebra o' r')
  where
  private
    module X = Displacement-algebra X
    module Y = Displacement-algebra Y

  record is-displacement-algebra-hom
    (f : Strictly-monotone X.strict-order Y.strict-order)
    : Type (o ⊔ o')
    where
    no-eta-equality
    open Strictly-monotone f
    field
      pres-ε : hom X.ε ≡ Y.ε
      pres-⊗ : ∀ (x y : ⌞ X ⌟) → hom (x X.⊗ y) ≡ (hom x Y.⊗ hom y)

  is-displacement-algebra-hom-is-prop
    : (f : Strictly-monotone X.strict-order Y.strict-order)
    → is-prop (is-displacement-algebra-hom f)
  is-displacement-algebra-hom-is-prop f =
    Iso→is-hlevel 1 eqv $
    Σ-is-hlevel 1 (Y.has-is-set _ _) λ _ →
    Π-is-hlevel² 1 λ _ _ → Y.has-is-set _ _
    where unquoteDecl eqv = declare-record-iso eqv (quote is-displacement-algebra-hom) 

  record Displacement-algebra-hom : Type (o ⊔ o' ⊔ r ⊔ r') where
    no-eta-equality
    field
      strict-hom : Strictly-monotone X.strict-order Y.strict-order
      has-is-displacement-hom : is-displacement-algebra-hom strict-hom

    open Strictly-monotone strict-hom public
    open is-displacement-algebra-hom has-is-displacement-hom public

open Displacement-algebra-hom

Displacement-algebra-hom-path
  : ∀ {o r o' r'}
  → {X : Displacement-algebra o r} {Y : Displacement-algebra o' r'}
  → (f g : Displacement-algebra-hom X Y)
  → (∀ (x : ⌞ X ⌟) → f .strict-hom # x ≡ g .strict-hom # x)
  → f ≡ g
Displacement-algebra-hom-path f g p i .strict-hom =
  Strictly-monotone-path (f .strict-hom) (g .strict-hom) p i
Displacement-algebra-hom-path {X = X} {Y = Y} f g p i .has-is-displacement-hom =
  is-prop→pathp
    (λ i → is-displacement-algebra-hom-is-prop X Y
      (Strictly-monotone-path (f .strict-hom) (g .strict-hom) p i))
    (f .has-is-displacement-hom)
    (g .has-is-displacement-hom) i

instance
  Funlike-displacement-algebra-hom
    : ∀ {o r o' r'}
    → Funlike (Displacement-algebra-hom {o} {r} {o'} {r'})
  Funlike-displacement-algebra-hom .Funlike._#_ f x =
    f .strict-hom # x
  Funlike-displacement-algebra-hom .Funlike.ext p =
    Displacement-algebra-hom-path _ _ p

displacement-hom-∘
  : Displacement-algebra-hom Y Z
  → Displacement-algebra-hom X Y
  → Displacement-algebra-hom X Z
displacement-hom-∘ f g .strict-hom =
  strictly-monotone-∘ (f .strict-hom) (g .strict-hom)
displacement-hom-∘ f g .has-is-displacement-hom .is-displacement-algebra-hom.pres-ε =
  ap (λ x → f # x) (g .pres-ε)
  ∙ f .pres-ε 
displacement-hom-∘ f g .has-is-displacement-hom .is-displacement-algebra-hom.pres-⊗ x y =
  ap (λ x → f # x) (g .pres-⊗ x y)
  ∙ f .pres-⊗ (g # x) (g # y)

--------------------------------------------------------------------------------
-- Subalgebras of Displacement Algebras

record is-displacement-subalgebra
  {o r o' r'}
  (X : Displacement-algebra o r)
  (Y : Displacement-algebra o' r')
  : Type (o ⊔ o' ⊔ r ⊔ r')
  where
  no-eta-equality
  field
    into : Displacement-algebra-hom X Y
    inj  : ∀ {x y : ⌞ X ⌟} → into # x ≡ into # y → x ≡ y

  open Displacement-algebra-hom into public

module _ where
  open is-displacement-subalgebra

  is-displacement-subalgebra-trans
    : ∀ {o r o' r' o'' r''}
    {X : Displacement-algebra o r}
    {Y : Displacement-algebra o' r'}
    {Z : Displacement-algebra o'' r''}
    → is-displacement-subalgebra X Y
    → is-displacement-subalgebra Y Z
    → is-displacement-subalgebra X Z
  is-displacement-subalgebra-trans f g .into = displacement-hom-∘ (g .into) (f .into)
  is-displacement-subalgebra-trans f g .is-displacement-subalgebra.inj p = f .inj (g .inj p)

--------------------------------------------------------------------------------
-- Some Properties of Displacement Algebras

module _
  {o r} (A : Strict-order o r)
  {ε : ⌞ A ⌟} {_⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟}
  (D : is-displacement-algebra A ε _⊗_)
  where
  private
    open Strict-order A using (_≤_)
    module A = Strict-order A
    module D = is-displacement-algebra D

  is-right-invariant-displacement-algebra→is-ordered-monoid
    : (∀ {x y z} → x ≤ y → (x ⊗ z) ≤ (y ⊗ z))
    → is-ordered-monoid A.poset ε _⊗_
  is-right-invariant-displacement-algebra→is-ordered-monoid ≤-invariantr = om where
    om : is-ordered-monoid A.poset ε _⊗_
    om .is-ordered-monoid.has-is-monoid = D.has-is-monoid
    om .is-ordered-monoid.invariant w≤y x≤z =
      A.≤-trans (≤-invariantr w≤y) (D.left-invariant-≤ x≤z)

--------------------------------------------------------------------------------
-- Augmentations of Displacement Algebras

module _ {o r} (𝒟 : Displacement-algebra o r) where

  open Displacement-algebra 𝒟

  -- Ordered Monoids
  has-ordered-monoid : Type (o ⊔ r)
  has-ordered-monoid = is-ordered-monoid poset ε _⊗_

  right-invariant→has-ordered-monoid : (∀ {x y z} → x ≤ y → (x ⊗ z) ≤ (y ⊗ z)) → has-ordered-monoid
  right-invariant→has-ordered-monoid =
    is-right-invariant-displacement-algebra→is-ordered-monoid
      strict-order
      has-is-displacement-algebra

  -- Joins
  record has-joins : Type (o ⊔ r) where
    field
      join : ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟
      joinl : ∀ {x y} → x ≤ join x y
      joinr : ∀ {x y} → y ≤ join x y
      universal : ∀ {x y z} → x ≤ z → y ≤ z → join x y ≤ z

  -- Bottoms
  record has-bottom : Type (o ⊔ r) where
    field
      bot : ⌞ 𝒟 ⌟
      is-bottom : ∀ x → bot ≤ x

--------------------------------------------------------------------------------
-- Subalgebras of Augmented Displacement Algebras

preserves-joins
  : (X-joins : has-joins X) (Y-joins : has-joins Y)
  → (f : Displacement-algebra-hom X Y)
  → Type _
preserves-joins {X = X} ⋁X ⋁Y f =
  ∀ (x y : ⌞ X ⌟) → f # (⋁X .join x y) ≡ ⋁Y .join (f # x) (f # y)
  where
    open has-joins

preserves-bottom
  : (X-bot : has-bottom X) (Y-bot : has-bottom Y)
  → (f : Displacement-algebra-hom X Y)
  → Type _
preserves-bottom X⊥ Y⊥ f = f # X⊥ .bot ≡ Y⊥ .bot
  where
    open has-bottom

record is-displacement-subsemilattice
  {X : Displacement-algebra o r} {Y : Displacement-algebra o' r'}
  (X-joins : has-joins X) (Y-joins : has-joins Y)
  : Type (o ⊔ o' ⊔ r' ⊔ r)
  where
  field
    has-displacement-subalgebra : is-displacement-subalgebra X Y

  open is-displacement-subalgebra has-displacement-subalgebra public
  field
    pres-joins : preserves-joins X-joins Y-joins into

record is-bounded-displacement-subalgebra
  {X : Displacement-algebra o r} {Y : Displacement-algebra o' r'}
  (X-bottom : has-bottom X) (Y-bottom : has-bottom Y)
  : Type (o ⊔ o' ⊔ r ⊔ r') where
  field
    has-displacement-subalgebra : is-displacement-subalgebra X Y
  open is-displacement-subalgebra has-displacement-subalgebra public
  field
    pres-bottom : preserves-bottom X-bottom Y-bottom into

--------------------------------------------------------------------------------
-- Displacement Actions

record is-right-displacement-action
  {o r o′ r′}
  (A : Strict-order o r) (B : Displacement-algebra o′ r′)
  (α : ⌞ A ⌟ → ⌞ B ⌟ → ⌞ A ⌟)
  : Type (o ⊔ r ⊔ o′ ⊔ r′)
  where
  no-eta-equality
  private
    module A = Strict-order A
    module B = Displacement-algebra B
  field
    identity  : ∀ (a : ⌞ A ⌟) → α a B.ε ≡ a
    compat    : ∀ (a : ⌞ A ⌟) (x y : ⌞ B ⌟) → α (α a x) y ≡ α a (x B.⊗ y)
    invariant : ∀ (a : ⌞ A ⌟) (x y : ⌞ B ⌟) → x B.< y → α a x A.< α a y

record Right-displacement-action
  {o r o′ r′}
  (A : Strict-order o r) (B : Displacement-algebra o′ r′)
  : Type (o ⊔ r ⊔ o′ ⊔ r′)
  where
  field
    hom : ⌞ A ⌟ → ⌞ B ⌟ → ⌞ A ⌟
    has-is-action : is-right-displacement-action A B hom

--------------------------------------------------------------------------------
-- Builders

record make-displacement-algebra
  {o r} (A : Strict-order o r)
  : Type (o ⊔ r)
  where
  no-eta-equality
  open Strict-order A
  field
    ε : ⌞ A ⌟
    _⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟
    idl : ∀ {x} → ε ⊗ x ≡ x
    idr : ∀ {x} → x ⊗ ε ≡ x
    associative : ∀ {x y z} → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
    left-invariant : ∀ {x y z} → y < z → (x ⊗ y) < (x ⊗ z)

module _ where
  open Displacement-algebra
  open Displacement-algebra-on
  open is-displacement-algebra
  open make-displacement-algebra

  to-displacement-algebra
    : ∀ {o r} {A : Strict-order o r}
    → make-displacement-algebra A
    → Displacement-algebra o r
  to-displacement-algebra {A = A} mk .strict-order = A
  to-displacement-algebra {A = A} mk .displacement-algebra-on .ε = mk .ε
  to-displacement-algebra {A = A} mk .displacement-algebra-on ._⊗_ = mk ._⊗_
  to-displacement-algebra {A = A} mk .displacement-algebra-on .has-is-displacement-algebra .has-is-monoid .has-is-semigroup .has-is-magma .has-is-set = Strict-order.has-is-set A
  to-displacement-algebra {A = A} mk .displacement-algebra-on .has-is-displacement-algebra .has-is-monoid .has-is-semigroup .associative = mk .associative
  to-displacement-algebra {A = A} mk .displacement-algebra-on .has-is-displacement-algebra .has-is-monoid .idl = mk .idl
  to-displacement-algebra {A = A} mk .displacement-algebra-on .has-is-displacement-algebra .has-is-monoid .idr = mk .idr
  to-displacement-algebra {A = A} mk .displacement-algebra-on .has-is-displacement-algebra .left-invariant = mk .left-invariant

record make-displacement-subalgebra
  {o r o' r'}
  (X : Displacement-algebra o r)
  (Y : Displacement-algebra o' r')
  : Type (o ⊔ o' ⊔ r ⊔ r')
  where
  no-eta-equality
  private
    module X = Displacement-algebra X
    module Y = Displacement-algebra Y
  field
    into : ⌞ X ⌟ → ⌞ Y ⌟
    pres-ε : into X.ε ≡ Y.ε
    pres-⊗ : ∀ x y → into (x X.⊗ y) ≡ into x Y.⊗ into y
    strictly-mono : ∀ x y → x X.< y → into x Y.< into y
    inj : ∀ {x y} → into x ≡ into y → x ≡ y

module _ where
  open Strictly-monotone
  open is-displacement-algebra-hom
  open is-displacement-subalgebra
  open make-displacement-subalgebra

  to-displacement-subalgebra
    : ∀ {o r o' r'}
    → {X : Displacement-algebra o r}
    → {Y : Displacement-algebra o' r'}
    → make-displacement-subalgebra X Y
    → is-displacement-subalgebra X Y
  to-displacement-subalgebra mk .into .strict-hom .hom = mk .into
  to-displacement-subalgebra mk .into .strict-hom .strict-mono = mk .strictly-mono _ _
  to-displacement-subalgebra mk .into .has-is-displacement-hom .pres-ε = mk .pres-ε
  to-displacement-subalgebra mk .into .has-is-displacement-hom .pres-⊗ = mk .pres-⊗
  to-displacement-subalgebra mk .inj = mk .inj
