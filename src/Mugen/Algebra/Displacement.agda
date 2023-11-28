module Mugen.Algebra.Displacement where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.Poset

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
  {o r} (A : Poset o r)
  (ε : ⌞ A ⌟) (_⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟)
  : Type (o ⊔ r)
  where
  no-eta-equality
  open Poset A
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
    left-strict-invariant : ∀ {x y z} → y ≤ z
      → ((x ⊗ y) ≤ (x ⊗ z)) × ((x ⊗ y) ≡ (x ⊗ z) → y ≡ z)

  abstract
    left-invariant : ∀ {x y z} → y ≤ z → (x ⊗ y) ≤ (x ⊗ z)
    left-invariant y≤z = fst $ left-strict-invariant y≤z

    injr-on-related : ∀ {x y z} → y ≤ z → (x ⊗ y) ≡ (x ⊗ z) → y ≡ z
    injr-on-related y≤z = snd $ left-strict-invariant y≤z

  open is-monoid has-is-monoid hiding (has-is-set) public

record Displacement-algebra-on
  {o r : Level} (A : Poset o r)
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
    poset : Poset o r
    displacement-algebra-on : Displacement-algebra-on poset

  open Poset poset public
  open Displacement-algebra-on displacement-algebra-on public

instance
  Underlying-displacement-algebra : ∀ {o r} → Underlying (Displacement-algebra o r)
  Underlying-displacement-algebra .Underlying.ℓ-underlying = _
  Underlying.⌞ Underlying-displacement-algebra ⌟ D = ⌞ Displacement-algebra.poset D ⌟

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
    (f : Strictly-monotone X.poset Y.poset)
    : Type (o ⊔ o')
    where
    no-eta-equality
    open Strictly-monotone f
    field
      pres-ε : hom X.ε ≡ Y.ε
      pres-⊗ : ∀ (x y : ⌞ X ⌟) → hom (x X.⊗ y) ≡ (hom x Y.⊗ hom y)

  is-displacement-algebra-hom-is-prop
    : (f : Strictly-monotone X.poset Y.poset)
    → is-prop (is-displacement-algebra-hom f)
  is-displacement-algebra-hom-is-prop f =
    Iso→is-hlevel 1 eqv $
    Σ-is-hlevel 1 (Y.has-is-set _ _) λ _ →
    Π-is-hlevel² 1 λ _ _ → Y.has-is-set _ _
    where unquoteDecl eqv = declare-record-iso eqv (quote is-displacement-algebra-hom)

  record Displacement-algebra-hom : Type (o ⊔ o' ⊔ r ⊔ r') where
    no-eta-equality
    field
      strict-hom : Strictly-monotone X.poset Y.poset
      has-is-displacement-hom : is-displacement-algebra-hom strict-hom

    open Strictly-monotone strict-hom public
    open is-displacement-algebra-hom has-is-displacement-hom public

Displacement-algebra-hom-path
  : ∀ {o r o' r'}
  → {X : Displacement-algebra o r} {Y : Displacement-algebra o' r'}
  → (f g : Displacement-algebra-hom X Y)
  → f .Displacement-algebra-hom.strict-hom ≡ g .Displacement-algebra-hom.strict-hom
  → f ≡ g
Displacement-algebra-hom-path f g p i .Displacement-algebra-hom.strict-hom = p i
Displacement-algebra-hom-path {X = X} {Y = Y} f g p i .Displacement-algebra-hom.has-is-displacement-hom =
  is-prop→pathp
    (λ i → is-displacement-algebra-hom-is-prop X Y (p i))
    (f .Displacement-algebra-hom.has-is-displacement-hom)
    (g .Displacement-algebra-hom.has-is-displacement-hom) i

instance
  Funlike-displacement-algebra-hom
    : ∀ {o r o' r'}
    → Funlike (Displacement-algebra-hom {o} {r} {o'} {r'})
  Funlike-displacement-algebra-hom .Funlike.au = Underlying-displacement-algebra
  Funlike-displacement-algebra-hom .Funlike.bu = Underlying-displacement-algebra
  Funlike-displacement-algebra-hom .Funlike._#_ f x = f .Displacement-algebra-hom.strict-hom # x

module _ {o r o' r' ℓ} {X : Displacement-algebra o r} {Y : Displacement-algebra o' r'} where
  private
    module X = Displacement-algebra X
    module Y = Displacement-algebra Y

  Extensional-Displacement-algebra-hom
    : ∀ ⦃ sa : Extensional (Strictly-monotone X.poset Y.poset) ℓ ⦄
    → Extensional (Displacement-algebra-hom X Y) ℓ
  Extensional-Displacement-algebra-hom ⦃ sa ⦄ =
    injection→extensional! {f = Displacement-algebra-hom.strict-hom} (Displacement-algebra-hom-path _ _) sa

  instance
    extensionality-displacement-algebra-hom : Extensionality (Displacement-algebra-hom X Y)
    extensionality-displacement-algebra-hom = record { lemma = quote Extensional-Displacement-algebra-hom }

displacement-hom-∘
  : Displacement-algebra-hom Y Z
  → Displacement-algebra-hom X Y
  → Displacement-algebra-hom X Z
displacement-hom-∘ f g .Displacement-algebra-hom.strict-hom =
  strictly-monotone-∘ (f .Displacement-algebra-hom.strict-hom) (g .Displacement-algebra-hom.strict-hom)
displacement-hom-∘ f g .Displacement-algebra-hom.has-is-displacement-hom .is-displacement-algebra-hom.pres-ε =
  ap (f #_) (g .Displacement-algebra-hom.pres-ε) ∙ f .Displacement-algebra-hom.pres-ε
displacement-hom-∘ f g .Displacement-algebra-hom.has-is-displacement-hom .is-displacement-algebra-hom.pres-⊗ x y =
  ap (f #_) (g .Displacement-algebra-hom.pres-⊗ x y) ∙ f .Displacement-algebra-hom.pres-⊗ (g # x) (g # y)

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
  {o r} (A : Poset o r)
  {ε : ⌞ A ⌟} {_⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟}
  (D : is-displacement-algebra A ε _⊗_)
  where
  private
    module A = Poset A
    open A using (_≤_)
    module D = is-displacement-algebra D

  is-right-invariant-displacement-algebra→is-ordered-monoid
    : (∀ {x y z} → x ≤ y → (x ⊗ z) ≤ (y ⊗ z))
    → is-ordered-monoid A ε _⊗_
  is-right-invariant-displacement-algebra→is-ordered-monoid ≤-invariantr = om where
    om : is-ordered-monoid A ε _⊗_
    om .is-ordered-monoid.has-is-monoid = D.has-is-monoid
    om .is-ordered-monoid.invariant w≤y x≤z =
      A.≤-trans (≤-invariantr w≤y) (D.left-invariant x≤z)

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
      poset
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

module _
  {o r o′ r′}
  (A : Poset o r) (B : Displacement-algebra o′ r′)
  where
  private
    module A = Poset A
    module B = Displacement-algebra B

  record is-right-displacement-action
    (α : ⌞ A ⌟ → ⌞ B ⌟ → ⌞ A ⌟)
    : Type (o ⊔ r ⊔ o′ ⊔ r′)
    where
    no-eta-equality
    field
      identity         : ∀ (a : ⌞ A ⌟) → α a B.ε ≡ a
      compat           : ∀ (a : ⌞ A ⌟) (x y : ⌞ B ⌟) → α (α a x) y ≡ α a (x B.⊗ y)
      strict-invariant : ∀ (a : ⌞ A ⌟) (x y : ⌞ B ⌟) → x B.≤ y → (α a x A.≤ α a y) × (α a x ≡ α a y → x ≡ y)

    abstract
      invariant : ∀ (a : ⌞ A ⌟) (x y : ⌞ B ⌟) → x B.≤ y → α a x A.≤ α a y
      invariant a x y x≤y = strict-invariant a x y x≤y .fst

      injr-on-related : ∀ (a : ⌞ A ⌟) (x y : ⌞ B ⌟) → x B.≤ y → α a x ≡ α a y → x ≡ y
      injr-on-related a x y x≤y = strict-invariant a x y x≤y .snd

  abstract
    is-right-displacement-action-is-prop
      : (α : ⌞ A ⌟ → ⌞ B ⌟ → ⌞ A ⌟)
      → is-prop (is-right-displacement-action α)
    is-right-displacement-action-is-prop α =
      Iso→is-hlevel 1 eqv $
      Σ-is-hlevel 1 (Π-is-hlevel 1 λ _ → A.has-is-set _ _) λ _ →
      Σ-is-hlevel 1 (Π-is-hlevel³ 1 λ _ _ _ → A.has-is-set _ _) λ _ →
      Π-is-hlevel³ 1 λ _ _ _ → Π-is-hlevel 1 λ _ → ×-is-hlevel 1 A.≤-thin $
      Π-is-hlevel 1 λ _ → B.has-is-set _ _
      where unquoteDecl eqv = declare-record-iso eqv (quote is-right-displacement-action)

record Right-displacement-action
  {o r o′ r′}
  (A : Poset o r) (B : Displacement-algebra o′ r′)
  : Type (o ⊔ r ⊔ o′ ⊔ r′)
  where
  field
    hom : ⌞ A ⌟ → ⌞ B ⌟ → ⌞ A ⌟
    has-is-action : is-right-displacement-action A B hom

  open is-right-displacement-action has-is-action public

module _ where
  open Right-displacement-action

  Right-displacement-action-path
    : ∀ {o r o′ r′}
    → {A : Poset o r} {B : Displacement-algebra o′ r′}
    → (α β : Right-displacement-action A B)
    → (∀ a b → α .hom a b ≡ β .hom a b)
    → α ≡ β
  Right-displacement-action-path α β p i .hom a b = p a b i
  Right-displacement-action-path α β p i .has-is-action =
    is-prop→pathp (λ i → is-right-displacement-action-is-prop _ _ (λ a b → p a b i))
      (α .has-is-action)
      (β .has-is-action) i

instance
  Right-actionlike-displacement-action
    : ∀ {o r o' r'}
    → Right-actionlike (Right-displacement-action {o} {r} {o'} {r'})
  Right-actionlike.⟦ Right-actionlike-displacement-action ⟧ʳ =
    Right-displacement-action.hom
  Right-actionlike-displacement-action .Right-actionlike.extʳ =
    Right-displacement-action-path _ _

--------------------------------------------------------------------------------
-- Builders

record make-displacement-algebra
  {o r} (A : Poset o r)
  : Type (o ⊔ r)
  where
  no-eta-equality
  open Poset A
  field
    ε : ⌞ A ⌟
    _⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟
    idl : ∀ {x} → ε ⊗ x ≡ x
    idr : ∀ {x} → x ⊗ ε ≡ x
    associative : ∀ {x y z} → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
    left-strict-invariant : ∀ {x y z} → y ≤ z
      → ((x ⊗ y) ≤ (x ⊗ z)) × ((x ⊗ y) ≡ (x ⊗ z) → y ≡ z)

module _ where
  open Displacement-algebra
  open Displacement-algebra-on
  open is-displacement-algebra
  open make-displacement-algebra

  to-displacement-algebra
    : ∀ {o r} {A : Poset o r}
    → make-displacement-algebra A
    → Displacement-algebra o r
  to-displacement-algebra {A = A} mk .poset = A
  to-displacement-algebra {A = A} mk .displacement-algebra-on .ε = mk .ε
  to-displacement-algebra {A = A} mk .displacement-algebra-on ._⊗_ = mk ._⊗_
  to-displacement-algebra {A = A} mk .displacement-algebra-on .has-is-displacement-algebra .has-is-monoid .has-is-semigroup .has-is-magma .is-magma.has-is-set = Poset.has-is-set A
  to-displacement-algebra {A = A} mk .displacement-algebra-on .has-is-displacement-algebra .has-is-monoid .has-is-semigroup .associative = mk .associative
  to-displacement-algebra {A = A} mk .displacement-algebra-on .has-is-displacement-algebra .has-is-monoid .idl = mk .idl
  to-displacement-algebra {A = A} mk .displacement-algebra-on .has-is-displacement-algebra .has-is-monoid .idr = mk .idr
  to-displacement-algebra {A = A} mk .displacement-algebra-on .has-is-displacement-algebra .left-strict-invariant = mk .left-strict-invariant

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
    mono : ∀ x y → x X.≤ y → into x Y.≤ into y
    inj : ∀ {x y} → into x ≡ into y → x ≡ y

  strict-mono : ∀ x y → x X.≤ y → (into x Y.≤ into y) × (into x ≡ into y → x ≡ y)
  strict-mono x y x≤y = mono x y x≤y , inj


module _ where
  open is-displacement-algebra-hom
  open is-displacement-subalgebra
  open make-displacement-subalgebra
  open Displacement-algebra-hom

  to-displacement-subalgebra
    : ∀ {o r o' r'}
    → {X : Displacement-algebra o r}
    → {Y : Displacement-algebra o' r'}
    → make-displacement-subalgebra X Y
    → is-displacement-subalgebra X Y
  to-displacement-subalgebra mk .into .strict-hom .Strictly-monotone.hom = mk .into
  to-displacement-subalgebra mk .into .strict-hom .Strictly-monotone.strict-mono =
    make-displacement-subalgebra.strict-mono mk _ _
  to-displacement-subalgebra mk .into .has-is-displacement-hom .pres-ε = mk .pres-ε
  to-displacement-subalgebra mk .into .has-is-displacement-hom .pres-⊗ = mk .pres-⊗
  to-displacement-subalgebra mk .inj = mk .inj
