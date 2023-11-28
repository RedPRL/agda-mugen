open import Mugen.Prelude

import Order.Base

module Mugen.Order.Poset where


--------------------------------------------------------------------------------
-- Partial Orders
--
-- We opt not to use the 1labs definition of partial order,
-- as it is defined as a structure on sets.
--
-- As this development is heavily focused on order theory,
-- it is much nicer to view partial orders/strict orders as
-- the primitive objects, and everything else as structures
-- atop that.

open Order.Base using
  ( is-partial-order
  ; is-partial-order-is-prop
  ; Poset-on
  ; Poset-on-pathp
  ; Poset-on-path
  ) public

strict : ∀ {o r} {A : Type o} (_≤_ : A → A → Type r) → A → A → Type (o ⊔ r)
strict _≤_ x y = (x ≤ y) × (¬ (x ≡ y))

abstract
  strict-is-prop : ∀ {o r} {A : Type o} (_≤_ : A → A → Type r) {x y : A}
    → is-prop (x ≤ y) → is-prop (strict _≤_ x y)
  strict-is-prop _≤_ hl = ×-is-hlevel 1 hl $ hlevel 1

record Poset o r : Type (lsuc (o ⊔ r)) where
  field
    Ob       : Type o
    poset-on : Poset-on r Ob
  open Poset-on poset-on public

  instance
    ≤-hlevel : ∀ {x y} {n} → H-Level (x ≤ y) (suc n)
    ≤-hlevel = prop-instance ≤-thin

  abstract
    =→≤ : ∀ {x y} → x ≡ y → x ≤ y
    =→≤ x=y = subst (_ ≤_) x=y ≤-refl

    ≤+=→≤ : ∀ {x y z} → x ≤ y → y ≡ z → x ≤ z
    ≤+=→≤ x≤y y≡z = subst (_ ≤_) y≡z x≤y

    =+≤→≤ : ∀ {x y z} → x ≡ y → y ≤ z → x ≤ z
    =+≤→≤ x≡y y≤z = subst (_≤ _) (sym x≡y) y≤z

  _<_ : Ob → Ob → Type (o ⊔ r)
  _<_ = strict _≤_

  abstract
    <-irrefl : ∀ {x} → x < x → ⊥
    <-irrefl (_ , x≠x) = x≠x refl

    <-trans : ∀ {x y z} → x < y → y < z → x < z
    <-trans {y = y} (x≤y , x≠y) (y≤z , y≠z) =
      ≤-trans x≤y y≤z ,
      λ x=z → x≠y $ ≤-antisym x≤y (subst (y ≤_) (sym x=z) y≤z)

    <-is-prop : ∀ {x y} → is-prop (x < y)
    <-is-prop {x} {y} = strict-is-prop _≤_ $ ≤-thin {x} {y}

    <-asym : ∀ {x y} → x < y → y < x → ⊥
    <-asym x<y y<x = <-irrefl (<-trans x<y y<x)

    =+<→< : ∀ {x y z} → x ≡ y → y < z → x < z
    =+<→< x≡y y<z = subst (λ ϕ → ϕ < _) (sym x≡y) y<z

    <+=→< : ∀ {x y z} → x < y → y ≡ z → x < z
    <+=→< x<y y≡z = subst (λ ϕ → _ < ϕ) y≡z x<y

    <→≱ : ∀ {x y} → x < y → y ≤ x → ⊥
    <→≱ (x≤y , x≠y) y≤x = x≠y $ ≤-antisym x≤y y≤x

    ≤→≯ : ∀ {x y} → x ≤ y → y < x → ⊥
    ≤→≯ x≤y (y≤x , y≠x) = y≠x $ ≤-antisym y≤x x≤y

    <→≠ : ∀ {x y} → x < y → x ≡ y → ⊥
    <→≠ x<y x≡y = <-irrefl $ subst (λ ϕ → ϕ < _) x≡y x<y

    <→≤ : ∀ {x y} → x < y → x ≤ y
    <→≤ (x≤y , _) = x≤y

    ≤+<→< : ∀ {x y z} → x ≤ y → y < z → x < z
    ≤+<→< x≤y (y≤z , _) .fst = ≤-trans x≤y y≤z
    ≤+<→< x≤y y<z .snd x=z = <→≱ y<z (=+≤→≤ (sym x=z) x≤y)

    <+≤→< : ∀ {x y z} → x < y → y ≤ z → x < z
    <+≤→< (x≤y , _) y≤z .fst = ≤-trans x≤y y≤z
    <+≤→< x<y y≤z .snd x=z = <→≱ x<y (≤+=→≤ y≤z (sym x=z))

    ≤-antisym'-l : ∀ {x y z} → x ≤ y → y ≤ z → x ≡ z → x ≡ y
    ≤-antisym'-l {y = y} x≤y y≤z x=z = ≤-antisym x≤y $ subst (y ≤_) (sym x=z) y≤z

    ≤-antisym'-r : ∀ {x y z} → x ≤ y → y ≤ z → x ≡ z → y ≡ z
    ≤-antisym'-r {y = y} x≤y y≤z x=z = ≤-antisym y≤z $ subst (_≤ y) x=z x≤y

instance
  Underlying-Poset : ∀ {o r} → Underlying (Poset o r)
  Underlying-Poset = record { ⌞_⌟ = Poset.Ob }

--------------------------------------------------------------------------------
-- Monotonic Maps

module _ {o o' r r'} (X : Poset o r) (Y : Poset o' r') where
  private
    module X = Poset X
    module Y = Poset Y

  is-monotone : ∀ (f : ⌞ X ⌟ → ⌞ Y ⌟) → Type _
  is-monotone f = ∀ {x y} → x X.≤ y → f x Y.≤ f y

  abstract
    is-monotone-is-prop : ∀ (f : ⌞ X ⌟ → ⌞ Y ⌟) → is-prop (is-monotone f)
    is-monotone-is-prop f =
      Π-is-hlevel' 1 λ _ → Π-is-hlevel' 1 λ _ →
      Π-is-hlevel 1 λ _ → Y.≤-thin

record Monotone
  {o o' r r'}
  (X : Poset o r) (Y : Poset o' r')
  : Type (o ⊔ o' ⊔ r ⊔ r')
  where
  no-eta-equality
  field
    hom : ⌞ X ⌟ → ⌞ Y ⌟
    mono : is-monotone X Y hom

--------------------------------------------------------------------------------
-- Strictly Monotonic Maps

module _ {o r o' r'} (X : Poset o r) (Y : Poset o' r') where
  private
    module X = Poset X
    module Y = Poset Y

  -- Favonia: this definition is constructively stronger than preserving '<'
  -- TODO: investigate why or why not this should agree with the nice definition
  -- in a displacement algebra.
  is-strictly-monotone : ∀ (f : ⌞ X ⌟ → ⌞ Y ⌟) → Type (o ⊔ r ⊔ o' ⊔ r')
  is-strictly-monotone f = ∀ {x y} → x X.≤ y → (f x Y.≤ f y) × (f x ≡ f y → x ≡ y)

  abstract
    is-strictly-monotone-is-prop : ∀ (f : ⌞ X ⌟ → ⌞ Y ⌟) → is-prop (is-strictly-monotone f)
    is-strictly-monotone-is-prop f =
      Π-is-hlevel' 1 λ x → Π-is-hlevel' 1 λ y → Π-is-hlevel 1 λ _ →
      ×-is-hlevel 1 Y.≤-thin (Π-is-hlevel 1 λ _ → X.has-is-set x y)

record Strictly-monotone {o o' r r'} (X : Poset o r) (Y : Poset o' r') : Type (o ⊔ o' ⊔ r ⊔ r') where
  no-eta-equality
  private
    module X = Poset X
    module Y = Poset Y
  field
    hom : ⌞ X ⌟ → ⌞ Y ⌟
    strict-mono : is-strictly-monotone X Y hom

  mono : ∀ {x y} → x X.≤ y → hom x Y.≤ hom y
  mono x≤y = fst (strict-mono x≤y)

  inj-on-related : ∀ {x y} → x X.≤ y → hom x ≡ hom y → x ≡ y
  inj-on-related x≤y = snd (strict-mono x≤y)

Strictly-monotone-path
  : ∀ {o r o' r'} {X : Poset o r} {Y : Poset o' r'}
  → (f g : Strictly-monotone X Y)
  → f .Strictly-monotone.hom ≡ g .Strictly-monotone.hom
  → f ≡ g
Strictly-monotone-path f g p i .Strictly-monotone.hom = p i
Strictly-monotone-path {X = X} {Y = Y} f g p i .Strictly-monotone.strict-mono =
  is-prop→pathp (λ i → is-strictly-monotone-is-prop X Y (p i))
    (f .Strictly-monotone.strict-mono) (g .Strictly-monotone.strict-mono) i

module _ {o r o' r'} {X : Poset o r} {Y : Poset o' r'} where
  private
    module X = Poset X
    module Y = Poset Y

  instance
    strict-monotone-hlevel : ∀ {n} → H-Level (Strictly-monotone X Y) (2 + n)
    strict-monotone-hlevel = basic-instance 2 $
      Iso→is-hlevel 2 eqv $
      Σ-is-hlevel 2 (Π-is-hlevel 2 λ _ → Y.has-is-set) λ f →
      is-hlevel-suc 1 $ is-strictly-monotone-is-prop X Y f
      where unquoteDecl eqv = declare-record-iso eqv (quote Strictly-monotone)

Extensional-Strictly-monotone
  : ∀ {o r o' r' ℓ} {X : Poset o r} {Y : Poset o' r'}
  → ⦃ sa : Extensional (⌞ X ⌟ → ⌞ Y ⌟) ℓ ⦄
  → Extensional (Strictly-monotone X Y) ℓ
Extensional-Strictly-monotone {Y = Y} ⦃ sa ⦄ =
  injection→extensional!
    {sb = Π-is-hlevel 2 λ _ → Poset.has-is-set Y}
    {f = Strictly-monotone.hom}
    (Strictly-monotone-path _ _) sa

instance
  Funlike-strictly-monotone
    : ∀ {o r o' r'}
    → Funlike (Strictly-monotone {o} {r} {o'} {r'})
  Funlike-strictly-monotone .Funlike.au = Underlying-Poset
  Funlike-strictly-monotone .Funlike.bu = Underlying-Poset
  Funlike-strictly-monotone .Funlike._#_ = Strictly-monotone.hom

  extensionality-strictly-monotone
    : ∀ {o r o' r'} {X : Poset o r} {Y : Poset o' r'}
    → Extensionality (Strictly-monotone X Y)
  extensionality-strictly-monotone = record { lemma = quote Extensional-Strictly-monotone }

strictly-monotone-id : ∀ {o r} {X : Poset o r} → Strictly-monotone X X
strictly-monotone-id .Strictly-monotone.hom x = x
strictly-monotone-id .Strictly-monotone.strict-mono p = p , λ q → q

strictly-monotone-∘
  : ∀ {o r o' r' o'' r''} {X : Poset o r} {Y : Poset o' r'} {Z : Poset o'' r''}
  → Strictly-monotone Y Z
  → Strictly-monotone X Y
  → Strictly-monotone X Z
strictly-monotone-∘ f g .Strictly-monotone.hom x = f # (g # x)
strictly-monotone-∘ f g .Strictly-monotone.strict-mono p =
  let gx≤gy = Strictly-monotone.mono g p in
  Strictly-monotone.mono f gx≤gy ,
  λ q → Strictly-monotone.inj-on-related g p $ Strictly-monotone.inj-on-related f gx≤gy q

--------------------------------------------------------------------------------
-- Builders

record make-poset {o} (r : Level) (A : Type o) : Type (o ⊔ lsuc r) where
  no-eta-equality
  field
    _≤_ : A → A → Type r
    ≤-thin : ∀ {x y} → is-prop (x ≤ y)
    ≤-refl : ∀ {x} → x ≤ x
    ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y

to-poset : ∀ {o r} {A : Type o} → make-poset r A → Poset o r
to-poset {A = A} mk .Poset.Ob = A
to-poset mk .Poset.poset-on .Poset-on._≤_ =
  mk .make-poset._≤_
to-poset mk .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-thin =
  mk .make-poset.≤-thin
to-poset mk .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-refl =
  mk .make-poset.≤-refl
to-poset mk .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-trans =
  mk .make-poset.≤-trans
to-poset mk .Poset.poset-on .Poset-on.has-is-poset .is-partial-order.≤-antisym =
  mk .make-poset.≤-antisym
