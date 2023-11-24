open import Mugen.Prelude
open import Mugen.Order.Poset

module Mugen.Order.StrictOrder where

--------------------------------------------------------------------------------
-- Strict Orders

non-strict : ∀ {o r} {A : Type o} (R : A → A → Type r) → A → A → Type (o ⊔ r)
non-strict R x y = (x ≡ y) ⊎ (R x y)

record is-strict-order {o r} {A : Type o} (_<_ : A → A → Type r) : Type (o ⊔ r) where
  no-eta-equality
  field
    <-irrefl : ∀ {x} → x < x → ⊥
    <-trans : ∀ {x y z} → x < y → y < z → x < z
    <-thin : ∀ {x y} → is-prop (x < y)
    has-is-set : is-set A

  <-asym : ∀ {x y} → x < y → y < x → ⊥
  <-asym x<y y<x = <-irrefl (<-trans x<y y<x)

  ≡+<→< : ∀ {x y z} → x ≡ y → y < z → x < z
  ≡+<→< x≡y y<z = subst (λ ϕ → ϕ < _) (sym x≡y) y<z

  <+≡→< : ∀ {x y z} → x < y → y ≡ z → x < z
  <+≡→< x<y y≡z = subst (λ ϕ → _ < ϕ) y≡z x<y

  <→≠ : ∀ {x y} → x < y → x ≡ y → ⊥
  <→≠ x<y x≡y = <-irrefl $ subst (λ ϕ → ϕ < _) x≡y x<y

  instance
    <-hlevel : ∀ {x y} {n} → H-Level (x < y) (suc n)
    <-hlevel = prop-instance <-thin

  _≤_ : A → A → Type (o ⊔ r)
  x ≤ y = non-strict _<_ x y

  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans (inl p) (inl q) = inl (p ∙ q)
  ≤-trans (inl p) (inr y<z) = inr (≡+<→< p y<z)
  ≤-trans (inr x<y) (inl q) = inr (<+≡→< x<y q)
  ≤-trans (inr x<y) (inr y<z) = inr (<-trans x<y y<z)

  ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
  ≤-antisym (inl x≡y) y≤x = x≡y
  ≤-antisym (inr x<y) (inl y≡x) = sym y≡x
  ≤-antisym (inr x<y) (inr y<x) = absurd (<-irrefl (<-trans x<y y<x))

  <→≤ : ∀ {x y} → x < y → x ≤ y
  <→≤ x<y = inr x<y

  ≤-refl : ∀ {x} → x ≤ x
  ≤-refl = inl refl

  ≤-thin : ∀ {x y} → is-prop (x ≤ y)
  ≤-thin =
    disjoint-⊎-is-prop (has-is-set _ _) <-thin
      (λ (p , q) → <→≠ q p)

  has-is-partial-order : is-partial-order _≤_
  has-is-partial-order .is-partial-order.≤-thin = ≤-thin
  has-is-partial-order .is-partial-order.≤-refl = ≤-refl
  has-is-partial-order .is-partial-order.≤-trans = ≤-trans
  has-is-partial-order .is-partial-order.≤-antisym = ≤-antisym

  ≤+<→< : ∀ {x y z} → x ≤ y → y < z → x < z
  ≤+<→< (inl x≡y) y<z = ≡+<→< x≡y y<z
  ≤+<→< (inr x<y) y<z = <-trans x<y y<z

  <+≤→< : ∀ {x y z} → x < y → y ≤ z → x < z
  <+≤→< x<y (inl y≡z) = <+≡→< x<y y≡z
  <+≤→< x<y (inr y<z) = <-trans x<y y<z

  ≤+≡→≤ : ∀ {x y z} → x ≤ y → y ≡ z → x ≤ z
  ≤+≡→≤ x≤y y≡z = subst (λ ϕ → _ ≤ ϕ) y≡z x≤y

  ≡+≤→≤ : ∀ {x y z} → x ≡ y → y ≤ z → x ≤ z
  ≡+≤→≤ x≡y y≤z = subst (λ ϕ → ϕ ≤ _) (sym x≡y) y≤z

  ≤+≮→= : ∀ {x y} → x ≤ y → ¬ (x < y) → x ≡ y
  ≤+≮→= (inl x=y) x≮y = x=y
  ≤+≮→= (inr x<y) x≮y = absurd (x≮y x<y)

  ≤+≠→< : ∀ {x y} → x ≤ y → ¬ (x ≡ y) → x < y
  ≤+≠→< (inl x=y) x≠y = absurd (x≠y x=y)
  ≤+≠→< (inr x<y) x≠y = x<y


instance
  is-strict-order-hlevel : ∀ {o r} {A : Type o} {_<_ : A → A → Type r} {n}
                           → H-Level (is-strict-order _<_) (suc n)
  is-strict-order-hlevel = prop-instance λ x →
     let open is-strict-order x in
     is-hlevel≃ 1 (Iso→Equiv eqv) hlevel! x
     where unquoteDecl eqv = declare-record-iso eqv (quote is-strict-order)

record Strict-order-on {o : Level} (r : Level) (A : Type o) : Type (o ⊔ lsuc r) where
  no-eta-equality
  field
    _<_ : A → A → Type r
    has-is-strict-order : is-strict-order _<_

  open is-strict-order has-is-strict-order public

  poset-on : Poset-on (o ⊔ r) A
  poset-on .Poset-on._≤_ = _≤_
  poset-on .Poset-on.has-is-poset = has-is-partial-order

record Strict-order (o r : Level) : Type (lsuc (o ⊔ r)) where
  no-eta-equality
  field
    Ob : Type o
    strict-order-on : Strict-order-on r Ob

  open Strict-order-on strict-order-on public

  poset : Poset o (o ⊔ r)
  poset .Poset.Ob = Ob
  poset .Poset.poset-on = poset-on

instance
  Underlying-Strict-order : ∀ {o r} → Underlying (Strict-order o r)
  Underlying-Strict-order .Underlying.ℓ-underlying = _
  Underlying.⌞ Underlying-Strict-order ⌟ = Strict-order.Ob

private variable
  o r : Level
  X Y Z : Strict-order o r

--------------------------------------------------------------------------------
-- Strictly Monotonic Maps

module _ {o r o' r'} (X : Strict-order o r) (Y : Strict-order o' r') where
  private
    module X = Strict-order X
    module Y = Strict-order Y

  is-strictly-monotone : ∀ (f : ⌞ X ⌟ → ⌞ Y ⌟) → Type (o ⊔ r ⊔ r')
  is-strictly-monotone f = ∀ {x y} →  x X.< y → f x Y.< f y

  is-strictly-monotone-is-prop : ∀ (f : ⌞ X ⌟ → ⌞ Y ⌟) → is-prop (is-strictly-monotone f)
  is-strictly-monotone-is-prop f = hlevel!

record Strictly-monotone
  {o o' r r'}
  (X : Strict-order o r) (Y : Strict-order o' r')
  : Type (o ⊔ o' ⊔ r ⊔ r')
  where
  no-eta-equality
  private
    module X = Strict-order X
    module Y = Strict-order Y
  field
    hom : ⌞ X ⌟ → ⌞ Y ⌟
    strict-mono : is-strictly-monotone X Y hom

  mono : ∀ {x y} → x X.≤ y → hom x Y.≤ hom y
  mono (inl p) = inl (ap hom p)
  mono (inr p) = inr (strict-mono p)

open Strictly-monotone

Strictly-monotone-path
  : ∀ {o r o' r'}
  → {X : Strict-order o r} {Y : Strict-order o' r'}
  → (f g : Strictly-monotone X Y)
  → f .hom ≡ g .hom
  → f ≡ g
Strictly-monotone-path f g p i .hom = p i
Strictly-monotone-path {Y = Y} f g p i .strict-mono {x = x} {y = y} q =
  is-prop→pathp (λ i → Strict-order.<-thin Y {x = p i x} {y = p i y})
    (f .strict-mono q)
    (g .strict-mono q) i

module _ {o r o' r'} {X : Strict-order o r} {Y : Strict-order o' r'} where
  private
    module X = Strict-order X
    module Y = Strict-order Y

  instance
    strict-monotone-hlevel : ∀ {n} → H-Level (Strictly-monotone X Y) (2 + n)
    strict-monotone-hlevel = basic-instance 2 $
      Iso→is-hlevel 2 eqv $
      Σ-is-hlevel 2 (Π-is-hlevel 2 λ _ → Y.has-is-set) λ f →
      is-hlevel-suc 1 (is-strictly-monotone-is-prop X Y f)
      where unquoteDecl eqv = declare-record-iso eqv (quote Strictly-monotone)

Extensional-Strictly-monotone
  : ∀ {o r o' r' ℓ} {X : Strict-order o r} {Y : Strict-order o' r'}
  → ⦃ sa : Extensional (⌞ X ⌟ → ⌞ Y ⌟) ℓ ⦄
  → Extensional (Strictly-monotone X Y) ℓ
Extensional-Strictly-monotone {Y = Y} ⦃ sa ⦄ =
  injection→extensional!
    {sb = Π-is-hlevel 2 λ _ → Strict-order.has-is-set Y}
    {f = Strictly-monotone.hom}
    (Strictly-monotone-path _ _) sa

instance
  Funlike-strictly-monotone
    : ∀ {o r o' r'}
    → Funlike (Strictly-monotone {o} {r} {o'} {r'})
  Funlike-strictly-monotone .Funlike.au = Underlying-Strict-order
  Funlike-strictly-monotone .Funlike.bu = Underlying-Strict-order
  Funlike-strictly-monotone .Funlike._#_ = Strictly-monotone.hom

  extensionality-strictly-monotone
    : ∀ {o r o' r'} {X : Strict-order o r} {Y : Strict-order o' r'}
    → Extensionality (Strictly-monotone X Y)
  extensionality-strictly-monotone = record { lemma = quote Extensional-Strictly-monotone }


strictly-monotone-id : Strictly-monotone X X
strictly-monotone-id .hom x = x
strictly-monotone-id .strict-mono p = p

strictly-monotone-∘
  : Strictly-monotone Y Z
  → Strictly-monotone X Y
  → Strictly-monotone X Z
strictly-monotone-∘ f g .hom x = f # (g # x)
strictly-monotone-∘ f g .strict-mono p =
  f .strict-mono (g .strict-mono p)

--------------------------------------------------------------------------------
-- Decidability

data Tri {o r} {A : Type o} (_<_ : A → A → Type r) (x y : A) : Type (o ⊔ r) where
  lt : x < y → Tri _<_ x y
  eq : x ≡ y → Tri _<_ x y
  gt : y < x → Tri _<_ x y

module _ {o r} {A : Type o} {_<_ : A → A → Type r} where


  tri-elim : ∀ {ℓ x y} (P : Tri _<_ x y → Type ℓ)
             → ((p : x < y) → P (lt p))
             → ((p : x ≡ y) → P (eq p))
             → ((p : y < x) → P (gt p))
             → (t : Tri _<_ x y) → P t
  tri-elim P plt peq pgt (lt x) = plt x
  tri-elim P plt peq pgt (eq x) = peq x
  tri-elim P plt peq pgt (gt x) = pgt x

  tri-rec : ∀ {ℓ x y} {R : Type ℓ} → R → R → R → Tri _<_ x y → R
  tri-rec rlt req rgt (lt x) = rlt
  tri-rec rlt req rgt (eq x) = req
  tri-rec rlt req rgt (gt x) = rgt

--------------------------------------------------------------------------------
-- Builders

record make-strict-order {o} (r : Level) (A : Type o) : Type (o ⊔ lsuc r) where
  no-eta-equality
  field
    _<_ : A → A → Type r
    <-irrefl : ∀ {x} → x < x → ⊥
    <-trans : ∀ {x y z} → x < y → y < z → x < z
    <-thin : ∀ {x y} → is-prop (x < y)
    has-is-set : is-set A

to-strict-order
  : ∀ {o r} {A : Type o}
  → make-strict-order r A → Strict-order o r
to-strict-order {A = A} mk .Strict-order.Ob = A
to-strict-order mk .Strict-order.strict-order-on .Strict-order-on._<_ =
  make-strict-order._<_ mk
to-strict-order mk .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.<-irrefl =
  make-strict-order.<-irrefl mk
to-strict-order mk .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.<-trans =
  make-strict-order.<-trans mk
to-strict-order mk .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.<-thin =
  make-strict-order.<-thin mk
to-strict-order mk .Strict-order.strict-order-on .Strict-order-on.has-is-strict-order .is-strict-order.has-is-set =
  make-strict-order.has-is-set mk
