open import Mugen.Prelude
import Mugen.Order.Reasoning as Reasoning

module Mugen.Order.StrictOrder where

private variable
  o o' o'' r r' r'' : Level

--------------------------------------------------------------------------------
-- Strictly Monotonic Maps

record Strictly-monotone (X : Poset o r) (Y : Poset o' r') : Type (o ⊔ o' ⊔ r ⊔ r') where
  no-eta-equality
  private
    module X = Reasoning X
    module Y = Reasoning Y
  field
    hom : ⌞ X ⌟ → ⌞ Y ⌟

    -- Preserving relative inequalities
    --
    -- This is morally '∀ {x y} → x X.≤[ x ≡ y ] y → hom x Y.≤[ x ≡ y ] hom y'
    -- and is equivalent to pres-≤[] below.
    pres-≤[]-equal : ∀ {x y} → x X.≤ y → hom x Y.≤[ x ≡ y ] hom y

  abstract
    pres-≤[] : ∀ {K : Type r''} {x y} → x X.≤[ K ] y → hom x Y.≤[ K ] hom y
    pres-≤[] x<y = Y.≤[]-map (x<y .snd) $ pres-≤[]-equal (x<y .fst)

    pres-≤ : ∀ {x y} → x X.≤ y → hom x Y.≤ hom y
    pres-≤ x≤y = Y.<→≤ $ pres-≤[] (X.≤→≤[]-equal x≤y)

    injective-on-related : ∀ {x y} → x X.≤ y → hom x ≡ hom y → x ≡ y
    injective-on-related x≤y = pres-≤[] (x≤y , λ p → p) .snd

abstract
  Strictly-monotone-path
    : ∀ {X : Poset o r} {Y : Poset o' r'}
    → (f g : Strictly-monotone X Y)
    → f .Strictly-monotone.hom ≡ g .Strictly-monotone.hom
    → f ≡ g
  Strictly-monotone-path f g p i .Strictly-monotone.hom = p i
  Strictly-monotone-path {X = X} {Y = Y} f g p i .Strictly-monotone.pres-≤[]-equal {x} {y} x<y =
    let module X = Reasoning X
        module Y = Reasoning Y
    in
    is-prop→pathp
      (λ i → Y.≤[]-is-hlevel {x = p i x} {y = p i y} 0 (X.Ob-is-set x y))
      (f .Strictly-monotone.pres-≤[]-equal x<y) (g .Strictly-monotone.pres-≤[]-equal x<y) i

module _ {X : Poset o r} {Y : Poset o' r'} where
  private
    module X = Reasoning X
    module Y = Reasoning Y

  abstract instance
    H-Level-Strictly-monotone : ∀ {n} → H-Level (Strictly-monotone X Y) (2 + n)
    H-Level-Strictly-monotone = basic-instance 2 $ Iso→is-hlevel 2 eqv (hlevel 2)
      where unquoteDecl eqv = declare-record-iso eqv (quote Strictly-monotone)

instance
  Extensional-Strictly-monotone
    : ∀ {ℓ} {X : Poset o r} {Y : Poset o' r'}
    → ⦃ sa : Extensional (⌞ X ⌟ → ⌞ Y ⌟) ℓ ⦄
    → Extensional (Strictly-monotone X Y) ℓ
  Extensional-Strictly-monotone {Y = Y} ⦃ sa ⦄ =
    injection→extensional!
      {f = Strictly-monotone.hom}
      (Strictly-monotone-path _ _) sa

  Funlike-Strictly-monotone : {X : Poset o r} {Y : Poset o' r'} → Funlike (Strictly-monotone X Y) ⌞ X ⌟ λ _ → ⌞ Y ⌟
  Funlike-Strictly-monotone .Funlike._#_ = Strictly-monotone.hom

strictly-monotone-id : ∀ {o r} {X : Poset o r} → Strictly-monotone X X
strictly-monotone-id .Strictly-monotone.hom x = x
strictly-monotone-id .Strictly-monotone.pres-≤[]-equal p = p , λ p → p

strictly-monotone-∘
  : ∀ {X : Poset o r} {Y : Poset o' r'} {Z : Poset o'' r''}
  → Strictly-monotone Y Z
  → Strictly-monotone X Y
  → Strictly-monotone X Z
strictly-monotone-∘ f g .Strictly-monotone.hom x = f # (g # x)
strictly-monotone-∘ {X = X} f g .Strictly-monotone.pres-≤[]-equal {x} {y} p =
  Strictly-monotone.pres-≤[] f $ Strictly-monotone.pres-≤[] g (p , λ p → p)
  where open Reasoning X

--------------------------------------------------------------------------------
-- A Subobject in StrictOrders

record is-full-subposet
  {A : Poset o r} {B : Poset o' r'}
  (f : Strictly-monotone A B)
  : Type (o ⊔ o' ⊔ r ⊔ r')
  where
  no-eta-equality
  private
    module A = Reasoning A
    module B = Reasoning B
  field
    injective : ∀ {x y : ⌞ A ⌟} → f # x ≡ f # y → x ≡ y
    full : ∀ {x y : ⌞ A ⌟} → f # x B.≤ f # y → x A.≤ y

module _
  {A : Poset o r} {B : Poset o' r'} {C : Poset o'' r''}
  where
  open is-full-subposet

  ∘-is-full-subposet
    : {f : Strictly-monotone B C} {g : Strictly-monotone A B}
    → is-full-subposet f
    → is-full-subposet g
    → is-full-subposet (strictly-monotone-∘ f g)
  ∘-is-full-subposet {f = f} {g = g} f-sub g-sub .is-full-subposet.injective =
    g-sub .is-full-subposet.injective ⊙ f-sub .is-full-subposet.injective
  ∘-is-full-subposet {f = f} {g = g} f-sub g-sub .is-full-subposet.full =
    g-sub .is-full-subposet.full ⊙ f-sub .is-full-subposet.full

--------------------------------------------------------------------------------
-- Builders for Subobjects in StrictOrders

record represents-full-subposet
  {A : Type o} (B : Poset o' r')
  (f : A →  ⌞ B ⌟)
  : Type (o ⊔ o')
  where
  no-eta-equality
  private
    module B = Reasoning B
  field
    injective : ∀ {x y} → f x ≡ f y → x ≡ y

  poset : Poset o r'
  poset .Poset.Ob = A
  poset .Poset._≤_ x y = f x B.≤ f y
  poset .Poset.≤-thin = B.≤-thin
  poset .Poset.≤-refl = B.≤-refl
  poset .Poset.≤-trans = B.≤-trans
  poset .Poset.≤-antisym p q = injective $ B.≤-antisym p q

  strictly-monotone : Strictly-monotone poset B
  strictly-monotone .Strictly-monotone.hom = f
  strictly-monotone .Strictly-monotone.pres-≤[]-equal p .fst = p
  strictly-monotone .Strictly-monotone.pres-≤[]-equal p .snd = injective

  has-is-full-subposet : is-full-subposet strictly-monotone
  has-is-full-subposet .is-full-subposet.injective = injective
  has-is-full-subposet .is-full-subposet.full p = p
