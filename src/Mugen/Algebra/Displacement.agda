module Mugen.Algebra.Displacement where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

import Mugen.Data.Nat as Nat


private variable
  o r : Level
  A : Type o

--------------------------------------------------------------------------------
-- Displacement Algebras

record is-displacement-algebra {A : Type o} (_<_ : A → A → Type r) (ε : A) (_⊗_ : A → A → A) : Type (o ⊔ r) where
  field
    has-monoid : is-monoid ε _⊗_
    has-strict-order : is-strict-order _<_
    left-invariant : ∀ {x y z} → y < z → (x ⊗ y) < (x ⊗ z)

  open is-monoid has-monoid public
  open is-strict-order has-strict-order public renaming (has-prop to <-is-prop)

  left-invariant-≤ : ∀ {x y z} → y ≤ z → (x ⊗ y) ≤ (x ⊗ z)
  left-invariant-≤ {x = x} (inl p) = inl (ap (x ⊗_) p)
  left-invariant-≤ (inr y<z) = inr (left-invariant y<z)

record DisplacementAlgebra-on {o : Level} (r : Level) (A : Type o) : Type (o ⊔ lsuc r) where
  field
    _<_ : A → A → Type r
    ε : A
    _⊗_ : A → A → A
    has-displacement-algebra : is-displacement-algebra _<_ ε _⊗_

  open is-displacement-algebra has-displacement-algebra public

DisplacementAlgebra : ∀ o r → Type (lsuc o ⊔ lsuc r)
DisplacementAlgebra o r = SetStructure (DisplacementAlgebra-on {o} r)

DA→SO : DisplacementAlgebra o r → StrictOrder o r
⌞ DA→SO 𝒟 ⌟ =  ⌞ 𝒟 ⌟ 
DA→SO 𝒟 .structure .StrictOrder-on._<_ = DisplacementAlgebra-on._<_ (structure 𝒟)
DA→SO 𝒟 .structure .StrictOrder-on.has-is-strict-order = DisplacementAlgebra-on.has-strict-order (structure 𝒟)
⌞ DA→SO 𝒟 ⌟-set = ⌞ 𝒟 ⌟-set 

module DisplacementAlgebra {o r} (𝒟 : DisplacementAlgebra o r) where
  open DisplacementAlgebra-on (structure 𝒟) public
  open StrictOrder (DA→SO 𝒟) using (≤-is-prop) public

_[_<_]ᵈ : (𝒟 : DisplacementAlgebra o r) → ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → Type r
𝒟 [ x < y ]ᵈ = DisplacementAlgebra-on._<_ (structure 𝒟) x y

_[_≤_]ᵈ : (𝒟 : DisplacementAlgebra o r) → ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → Type (o ⊔ r)
𝒟 [ x ≤ y ]ᵈ = DisplacementAlgebra-on._≤_ (structure 𝒟) x y

--------------------------------------------------------------------------------
-- Homomorphisms of Displacement Algebras

record is-displacement-algebra-homomorphism
  {o r}
  (X Y : DisplacementAlgebra o r)
  (f : ⌞ X ⌟ → ⌞ Y ⌟)
  : Type (o ⊔ r)
  where
  private
    module X = DisplacementAlgebra X
    module Y = DisplacementAlgebra Y
  field
    pres-ε : f X.ε ≡ Y.ε
    pres-⊗ : ∀ (x y : ⌞ X ⌟) → f (x X.⊗ y) ≡ (f x Y.⊗ f y)
    strictly-mono : ∀ {x y} → X [ x < y ]ᵈ → Y [ f x < f y ]ᵈ

  mono : ∀ {x y} → X [ x ≤ y ]ᵈ → Y [ f x ≤ f y ]ᵈ
  mono (inl x≡y) = inl (ap f x≡y)
  mono (inr x<y) = inr (strictly-mono x<y)

DisplacementAlgebra-hom : ∀ {o r} → (X Y : DisplacementAlgebra o r) → Type (o ⊔ r)
DisplacementAlgebra-hom = Homomorphism is-displacement-algebra-homomorphism

module DisplacementAlgebra-hom
  {o r} {X Y : DisplacementAlgebra o r}
  (f : DisplacementAlgebra-hom X Y)
  where

  open is-displacement-algebra-homomorphism (homo f) public

displacement-hom-∘ : ∀ {o r} {X Y Z : DisplacementAlgebra o r}
                     → DisplacementAlgebra-hom Y Z
                     → DisplacementAlgebra-hom X Y
                     → DisplacementAlgebra-hom X Z
displacement-hom-∘ {X = X} {Z = Z} f g = f∘g
  where
    open is-displacement-algebra-homomorphism

    f∘g : DisplacementAlgebra-hom X Z
    f∘g ⟨$⟩ x = f ⟨$⟩ (g ⟨$⟩ x)
    f∘g .homo .pres-ε = ap (f ⟨$⟩_) (g .homo .pres-ε) ∙ f .homo .pres-ε 
    f∘g .homo .pres-⊗ x y = ap (f ⟨$⟩_) (g .homo .pres-⊗ x y) ∙ f .homo .pres-⊗ (g ⟨$⟩ x) (g ⟨$⟩ y)
    f∘g .homo .strictly-mono x<y = f .homo .strictly-mono (g .homo .strictly-mono x<y)

--------------------------------------------------------------------------------
-- Subalgebras of Displacement Algebras

record is-displacement-subalgebra {o r} (X Y : DisplacementAlgebra o r) : Type (o ⊔ r) where
  field
    into : DisplacementAlgebra-hom X Y
    inj  : ∀ {x y} → into ⟨$⟩ x ≡ into ⟨$⟩ y → x ≡ y

  open DisplacementAlgebra-hom into public

module _ where
  open is-displacement-subalgebra

  is-displacement-subalgebra-trans : ∀ {o r} {X Y Z : DisplacementAlgebra o r}
                                     → is-displacement-subalgebra X Y
                                     → is-displacement-subalgebra Y Z
                                     → is-displacement-subalgebra X Z
  is-displacement-subalgebra-trans f g .into = displacement-hom-∘ (g .into) (f .into)
  is-displacement-subalgebra-trans f g .is-displacement-subalgebra.inj p = f .inj (g .inj p)

--------------------------------------------------------------------------------
-- Some Properties of Displacement Algebras

module _ {o r} {A : Type o} {_<_ : A → A → Type r} {ε : A} {_⊗_ : A → A → A}
         (A-set : is-set A)
         (𝒟 : is-displacement-algebra _<_ ε _⊗_) where

  private
    module 𝒟 = is-displacement-algebra 𝒟
    open 𝒟 using (_≤_)

  is-right-invariant-displacement-algebra→is-ordered-monoid : (∀ {x y z} → x ≤ y → (x ⊗ z) ≤ (y ⊗ z))
                                                            → is-ordered-monoid _≤_ ε _⊗_
  is-right-invariant-displacement-algebra→is-ordered-monoid ≤-invariantr .is-ordered-monoid.has-monoid =
    𝒟.has-monoid
  is-right-invariant-displacement-algebra→is-ordered-monoid ≤-invariantr .is-ordered-monoid.has-partial-order =
    is-strict-order→is-partial-order A-set 𝒟.has-strict-order
  is-right-invariant-displacement-algebra→is-ordered-monoid ≤-invariantr .is-ordered-monoid.invariant w≤y x≤z =
    𝒟.≤-trans (≤-invariantr w≤y) (𝒟.left-invariant-≤ x≤z)

  is-displacement-algebra×is-ordered-monoid→is-right-invariant : is-ordered-monoid _≤_ ε _⊗_
                                                               → (∀ {x y z} → x ≤ y → (x ⊗ z) ≤ (y ⊗ z))
  is-displacement-algebra×is-ordered-monoid→is-right-invariant ordered-monoid x≤y =
    is-ordered-monoid.invariant ordered-monoid x≤y (inl refl)

--------------------------------------------------------------------------------
-- Augmentations of Displacement Algebras

module _ {o r} (𝒟 : DisplacementAlgebra o r) where

  open DisplacementAlgebra 𝒟

  -- Ordered Monoids
  has-ordered-monoid : Type (o ⊔ r)
  has-ordered-monoid = is-ordered-monoid _≤_ ε _⊗_

  right-invariant→has-ordered-monoid : (∀ {x y z} → x ≤ y → (x ⊗ z) ≤ (y ⊗ z)) → has-ordered-monoid
  right-invariant→has-ordered-monoid =
    is-right-invariant-displacement-algebra→is-ordered-monoid ⌞ 𝒟 ⌟-set has-displacement-algebra

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

preserves-joins : {X Y : DisplacementAlgebra o r} (X-joins : has-joins X) (Y-joins : has-joins Y) → (f : DisplacementAlgebra-hom X Y) → Type o
preserves-joins X Y f = ∀ x y → f ⟨$⟩ X .join x y ≡ Y .join (f ⟨$⟩ x) (f ⟨$⟩ y)
  where
    open has-joins

preserves-bottom : {X Y : DisplacementAlgebra o r} (X-joins : has-bottom X) (Y-joins : has-bottom Y) → (f : DisplacementAlgebra-hom X Y) → Type o
preserves-bottom X Y f = f ⟨$⟩ X .bot ≡ Y .bot
  where
    open has-bottom

record is-displacement-subsemilattice {X Y : DisplacementAlgebra o r} (X-joins : has-joins X) (Y-joins : has-joins Y) : Type (o ⊔ r) where
  field
    has-displacement-subalgebra : is-displacement-subalgebra X Y

  open is-displacement-subalgebra has-displacement-subalgebra public
  field
    pres-joins : preserves-joins X-joins Y-joins into

--------------------------------------------------------------------------------
-- Displacement Actions

record is-right-displacement-action {o r o′ r′} (A : StrictOrder o r) (B : DisplacementAlgebra o′ r′) (α : ⌞ A ⌟ → ⌞ B ⌟ → ⌞ A ⌟) : Type (o ⊔ r ⊔ o′ ⊔ r′) where
  open DisplacementAlgebra-on (structure B) using (ε; _⊗_)
  field
    identity  : ∀ (a : ⌞ A ⌟) → α a ε ≡ a
    compat    : ∀ (a : ⌞ A ⌟) (x y : ⌞ B ⌟) → α (α a x) y ≡ α a (x ⊗ y)
    invariant : ∀ (a : ⌞ A ⌟) (x y : ⌞ B ⌟) → B [ x < y ]ᵈ → A [ α a x < α a y ]

RightDisplacementAction : ∀ {o r o′ r′} (A : StrictOrder o r) (B : DisplacementAlgebra o′ r′) → Type (o ⊔ r ⊔ o′ ⊔ r′)
RightDisplacementAction = RightAction is-right-displacement-action

module RightDisplacementAction {o r o′ r′} {A : StrictOrder o r} {B : DisplacementAlgebra o′ r′} (α : RightDisplacementAction A B) where
  open is-right-displacement-action (is-action α) public
