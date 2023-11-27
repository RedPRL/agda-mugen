module Mugen.Algebra.Displacement.Lexicographic where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Order.Poset
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Product
open import Mugen.Algebra.OrderedMonoid

--------------------------------------------------------------------------------
-- Lexicographic Products
-- Section 3.3.4
--
-- The lexicographic product of 2 displacement algebras consists of their product
-- as monoids, as well as their lexicographic product as orders.
--
-- As noted earlier, algebraic structure is given by the product of monoids, so we don't need
-- to prove that here.

module Lex {o r} (𝒟₁ 𝒟₂ : Displacement-algebra o r) where
  private
    module 𝒟₁ = Displacement-algebra 𝒟₁
    module 𝒟₂ = Displacement-algebra 𝒟₂
    open Product 𝒟₁ 𝒟₂

  --------------------------------------------------------------------------------
  -- Ordering

  lex≤ : ∀ (x : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) (y : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) → Type (o ⊔ r)
  lex≤ x y = (fst x 𝒟₁.≤ fst y) × (fst x ≡ fst y → snd x 𝒟₂.≤ snd y)

  lex≤-refl : ∀ x → lex≤ x x
  lex≤-refl x = 𝒟₁.≤-refl , λ _ → 𝒟₂.≤-refl

  lex≤-trans : ∀ x y z → lex≤ x y → lex≤ y z → lex≤ x z
  lex≤-trans x y z (x1≤y1 , x2≤y2) (y1≤z1 , y2≤z2) =
    𝒟₁.≤-trans x1≤y1 y1≤z1 , λ x1=z1 →
    𝒟₂.≤-trans
      (x2≤y2 (𝒟₁.≤-antisym'-l x1≤y1 y1≤z1 x1=z1))
      (y2≤z2 (𝒟₁.≤-antisym'-r x1≤y1 y1≤z1 x1=z1))

  lex≤-antisym : ∀ x y → lex≤ x y → lex≤ y x → x ≡ y
  lex≤-antisym x y (x1≤y1 , x2≤y2) (y1≤x1 , y2≤x2) i =
    let x1=y1 = 𝒟₁.≤-antisym x1≤y1 y1≤x1 in
    x1=y1 i , 𝒟₂.≤-antisym (x2≤y2 x1=y1) (y2≤x2 (sym x1=y1)) i

  lex≤-thin : ∀ x y → is-prop (lex≤ x y)
  lex≤-thin x y = hlevel 1

  --------------------------------------------------------------------------------
  -- Left Invariance

  lex-left-invariant : ∀ x y z → lex≤ y z → lex≤ (x ⊗× y) (x ⊗× z)
  lex-left-invariant x y z (y1≤z1 , y2≤z2) =
    𝒟₁.≤-left-invariant y1≤z1 , λ p → 𝒟₂.≤-left-invariant (y2≤z2 (𝒟₁.injr-on-≤ y1≤z1 p))

  lex-injr-on-≤ : ∀ x y z → lex≤ y z → (x ⊗× y) ≡ (x ⊗× z) → y ≡ z
  lex-injr-on-≤ x y z (y1≤z1 , y2≤z2) p i =
    let y1=z1 = 𝒟₁.injr-on-≤ y1≤z1 (ap fst p) in
    y1=z1 i , 𝒟₂.injr-on-≤ (y2≤z2 y1=z1) (ap snd p) i

Lex
  : ∀ {o r}
  → Displacement-algebra o r → Displacement-algebra o r
  → Displacement-algebra o (o ⊔ r)
Lex {o = o} {r = r} 𝒟₁ 𝒟₂ = to-displacement-algebra displacement
  where
    open Product 𝒟₁ 𝒟₂
    open Lex 𝒟₁ 𝒟₂
    module 𝒟₁ = Displacement-algebra 𝒟₁
    module 𝒟₂ = Displacement-algebra 𝒟₂

    order : make-poset (o ⊔ r) (⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟)
    order .make-poset._≤_ = lex≤
    order .make-poset.≤-thin = lex≤-thin _ _
    order .make-poset.≤-refl = lex≤-refl _
    order .make-poset.≤-trans = lex≤-trans _ _ _
    order .make-poset.≤-antisym = lex≤-antisym _ _

    displacement : make-displacement-algebra (to-poset order)
    displacement .make-displacement-algebra.ε = ε×
    displacement .make-displacement-algebra._⊗_ = _⊗×_
    displacement .make-displacement-algebra.idl = ⊗×-idl _
    displacement .make-displacement-algebra.idr = ⊗×-idr _
    displacement .make-displacement-algebra.associative = ⊗×-associative _ _ _
    displacement .make-displacement-algebra.≤-left-invariant = lex-left-invariant _ _ _
    displacement .make-displacement-algebra.injr-on-≤ = lex-injr-on-≤ _ _ _

module LexProperties {o r} {𝒟₁ 𝒟₂ : Displacement-algebra o r} where
  private
    module 𝒟₁ = Displacement-algebra 𝒟₁
    module 𝒟₂ = Displacement-algebra 𝒟₂
    open Product 𝒟₁ 𝒟₂
    open Lex 𝒟₁ 𝒟₂

  --------------------------------------------------------------------------------
  -- Ordered Monoids

  -- When 𝒟₁ is /strictly/ right invariant and 𝒟₂ is an ordered monoid, then 'Lex 𝒟₁ 𝒟₂' is also an ordered monoid.
  lex-has-ordered-monoid
    : has-ordered-monoid 𝒟₁
    → (∀ {x y z} → x 𝒟₁.≤ y → (x 𝒟₁.⊗ z) ≡ (y 𝒟₁.⊗ z) → x ≡ y)
    → has-ordered-monoid 𝒟₂
    → has-ordered-monoid (Lex 𝒟₁ 𝒟₂)
  lex-has-ordered-monoid 𝒟₁-ordered-monoid 𝒟₁-injl-on-≤ 𝒟₂-ordered-monoid =
    right-invariant→has-ordered-monoid (Lex 𝒟₁ 𝒟₂) λ x≤y → lex-right-invariant _ _ _ x≤y
    where
      module 𝒟₁-ordered-monoid = is-ordered-monoid (𝒟₁-ordered-monoid)
      module 𝒟₂-ordered-monoid = is-ordered-monoid (𝒟₂-ordered-monoid)

      lex-right-invariant : ∀ x y z → lex≤ x y → lex≤ (x ⊗× z) (y ⊗× z)
      lex-right-invariant x y z (y1≤z1 , y2≤z2) =
        𝒟₁-ordered-monoid.right-invariant y1≤z1 , λ p →
        𝒟₂-ordered-monoid.right-invariant (y2≤z2 (𝒟₁-injl-on-≤ y1≤z1 p))

  --------------------------------------------------------------------------------
  -- Joins

  -- If the following conditions are true, then 'Lex 𝒟₁ 𝒟₂' has joins:
  -- (1) Both 𝒟₁ and 𝒟₂ have joins.
  -- (2) 𝒟₂ has a bottom.
  -- (3) It's decidable in 𝒟₁ whether an element is equal to its join with another element.
  lex-has-joins
    : (𝒟₁-joins : has-joins 𝒟₁) (let module 𝒟₁-joins = has-joins 𝒟₁-joins)
    → (∀ x y → Dec (x ≡ 𝒟₁-joins.join x y) × Dec (y ≡ 𝒟₁-joins.join x y))
    → (𝒟₂-joins : has-joins 𝒟₂) → has-bottom 𝒟₂
    → has-joins (Lex 𝒟₁ 𝒟₂)
                
  lex-has-joins 𝒟₁-joins _≡∨₁?_ 𝒟₂-joins 𝒟₂-bottom = joins
    where
      module 𝒟₁-joins = has-joins 𝒟₁-joins
      module 𝒟₂-joins = has-joins 𝒟₂-joins
      module 𝒟₂-bottom = has-bottom 𝒟₂-bottom

      joins : has-joins (Lex 𝒟₁ 𝒟₂)
      joins .has-joins.join (x1 , x2) (y1 , y2) with x1 ≡∨₁? y1
      ... | yes _ , yes _ = 𝒟₁-joins.join x1 y1 , 𝒟₂-joins.join x2 y2
      ... | yes _ , no  _ = 𝒟₁-joins.join x1 y1 , x2
      ... | no  _ , yes _ = 𝒟₁-joins.join x1 y1 , y2
      ... | no  _ , no  _ = 𝒟₁-joins.join x1 y1 , 𝒟₂-bottom.bot
      joins .has-joins.joinl {x1 , _} {y1 , _} with x1 ≡∨₁? y1
      ... | yes x1=x1∨y1 , yes _ = 𝒟₁-joins.joinl , λ _ → 𝒟₂-joins.joinl
      ... | yes x1=x1∨y1 , no  _ = 𝒟₁-joins.joinl , λ _ → 𝒟₂.≤-refl
      ... | no  x1≠x1∨y1 , yes _ = 𝒟₁-joins.joinl , λ x1≡x1∨y1 → absurd (x1≠x1∨y1 x1≡x1∨y1)
      ... | no  x1≠x1∨y1 , no  _ = 𝒟₁-joins.joinl , λ x1≡x1∨y1 → absurd (x1≠x1∨y1 x1≡x1∨y1)
      joins .has-joins.joinr {x1 , _} {y1 , _} with x1 ≡∨₁? y1
      ... | yes _ , yes y1=x1∨y1 = 𝒟₁-joins.joinr , λ _ → 𝒟₂-joins.joinr
      ... | yes _ , no  y1≠x1∨y1 = 𝒟₁-joins.joinr , λ y1≡x1∨y1 → absurd (y1≠x1∨y1 y1≡x1∨y1)
      ... | no  _ , yes y1=x1∨y1 = 𝒟₁-joins.joinr , λ _ → 𝒟₂.≤-refl
      ... | no  _ , no  y1≠x1∨y1 = 𝒟₁-joins.joinr , λ y1≡x1∨y1 → absurd (y1≠x1∨y1 y1≡x1∨y1)
      joins .has-joins.universal {x1 , _} {y1 , _} {_ , z2} x≤z y≤z with x1 ≡∨₁? y1
      ... | yes x1=x1∨y1 , yes y1=x1∨y1 =
        𝒟₁-joins.universal (x≤z .fst) (y≤z .fst) , λ x1vy1=z1 →
        𝒟₂-joins.universal (x≤z .snd (x1=x1∨y1 ∙ x1vy1=z1)) (y≤z .snd (y1=x1∨y1 ∙ x1vy1=z1))
      ... | yes x1=x1∨y1 , no  y1≠x1∨y1 =
        𝒟₁-joins.universal (x≤z .fst) (y≤z .fst) , λ x1vy1=z1 → x≤z .snd (x1=x1∨y1 ∙ x1vy1=z1)
      ... | no  x1≠x1∨y1 , yes y1=x1∨y1 =
        𝒟₁-joins.universal (x≤z .fst) (y≤z .fst) , λ x1vy1=z1 → y≤z .snd (y1=x1∨y1 ∙ x1vy1=z1)
      ... | no  x1≠x1∨y1 , no  y1≠x1∨y1 =
        𝒟₁-joins.universal (x≤z .fst) (y≤z .fst) , λ x1vy1=z1 → 𝒟₂-bottom.is-bottom z2

  --------------------------------------------------------------------------------
  -- Bottoms

  lex-has-bottom : has-bottom 𝒟₁ → has-bottom 𝒟₂ → has-bottom (Lex 𝒟₁ 𝒟₂)
  lex-has-bottom 𝒟₁-bottom 𝒟₂-bottom = bottom
    where
      module 𝒟₁-bottom = has-bottom (𝒟₁-bottom)
      module 𝒟₂-bottom = has-bottom (𝒟₂-bottom)

      bottom : has-bottom (Lex 𝒟₁ 𝒟₂)
      bottom .has-bottom.bot = 𝒟₁-bottom.bot , 𝒟₂-bottom.bot
      bottom .has-bottom.is-bottom (x1 , x2) = 𝒟₁-bottom.is-bottom x1 , λ _ → 𝒟₂-bottom.is-bottom x2
