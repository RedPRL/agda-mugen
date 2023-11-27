module Mugen.Algebra.Displacement.Product where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Order.Poset
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid

--------------------------------------------------------------------------------
-- Products
-- Section 3.3.3
--
-- We can take the product of 2 displacement algebras. Algebraic structure
-- is given by the product of monoids, and ordering is given by the product of the
-- orders.

module Product {o r} (𝒟₁ 𝒟₂ : Displacement-algebra o r) where
  private
    module 𝒟₁ = Displacement-algebra 𝒟₁
    module 𝒟₂ = Displacement-algebra 𝒟₂

  --------------------------------------------------------------------------------
  -- Algebra

  _⊗×_ : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟ → ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟ → ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟
  (d1 , d2) ⊗× (d1′ , d2′) = (d1 𝒟₁.⊗ d1′) , (d2 𝒟₂.⊗ d2′)

  ε× : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟
  ε× = 𝒟₁.ε , 𝒟₂.ε

  ⊗×-associative : ∀ (x y z : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) → (x ⊗× (y ⊗× z)) ≡ ((x ⊗× y) ⊗× z)
  ⊗×-associative (d1 , d2) (d1′ , d2′) (d1″ , d2″) i = 𝒟₁.associative {d1} {d1′} {d1″} i , 𝒟₂.associative {d2} {d2′} {d2″} i

  ⊗×-idl : ∀ (x : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) → (ε× ⊗× x) ≡ x
  ⊗×-idl (d1 , d2) i = 𝒟₁.idl {d1} i , 𝒟₂.idl {d2} i

  ⊗×-idr : ∀ (x : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) → (x ⊗× ε×) ≡ x
  ⊗×-idr (d1 , d2) i = 𝒟₁.idr {d1} i , 𝒟₂.idr {d2} i

  ⊗×-is-magma : is-magma _⊗×_
  ⊗×-is-magma .has-is-set = ×-is-hlevel 2 𝒟₁.has-is-set 𝒟₂.has-is-set

  ⊗×-is-semigroup : is-semigroup _⊗×_
  ⊗×-is-semigroup .has-is-magma = ⊗×-is-magma
  ⊗×-is-semigroup .associative {x} {y} {z} = ⊗×-associative x y z

  ⊗×-is-monoid : is-monoid ε× _⊗×_
  ⊗×-is-monoid .has-is-semigroup = ⊗×-is-semigroup
  ⊗×-is-monoid .idl {x} = ⊗×-idl x
  ⊗×-is-monoid .idr {x} = ⊗×-idr x

  --------------------------------------------------------------------------------
  -- Ordering

  _⊗×≤_ : ∀ (x :  ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) (y : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) → Type r
  _⊗×≤_ x y = (fst x 𝒟₁.≤ fst y) × (snd x 𝒟₂.≤ snd y)

  ⊗×≤-thin : ∀ x y → is-prop (x ⊗×≤ y)
  ⊗×≤-thin x y = hlevel 1

  ⊗×≤-refl : ∀ x → x ⊗×≤ x
  ⊗×≤-refl x = 𝒟₁.≤-refl , 𝒟₂.≤-refl

  ⊗×≤-trans : ∀ x y z → x ⊗×≤ y → y ⊗×≤ z → x ⊗×≤ z
  ⊗×≤-trans _ _ _ (x1≤y1 , x2≤y2) (y1≤z1 , y2≤z2) = 𝒟₁.≤-trans x1≤y1 y1≤z1 , 𝒟₂.≤-trans x2≤y2 y2≤z2

  ⊗×≤-antisym : ∀ x y → x ⊗×≤ y → y ⊗×≤ x → x ≡ y
  ⊗×≤-antisym _ _ (x1≤y1 , x2≤y2) (y1≤z1 , y2≤z2) i = 𝒟₁.≤-antisym x1≤y1 y1≤z1 i , 𝒟₂.≤-antisym x2≤y2 y2≤z2 i

  --------------------------------------------------------------------------------
  -- Left Invariance

  ⊗×-left-invariant : ∀ (x y z : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) → y ⊗×≤ z → (x ⊗× y) ⊗×≤ (x ⊗× z)
  ⊗×-left-invariant _ _ _ (y1≤z1 , y2≤z2) = 𝒟₁.≤-left-invariant y1≤z1 , 𝒟₂.≤-left-invariant y2≤z2

  ⊗×-injr-on-⊗≤ : ∀ (x y z : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) → y ⊗×≤ z → (x ⊗× y) ≡ (x ⊗× z) → y ≡ z
  ⊗×-injr-on-⊗≤ _ _ _ (y1≤z1 , y2≤z2) p i = 𝒟₁.injr-on-≤ y1≤z1 (ap fst p) i , 𝒟₂.injr-on-≤ y2≤z2 (ap snd p) i

_⊗ᵈ_
  : ∀ {o r}
  → Displacement-algebra o r
  → Displacement-algebra o r
  → Displacement-algebra o r
𝒟₁ ⊗ᵈ 𝒟₂ = to-displacement-algebra mk where
  open Product 𝒟₁ 𝒟₂
  module 𝒟₁ = Displacement-algebra 𝒟₁
  module 𝒟₂ = Displacement-algebra 𝒟₂

  mk-poset : make-poset _ _
  mk-poset .make-poset._≤_ = _⊗×≤_
  mk-poset .make-poset.≤-thin = ⊗×≤-thin _ _
  mk-poset .make-poset.≤-refl = ⊗×≤-refl _
  mk-poset .make-poset.≤-trans = ⊗×≤-trans _ _ _
  mk-poset .make-poset.≤-antisym = ⊗×≤-antisym _ _

  mk : make-displacement-algebra (to-poset mk-poset)
  mk .make-displacement-algebra.ε = ε×
  mk .make-displacement-algebra._⊗_ = _⊗×_
  mk .make-displacement-algebra.idl = ⊗×-idl _
  mk .make-displacement-algebra.idr = ⊗×-idr _
  mk .make-displacement-algebra.associative = ⊗×-associative _ _ _
  mk .make-displacement-algebra.≤-left-invariant = ⊗×-left-invariant _ _ _
  mk .make-displacement-algebra.injr-on-≤ = ⊗×-injr-on-⊗≤ _ _ _

module ProductProperties
  {o r} {𝒟₁ 𝒟₂ : Displacement-algebra o r}
  where
  private
    module 𝒟₁ = Displacement-algebra 𝒟₁
    module 𝒟₂ = Displacement-algebra 𝒟₂
    open Product 𝒟₁ 𝒟₂

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  ⊗×-has-ordered-monoid : has-ordered-monoid 𝒟₁ → has-ordered-monoid 𝒟₂ → has-ordered-monoid (𝒟₁ ⊗ᵈ 𝒟₂)
  ⊗×-has-ordered-monoid 𝒟₁-ordered-monoid 𝒟₂-ordered-monoid =
    right-invariant→has-ordered-monoid (𝒟₁ ⊗ᵈ 𝒟₂) λ x≤y → ⊗×-right-invariant _ _ _ x≤y
    where
      module 𝒟₁-ordered-monoid = is-ordered-monoid (𝒟₁-ordered-monoid)
      module 𝒟₂-ordered-monoid = is-ordered-monoid (𝒟₂-ordered-monoid)

      ⊗×-right-invariant : ∀ x y z → x ⊗×≤ y → (x ⊗× z) ⊗×≤ (y ⊗× z)
      ⊗×-right-invariant x y z (x1≤y1 , x2≤y2) =
        𝒟₁-ordered-monoid.right-invariant x1≤y1 , 𝒟₂-ordered-monoid.right-invariant x2≤y2

  --------------------------------------------------------------------------------
  -- Joins

  ⊗×-has-joins : has-joins 𝒟₁ → has-joins 𝒟₂ → has-joins (𝒟₁ ⊗ᵈ 𝒟₂)
  ⊗×-has-joins 𝒟₁-joins 𝒟₂-joins = joins
    where
      module 𝒟₁-joins = has-joins 𝒟₁-joins
      module 𝒟₂-joins = has-joins 𝒟₂-joins

      joins : has-joins (𝒟₁ ⊗ᵈ 𝒟₂)
      joins .has-joins.join (x1 , x2) (y1 , y2) = (𝒟₁-joins.join x1 y1) , (𝒟₂-joins.join x2 y2)
      joins .has-joins.joinl = 𝒟₁-joins.joinl , 𝒟₂-joins.joinl
      joins .has-joins.joinr = 𝒟₁-joins.joinr , 𝒟₂-joins.joinr
      joins .has-joins.universal {x1 , x2} {y1 , y2} {z1 , z2} x≤z y≤z =
        𝒟₁-joins.universal (fst x≤z) (fst y≤z) ,
        𝒟₂-joins.universal (snd x≤z) (snd y≤z)

  --------------------------------------------------------------------------------
  -- Bottoms

  ⊗×-has-bottom : has-bottom 𝒟₁ → has-bottom 𝒟₂ → has-bottom (𝒟₁ ⊗ᵈ 𝒟₂)
  ⊗×-has-bottom 𝒟₁-bottom 𝒟₂-bottom = bottom
    where
      module 𝒟₁-bottom = has-bottom (𝒟₁-bottom)
      module 𝒟₂-bottom = has-bottom (𝒟₂-bottom)

      bottom : has-bottom (𝒟₁ ⊗ᵈ 𝒟₂)
      bottom .has-bottom.bot = 𝒟₁-bottom.bot , 𝒟₂-bottom.bot
      bottom .has-bottom.is-bottom (x1 , x2) = 𝒟₁-bottom.is-bottom x1 , 𝒟₂-bottom.is-bottom x2
