module Mugen.Algebra.Displacement.Product where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

--------------------------------------------------------------------------------
-- Products
--
-- We can take the product of 2 displacement algebras. Algebraic structure
-- is given by the product of monoids, and ordering is given by the product of the
-- orders.

module Product {o r} (𝒟₁ 𝒟₂ : DisplacementAlgebra o r) where
  private
    module 𝒟₁ = DisplacementAlgebra 𝒟₁
    module 𝒟₂ = DisplacementAlgebra 𝒟₂

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
  ⊗×-is-magma .has-is-set = ×-is-hlevel 2 ⌞ 𝒟₁ ⌟-set ⌞ 𝒟₂ ⌟-set

  ⊗×-is-semigroup : is-semigroup _⊗×_
  ⊗×-is-semigroup .has-is-magma = ⊗×-is-magma
  ⊗×-is-semigroup .associative {x} {y} {z} = ⊗×-associative x y z

  ⊗×-is-monoid : is-monoid ε× _⊗×_
  ⊗×-is-monoid .has-is-semigroup = ⊗×-is-semigroup
  ⊗×-is-monoid .idl {x} = ⊗×-idl x
  ⊗×-is-monoid .idr {x} = ⊗×-idr x

  --------------------------------------------------------------------------------
  -- Ordering

  -- NOTE: This version of the definition doesn't require a propositional truncation.
  data _⊗×<_ (x :  ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) (y : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) : Type (o ⊔ r) where
    fst< : 𝒟₁ [ fst x < fst y ]ᵈ → snd x ≡ snd y → x ⊗×< y
    snd< : fst x ≡ fst y → 𝒟₂ [ snd x < snd y ]ᵈ → x ⊗×< y
    both< :  𝒟₁ [ fst x < fst y ]ᵈ → 𝒟₂ [ snd x < snd y ]ᵈ → x ⊗×< y

  -- Instead of working with 'non-strict _⊗×<_', we define an equivalent
  -- definition that is simpler to handle.
  record _⊗×≤_ (x :  ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) (y : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) : Type (o ⊔ r) where
    constructor both≤
    field
      fst≤ : 𝒟₁ [ fst x ≤ fst y ]ᵈ
      snd≤ : 𝒟₂ [ snd x ≤ snd y ]ᵈ

  open _⊗×≤_ public

  from-⊗×≤ : ∀ {x y} → x ⊗×≤ y → non-strict _⊗×<_ x y
  from-⊗×≤ (both≤ (inl x1≡y1) (inl x2≡y2)) = inl (Σ-pathp x1≡y1 x2≡y2)
  from-⊗×≤ (both≤ (inl x1≡y1) (inr x2<y2)) = inr (snd< x1≡y1 x2<y2)
  from-⊗×≤ (both≤ (inr x1<y1) (inl x2≡y2)) = inr (fst< x1<y1 x2≡y2)
  from-⊗×≤ (both≤ (inr x1<y1) (inr x2<y2)) = inr (both< x1<y1 x2<y2)

  to-⊗×≤ : ∀ {x y} → non-strict _⊗×<_ x y → x ⊗×≤ y
  to-⊗×≤ (inl x≡y) = both≤ (inl (ap fst x≡y)) (inl (ap snd x≡y))
  to-⊗×≤ (inr (fst< x1<y1 x2≡y2)) = both≤ (inr x1<y1) (inl x2≡y2)
  to-⊗×≤ (inr (snd< x1≡y1 x2<y2)) = both≤ (inl x1≡y1) (inr x2<y2)
  to-⊗×≤ (inr (both< x1<y1 x2<y2)) = both≤ (inr x1<y1) (inr x2<y2)

  ⊗×<-irrefl : ∀ x → x ⊗×< x → ⊥
  ⊗×<-irrefl _ (fst< x1<x1 _) = 𝒟₁.irrefl x1<x1
  ⊗×<-irrefl _ (snd< _ x2<x2) = 𝒟₂.irrefl x2<x2
  ⊗×<-irrefl _ (both< x1<x1 x2<x2) = 𝒟₁.irrefl x1<x1

  ⊗×<-trans : ∀ x y z → x ⊗×< y → y ⊗×< z → x ⊗×< z
  ⊗×<-trans _ _ _ (fst< x1<y1 x2≡y2)  (fst< y1<z1 y2≡z2)  = fst< (𝒟₁.trans x1<y1 y1<z1) (x2≡y2 ∙ y2≡z2)
  ⊗×<-trans _ _ _ (fst< x1<y1 x2≡y2)  (snd< y1≡z1 y2<z2)  = both< (𝒟₁.≡-transr x1<y1 y1≡z1) (𝒟₂.≡-transl x2≡y2 y2<z2)
  ⊗×<-trans _ _ _ (fst< x1<y1 x2≡y2)  (both< y1<z1 y2<z2) = both< (𝒟₁.trans x1<y1 y1<z1) (𝒟₂.≡-transl x2≡y2 y2<z2)
  ⊗×<-trans _ _ _ (snd< x1≡y1 x2<y2)  (fst< y1<z1 y2≡z2)  = both< (𝒟₁.≡-transl x1≡y1 y1<z1) (𝒟₂.≡-transr x2<y2 y2≡z2)
  ⊗×<-trans _ _ _ (snd< x1≡y1 x2<y2)  (snd< y1≡z1 y2<z2)  = snd< (x1≡y1 ∙ y1≡z1) (𝒟₂.trans x2<y2 y2<z2)
  ⊗×<-trans _ _ _ (snd< x1≡y1 x2<y2)  (both< y1<z1 y2<z2) = both< (𝒟₁.≡-transl x1≡y1 y1<z1) (𝒟₂.trans x2<y2 y2<z2)
  ⊗×<-trans _ _ _ (both< x1<y1 x2<y2) (fst< y1<z1 y2≡z2)  = both< (𝒟₁.trans x1<y1 y1<z1) (𝒟₂.≡-transr x2<y2 y2≡z2)
  ⊗×<-trans _ _ _ (both< x1<y1 x2<y2) (snd< y1≡z1 y2<z2)  = both< (𝒟₁.≡-transr x1<y1 y1≡z1) (𝒟₂.trans x2<y2 y2<z2)
  ⊗×<-trans _ _ _ (both< x1<y1 x2<y2) (both< y1<z1 y2<z2) = both< (𝒟₁.trans x1<y1 y1<z1) (𝒟₂.trans x2<y2 y2<z2)

  ⊗×<-is-prop : ∀ x y → is-prop (x ⊗×< y)
  ⊗×<-is-prop _ _ (fst< x1<y1 x2≡y2)  (fst< x1<y1′ x2≡y2′)  = ap₂ fst< (𝒟₁.<-is-prop x1<y1 x1<y1′) (⌞ 𝒟₂ ⌟-set _ _ x2≡y2 x2≡y2′)
  ⊗×<-is-prop _ _ (fst< x1<y1 _)      (snd< x1≡y1 _)        = absurd (𝒟₁.irrefl (𝒟₁.≡-transr x1<y1 (sym x1≡y1)))
  ⊗×<-is-prop _ _ (fst< _ x2≡y2)      (both< _ x2<y2)       = absurd (𝒟₂.irrefl (𝒟₂.≡-transr x2<y2 (sym x2≡y2)))
  ⊗×<-is-prop _ _ (snd< x1≡y1 _)      (fst< x1<y1 _)        = absurd (𝒟₁.irrefl (𝒟₁.≡-transr x1<y1 (sym x1≡y1)))
  ⊗×<-is-prop _ _ (snd< x1≡y1 x2<y2)  (snd< x1≡y1′ x2<y2′)  = ap₂ snd< ( ⌞ 𝒟₁ ⌟-set _ _ x1≡y1 x1≡y1′) (𝒟₂.<-is-prop x2<y2 x2<y2′)
  ⊗×<-is-prop _ _ (snd< x1≡y1 _)      (both< x1<y1 _)       = absurd (𝒟₁.irrefl (𝒟₁.≡-transr x1<y1 (sym x1≡y1)))
  ⊗×<-is-prop _ _ (both< _ x2<y2)     (fst< _ x2≡y2)        = absurd (𝒟₂.irrefl (𝒟₂.≡-transr x2<y2 (sym x2≡y2)))
  ⊗×<-is-prop _ _ (both< x1<y1 _)     (snd< x1≡y1 _)        = absurd (𝒟₁.irrefl (𝒟₁.≡-transr x1<y1 (sym x1≡y1)))
  ⊗×<-is-prop _ _ (both< x1<y1 x2<y2) (both< x1<y1′ x2<y2′) = ap₂ both< (𝒟₁.<-is-prop x1<y1 x1<y1′) (𝒟₂.<-is-prop x2<y2 x2<y2′)

  ⊗×<-is-strict-order : is-strict-order _⊗×<_
  ⊗×<-is-strict-order .is-strict-order.irrefl {x} = ⊗×<-irrefl x
  ⊗×<-is-strict-order .is-strict-order.trans {x} {y} {z} = ⊗×<-trans x y z
  ⊗×<-is-strict-order .is-strict-order.has-prop {x} {y} = ⊗×<-is-prop x y

  --------------------------------------------------------------------------------
  -- Left Invariance

  ⊗×-left-invariant : ∀ (x y z : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) → y ⊗×< z → (x ⊗× y) ⊗×< (x ⊗× z)
  ⊗×-left-invariant (x1 , x2) (y1 , y2) (z1 , z2) (fst< y1<z1 y2≡z2)  = fst< (𝒟₁.left-invariant y1<z1) (ap (x2 𝒟₂.⊗_) y2≡z2)
  ⊗×-left-invariant (x1 , x2) (y1 , y2) (z1 , z2) (snd< y1≡z1 y2<z2)  = snd< (ap (x1 𝒟₁.⊗_) y1≡z1) (𝒟₂.left-invariant y2<z2)
  ⊗×-left-invariant (x1 , x2) (y1 , y2) (z1 , z2) (both< y1<z1 y2<z2) = both< (𝒟₁.left-invariant y1<z1) (𝒟₂.left-invariant y2<z2)

  ⊗×-is-displacement-algebra : is-displacement-algebra _⊗×<_ ε× _⊗×_
  ⊗×-is-displacement-algebra .is-displacement-algebra.has-monoid = ⊗×-is-monoid
  ⊗×-is-displacement-algebra .is-displacement-algebra.has-strict-order = ⊗×<-is-strict-order
  ⊗×-is-displacement-algebra .is-displacement-algebra.left-invariant {x} {y} {z} = ⊗×-left-invariant x y z

_⊗ᵈ_ : ∀ {o r} → DisplacementAlgebra o r → DisplacementAlgebra o r → DisplacementAlgebra o (o ⊔ r)
⌞ 𝒟₁ ⊗ᵈ 𝒟₂ ⌟ =  ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟
(𝒟₁ ⊗ᵈ 𝒟₂) .structure .DisplacementAlgebra-on._<_ = Product._⊗×<_ 𝒟₁ 𝒟₂
(𝒟₁ ⊗ᵈ 𝒟₂) .structure .DisplacementAlgebra-on.ε =  Product.ε× 𝒟₁ 𝒟₂
(𝒟₁ ⊗ᵈ 𝒟₂) .structure .DisplacementAlgebra-on._⊗_ = Product._⊗×_ 𝒟₁ 𝒟₂
(𝒟₁ ⊗ᵈ 𝒟₂) .structure .DisplacementAlgebra-on.has-displacement-algebra = Product.⊗×-is-displacement-algebra 𝒟₁ 𝒟₂
⌞ 𝒟₁ ⊗ᵈ 𝒟₂ ⌟-set = ×-is-hlevel 2  ⌞ 𝒟₁ ⌟-set ⌞ 𝒟₂ ⌟-set

module ProductProperties {o r} {𝒟₁ 𝒟₂ : DisplacementAlgebra o r}
                          where
  private
    module 𝒟₁ = DisplacementAlgebra 𝒟₁
    module 𝒟₂ = DisplacementAlgebra 𝒟₂
    open Product 𝒟₁ 𝒟₂

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  ⊗×-has-ordered-monoid : has-ordered-monoid 𝒟₁ → has-ordered-monoid 𝒟₂ → has-ordered-monoid (𝒟₁ ⊗ᵈ 𝒟₂)
  ⊗×-has-ordered-monoid 𝒟₁-ordered-monoid 𝒟₂-ordered-monoid =
    right-invariant→has-ordered-monoid (𝒟₁ ⊗ᵈ 𝒟₂) λ x≤y → from-⊗×≤ (⊗×-right-invariant _ _ _ (to-⊗×≤ x≤y))
    where
      module 𝒟₁-ordered-monoid = is-ordered-monoid (𝒟₁-ordered-monoid)
      module 𝒟₂-ordered-monoid = is-ordered-monoid (𝒟₂-ordered-monoid)

      ⊗×-right-invariant : ∀ x y z → x ⊗×≤ y → (x ⊗× z) ⊗×≤ (y ⊗× z)
      ⊗×-right-invariant x y z (both≤ x1≤y1 x2≤y2) = both≤ (𝒟₁-ordered-monoid.right-invariant x1≤y1) (𝒟₂-ordered-monoid.right-invariant x2≤y2)
        
  --------------------------------------------------------------------------------
  -- Joins

  ⊗×-has-joins : has-joins 𝒟₁ → has-joins 𝒟₂ → has-joins (𝒟₁ ⊗ᵈ 𝒟₂)
  ⊗×-has-joins 𝒟₁-joins 𝒟₂-joins = joins
    where
      module 𝒟₁-joins = has-joins 𝒟₁-joins
      module 𝒟₂-joins = has-joins 𝒟₂-joins

      joins : has-joins (𝒟₁ ⊗ᵈ 𝒟₂)
      joins .has-joins.join (x1 , x2) (y1 , y2) = (𝒟₁-joins.join x1 y1) , (𝒟₂-joins.join x2 y2)
      joins .has-joins.joinl = from-⊗×≤ (both≤ 𝒟₁-joins.joinl 𝒟₂-joins.joinl)
      joins .has-joins.joinr = from-⊗×≤ (both≤ 𝒟₁-joins.joinr 𝒟₂-joins.joinr)
      joins .has-joins.universal {x1 , x2} {y1 , y2} {z1 , z2} x≤z y≤z =
        from-⊗×≤ $ both≤ (𝒟₁-joins.universal (fst≤ (to-⊗×≤ x≤z)) (fst≤ (to-⊗×≤ y≤z)))
                         (𝒟₂-joins.universal (snd≤ (to-⊗×≤ x≤z)) (snd≤ (to-⊗×≤ y≤z)))

  --------------------------------------------------------------------------------
  -- Bottoms

  ⊗×-has-bottom : has-bottom 𝒟₁ → has-bottom 𝒟₂ → has-bottom (𝒟₁ ⊗ᵈ 𝒟₂)
  ⊗×-has-bottom 𝒟₁-bottom 𝒟₂-bottom = bottom
    where
      module 𝒟₁-bottom = has-bottom (𝒟₁-bottom)
      module 𝒟₂-bottom = has-bottom (𝒟₂-bottom)

      bottom : has-bottom (𝒟₁ ⊗ᵈ 𝒟₂)
      bottom .has-bottom.bot = 𝒟₁-bottom.bot , 𝒟₂-bottom.bot
      bottom .has-bottom.is-bottom (x1 , x2) = from-⊗×≤ (both≤ (𝒟₁-bottom.is-bottom x1) (𝒟₂-bottom.is-bottom x2))
