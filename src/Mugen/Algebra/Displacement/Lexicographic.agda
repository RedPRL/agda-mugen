module Mugen.Algebra.Displacement.Lexicographic where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Product
open import Mugen.Algebra.OrderedMonoid

open import Mugen.Order.StrictOrder

module Lex {o r} (𝒟₁ 𝒟₂ : DisplacementAlgebra o r) where
  private
    module 𝒟₁ = DisplacementAlgebra-on (structure 𝒟₁)
    module 𝒟₂ = DisplacementAlgebra-on (structure 𝒟₂)
    open Product 𝒟₁ 𝒟₂

  data lex< (x : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) (y : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) : Type (o ⊔ r) where
    fst< : 𝒟₁ [ fst x < fst y ]ᵈ → lex< x y
    fst≡ : fst x ≡ fst y → 𝒟₂ [ snd x < snd y ]ᵈ → lex< x y

  data lex≤ (x : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) (y : ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟) : Type (o ⊔ r) where
    fst< : 𝒟₁ [ fst x < fst y ]ᵈ → lex≤ x y
    fst≡ : fst x ≡ fst y → 𝒟₂ [ snd x ≤ snd y ]ᵈ → lex≤ x y

  from-lex≤ : ∀ {x y} → lex≤ x y → non-strict lex< x y
  from-lex≤ (fst< x1<y1) = inr (fst< x1<y1)
  from-lex≤ (fst≡ x1≡y1 (inl x2≡y2)) = inl (Σ-pathp x1≡y1 x2≡y2)
  from-lex≤ (fst≡ x1≡y1 (inr x2<y2)) = inr (fst≡ x1≡y1 x2<y2)

  to-lex≤ : ∀ {x y} → non-strict lex< x y → lex≤ x y
  to-lex≤ (inl x≡y) = fst≡ (ap fst x≡y) (inl (ap snd x≡y))
  to-lex≤ (inr (fst< x1<y1)) = fst< x1<y1
  to-lex≤ (inr (fst≡ x1≡y1 x2<y2)) = fst≡ x1≡y1 (inr x2<y2)

  lex≤-fst : ∀ {x y} → lex≤ x y → 𝒟₁ [ fst x ≤ fst y ]ᵈ
  lex≤-fst (fst< x1<y1)   = inr x1<y1
  lex≤-fst (fst≡ x1≡y1 _) = inl x1≡y1

  lex≤-both : ∀ {x1 x2 y1 y2} → 𝒟₁ [ x1 ≤ y1 ]ᵈ → 𝒟₂ [ x2 ≤ y2 ]ᵈ → lex≤ (x1 , x2) (y1 , y2)
  lex≤-both (inl x1≡y1) x2≤y2 = fst≡ x1≡y1 x2≤y2
  lex≤-both (inr x1<y1) x2≤y2 = fst< x1<y1

  lex<-irrefl : ∀ x → lex< x x → ⊥
  lex<-irrefl x (fst< x1<x1) = 𝒟₁.irrefl x1<x1
  lex<-irrefl x (fst≡ x₁ x2<x2) = 𝒟₂.irrefl x2<x2

  lex<-trans : ∀ x y z → lex< x y → lex< y z → lex< x z
  lex<-trans x y z (fst< x1<y1) (fst< y1<z1) = fst< (𝒟₁.trans x1<y1 y1<z1)
  lex<-trans x y z (fst< x1<y1) (fst≡ y1≡z1 _) = fst< (𝒟₁.≡-transr x1<y1 y1≡z1)
  lex<-trans x y z (fst≡ x1≡y1 x2<y2) (fst< y1<z1) = fst< (𝒟₁.≡-transl x1≡y1 y1<z1)
  lex<-trans x y z (fst≡ x1≡y1 x2<y2) (fst≡ y1≡z1 y2<z2) = fst≡ (x1≡y1 ∙ y1≡z1) (𝒟₂.trans x2<y2 y2<z2)

  lex<-is-prop : ∀ x y → is-prop (lex< x y)
  lex<-is-prop x y (fst< x1<y1)       (fst< x1<y1′)        = ap lex<.fst< (𝒟₁.<-is-prop x1<y1 x1<y1′)
  lex<-is-prop x y (fst< x1<y1)       (fst≡ x1≡y1 _)       = absurd (𝒟₁.irrefl (𝒟₁.≡-transr x1<y1 (sym x1≡y1)))
  lex<-is-prop x y (fst≡ x1≡y1 _)     (fst< x1<y1)         = absurd (𝒟₁.irrefl (𝒟₁.≡-transr x1<y1 (sym x1≡y1)))
  lex<-is-prop x y (fst≡ x1≡y1 x2<y2) (fst≡ x1≡y1′ x2<y2′) = ap₂ lex<.fst≡ (⌞ 𝒟₁ ⌟-set _ _ x1≡y1 x1≡y1′) (𝒟₂.<-is-prop x2<y2 x2<y2′)

  lex-is-strict-order : is-strict-order lex<
  lex-is-strict-order .is-strict-order.irrefl {x} = lex<-irrefl x
  lex-is-strict-order .is-strict-order.trans {x} {y} {z} = lex<-trans x y z
  lex-is-strict-order .is-strict-order.has-prop {x} {y} = lex<-is-prop x y

  lex-left-invariant : ∀ x y z → lex< y z → lex< (x ⊗× y) (x ⊗× z)
  lex-left-invariant (x1 , x2) (y1 , y2) (z1 , z2) (fst< y1<z1) = fst< (𝒟₁.left-invariant y1<z1)
  lex-left-invariant (x1 , x2) (y1 , y2) (z1 , z2) (fst≡ y1≡z1 y2<z2) = fst≡ (ap (x1 𝒟₁.⊗_) y1≡z1) (𝒟₂.left-invariant y2<z2)

  lex-is-displacement-algebra : is-displacement-algebra lex< ε× _⊗×_
  lex-is-displacement-algebra .is-displacement-algebra.has-monoid = ⊗×-is-monoid
  lex-is-displacement-algebra .is-displacement-algebra.has-strict-order = lex-is-strict-order
  lex-is-displacement-algebra .is-displacement-algebra.left-invariant {x} {y} {z} = lex-left-invariant x y z

Lex : ∀ {o r} → DisplacementAlgebra o r → DisplacementAlgebra o r → DisplacementAlgebra o (o ⊔ r)
Lex {o = o} {r = r} 𝒟₁ 𝒟₂ = displacement
  where
    open Product 𝒟₁ 𝒟₂
    open Lex 𝒟₁ 𝒟₂

    displacement : DisplacementAlgebra o (o ⊔ r)
    ⌞ displacement ⌟ =  ⌞ 𝒟₁ ⌟ × ⌞ 𝒟₂ ⌟
    displacement .structure .DisplacementAlgebra-on._<_ = lex<
    displacement .structure .DisplacementAlgebra-on.ε = ε×
    displacement .structure .DisplacementAlgebra-on._⊗_ = _⊗×_
    displacement .structure .DisplacementAlgebra-on.has-displacement-algebra = lex-is-displacement-algebra
    ⌞ displacement ⌟-set = ×-is-hlevel 2 ⌞ 𝒟₁ ⌟-set ⌞ 𝒟₂ ⌟-set

module LexProperties {o r} {𝒟₁ 𝒟₂ : DisplacementAlgebra o r} where
  private
    module 𝒟₁ = DisplacementAlgebra-on (structure 𝒟₁)
    module 𝒟₂ = DisplacementAlgebra-on (structure 𝒟₂)
    open Product 𝒟₁ 𝒟₂
    open Lex 𝒟₁ 𝒟₂

  lex≤? : (∀ x1 y1 → Dec (𝒟₁ [ x1 ≤ y1 ]ᵈ)) → (∀ x2 y2 → Dec (𝒟₂ [ x2 ≤ y2 ]ᵈ)) → ∀ x y → Dec (lex≤ x y)
  lex≤? ≤₁? ≤₂? (x1 , y1) (x2 , y2) with ≤₁? x1 x2
  lex≤? ≤₁? ≤₂? (x1 , y1) (x2 , y2) | yes (inl x1≡x2) with ≤₂? y1 y2
  lex≤? ≤₁? ≤₂? (x1 , y1) (x2 , y2) | yes (inl x1≡x2) | yes y1≤y2 = yes (fst≡ x1≡x2 y1≤y2)
  lex≤? ≤₁? ≤₂? (x1 , y1) (x2 , y2) | yes (inl x1≡x2) | no ¬y1≤y2 = no λ where
    (fst< x1<x2) → absurd (𝒟₁.irrefl (𝒟₁.≡-transl (sym x1≡x2) x1<x2))
    (fst≡ x1≡x2 y1≤y2) → ¬y1≤y2 y1≤y2
  lex≤? ≤₁? ≤₂? (x1 , y1) (x2 , y2) | yes (inr x1<x2) = yes (fst< x1<x2)
  lex≤? ≤₁? ≤₂? (x1 , y1) (x2 , y2) | no ¬x1≤x2 = no λ where
    (fst< x1<x2) → ¬x1≤x2 (inr x1<x2)
    (fst≡ x1≡x2 _) → ¬x1≤x2 (inl (x1≡x2))

  -- When 𝒟₁ is /strictly/ right invariant and 𝒟₂ is an ordered monoid, then 'Lex 𝒟₁ 𝒟₂' is also an ordered monoid.
  lex-has-ordered-monoid : (∀ {x y z} → 𝒟₁ [ x < y ]ᵈ → 𝒟₁ [ (x 𝒟₁.⊗ z) < (y 𝒟₁.⊗ z) ]ᵈ) → has-ordered-monoid 𝒟₂ → has-ordered-monoid (Lex 𝒟₁ 𝒟₂)
  lex-has-ordered-monoid 𝒟₁-strictly-right-invariant 𝒟₂-ordered-monoid =
    right-invariant→has-ordered-monoid (Lex 𝒟₁ 𝒟₂) λ x≤y → from-lex≤ (lex-right-invariant _ _ _ (to-lex≤ x≤y))
    where
      module 𝒟₂-ordered-monoid = is-ordered-monoid (𝒟₂-ordered-monoid)

      lex-right-invariant : ∀ x y z → lex≤ x y → lex≤ (x ⊗× z) (y ⊗× z)
      lex-right-invariant (x1 , x2) (y1 , y2) (z1 , z2) (fst< x1<y1) = fst< (𝒟₁-strictly-right-invariant x1<y1)
      lex-right-invariant (x1 , x2) (y1 , y2) (z1 , z2) (fst≡ x1≡y1 x2≤y2) = fst≡ (ap (𝒟₁._⊗ z1) x1≡y1) (𝒟₂-ordered-monoid.right-invariant x2≤y2)

  lex-has-bottom : has-bottom 𝒟₁ → has-bottom 𝒟₂ → has-bottom (Lex 𝒟₁ 𝒟₂)
  lex-has-bottom 𝒟₁-bottom 𝒟₂-bottom = bottom
    where
      module 𝒟₁-bottom = has-bottom (𝒟₁-bottom)
      module 𝒟₂-bottom = has-bottom (𝒟₂-bottom)

      bottom : has-bottom (Lex 𝒟₁ 𝒟₂)
      bottom .has-bottom.bot = 𝒟₁-bottom.bot , 𝒟₂-bottom.bot
      bottom .has-bottom.is-bottom (x1 , x2) with 𝒟₁-bottom.is-bottom x1
      ... | inl bot1≡x1 = from-lex≤ (fst≡ bot1≡x1 (𝒟₂-bottom.is-bottom x2))
      ... | inr bot1<x1 = from-lex≤ (fst< bot1<x1)

  lex-has-joins : (∀ x1 y1 → Dec (𝒟₁ [ x1 ≤ y1 ]ᵈ)) → (∀ x2 y2 → Dec (𝒟₂ [ x2 ≤ y2 ]ᵈ))
                → has-joins 𝒟₁ → has-joins 𝒟₂ → has-bottom 𝒟₂ → has-joins (Lex 𝒟₁ 𝒟₂)
  lex-has-joins _≤₁?_ _≤₂?_ 𝒟₁-joins 𝒟₂-joins 𝒟₂-bottom = joins
    where
      module 𝒟₁-joins = has-joins 𝒟₁-joins
      module 𝒟₂-joins = has-joins 𝒟₂-joins
      module 𝒟₂-bottom = has-bottom (𝒟₂-bottom)

      joins : has-joins (Lex 𝒟₁ 𝒟₂)
      joins .has-joins.join (x1 , x2) (y1 , y2) with x1 ≤₁? (𝒟₁-joins.join x1 y1) | y1 ≤₁? (𝒟₁-joins.join x1 y1)
      ... | yes (inr x1<x1∨y1) | yes (inr y1<x1∨y1) = 𝒟₁-joins.join x1 y1 , 𝒟₂-bottom.bot
      ... | yes (inr x1<x1∨y1) | yes (inl y1≡x1∨y1) = 𝒟₁-joins.join x1 y1 , y2
      ... | yes (inl x1≡x1∨y1) | yes (inr y1<x1∨y1) = 𝒟₁-joins.join x1 y1 , x2
      ... | yes (inl x1≡x1∨y1) | yes (inl y1≡x1∨y1) = 𝒟₁-joins.join x1 y1 , 𝒟₂-joins.join x2 y2
      ... | yes (inl _)        | no ¬y1≤x1∨y1       = absurd (¬y1≤x1∨y1 𝒟₁-joins.joinr)
      ... | yes (inr _)        | no ¬y1≤x1∨y1       = absurd (¬y1≤x1∨y1 𝒟₁-joins.joinr)
      ... | no ¬x1≤x1∨y1       | _                  = absurd (¬x1≤x1∨y1 𝒟₁-joins.joinl)
      joins .has-joins.joinl {x1 , x2} {y1 , y2} with x1 ≤₁? (𝒟₁-joins.join x1 y1) | y1 ≤₁? (𝒟₁-joins.join x1 y1)
      ... | yes (inr x1<x1∨y1) | yes (inr y1<x1∨y1) = from-lex≤ (fst< x1<x1∨y1)
      ... | yes (inr x1<x1∨y1) | yes (inl y1≡x1∨y1) = from-lex≤ (fst< x1<x1∨y1)
      ... | yes (inl x1≡x1∨y1) | yes (inr y1<x1∨y1) = from-lex≤ (fst≡ x1≡x1∨y1 (inl refl))
      ... | yes (inl x1≡x1∨y1) | yes (inl y1≡x1∨y1) = from-lex≤ (fst≡ x1≡x1∨y1 𝒟₂-joins.joinl)
      ... | yes (inl _)        | no ¬y1≤x1∨y1       = absurd (¬y1≤x1∨y1 𝒟₁-joins.joinr)
      ... | yes (inr _)        | no ¬y1≤x1∨y1       = absurd (¬y1≤x1∨y1 𝒟₁-joins.joinr)
      ... | no ¬x1≤x1∨y1       | _                  = absurd (¬x1≤x1∨y1 𝒟₁-joins.joinl)
      joins .has-joins.joinr {x1 , x2} {y1 , y2} with x1 ≤₁? (𝒟₁-joins.join x1 y1) | y1 ≤₁? (𝒟₁-joins.join x1 y1)
      ... | yes (inr x1<x1∨y1) | yes (inr y1<x1∨y1) = from-lex≤ (fst< y1<x1∨y1)
      ... | yes (inr x1<x1∨y1) | yes (inl y1≡x1∨y1) = from-lex≤ (fst≡ y1≡x1∨y1 (inl refl))
      ... | yes (inl x1≡x1∨y1) | yes (inr y1<x1∨y1) = from-lex≤ (fst< y1<x1∨y1)
      ... | yes (inl x1≡x1∨y1) | yes (inl y1≡x1∨y1) = from-lex≤ (fst≡ y1≡x1∨y1 𝒟₂-joins.joinr)
      ... | yes (inl _)        | no ¬y1≤x1∨y1       = absurd (¬y1≤x1∨y1 𝒟₁-joins.joinr)
      ... | yes (inr _)        | no ¬y1≤x1∨y1       = absurd (¬y1≤x1∨y1 𝒟₁-joins.joinr)
      ... | no ¬x1≤x1∨y1       | _                  = absurd (¬x1≤x1∨y1 𝒟₁-joins.joinl)
      joins .has-joins.universal {x1 , x2} {y1 , y2} {z1 , z2} x≤z y≤z with x1 ≤₁? (𝒟₁-joins.join x1 y1) | y1 ≤₁? (𝒟₁-joins.join x1 y1) | to-lex≤ x≤z | to-lex≤ y≤z
      ... | yes (inr x1<x1∨y1) | yes (inr y1<x1∨y1) | x≤z              | y≤z = from-lex≤ (lex≤-both (𝒟₁-joins.universal (lex≤-fst x≤z) (lex≤-fst y≤z)) (𝒟₂-bottom.is-bottom z2))
      ... | yes (inr x1<x1∨y1) | yes (inl y1≡x1∨y1) | x≤z              | fst< y1<z1 = from-lex≤ (fst< (𝒟₁.≡-transl (sym y1≡x1∨y1) y1<z1))
      ... | yes (inr x1<x1∨y1) | yes (inl y1≡x1∨y1) | x≤z              | fst≡ y1≡z1 y2≤z2 = from-lex≤ (fst≡ (sym y1≡x1∨y1 ∙ y1≡z1) y2≤z2)
      ... | yes (inl x1≡x1∨y1) | yes (inr y1<x1∨y1) | fst< x1<z1       | y≤z = from-lex≤ (fst< (𝒟₁.≡-transl (sym x1≡x1∨y1) x1<z1))
      ... | yes (inl x1≡x1∨y1) | yes (inr y1<x1∨y1) | fst≡ x1≡z1 x2≤z2 | y≤z = from-lex≤ (fst≡ (sym x1≡x1∨y1 ∙ x1≡z1) x2≤z2)
      ... | yes (inl x1≡x1∨y1) | yes (inl y1≡x1∨y1) | fst< x1<z1       | y≤z = from-lex≤ (fst< (𝒟₁.≡-transl (sym x1≡x1∨y1) x1<z1))
      ... | yes (inl x1≡x1∨y1) | yes (inl y1≡x1∨y1) | fst≡ x1≡z1 x2≤z2 | fst< y1<z1 = from-lex≤ (fst< (𝒟₁.≡-transl (sym y1≡x1∨y1) y1<z1))
      ... | yes (inl x1≡x1∨y1) | yes (inl y1≡x1∨y1) | fst≡ x1≡z1 x2≤z2 | fst≡ y1≡z1 y2≤z2 = from-lex≤ (fst≡ (sym x1≡x1∨y1 ∙ x1≡z1) (𝒟₂-joins.universal x2≤z2 y2≤z2))
      ... | yes (inl _)        | no ¬y1≤x1∨y1       | x≤z              | y≤z = absurd (¬y1≤x1∨y1 𝒟₁-joins.joinr)
      ... | yes (inr _)        | no ¬y1≤x1∨y1       | x≤z              | y≤z = absurd (¬y1≤x1∨y1 𝒟₁-joins.joinr)
      ... | no ¬x1≤x1∨y1       | _                  | x≤z              | y≤z = absurd (¬x1≤x1∨y1 𝒟₁-joins.joinl)
