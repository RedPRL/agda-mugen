module Mugen.Algebra.Displacement.Lexicographic where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Product
open import Mugen.Algebra.OrderedMonoid

open import Mugen.Order.StrictOrder

--------------------------------------------------------------------------------
-- Lexicographic Products
-- Section 3.3.4
--
-- The lexicographic product of 2 displacement algebras consists of their product
-- as monoids, as well as their lexicographic product as orders.
--
-- As noted earlier, algebraic structure is given by the product of monoids, so we don't need
-- to prove that here.

module Lex {o r} (πβ πβ : DisplacementAlgebra o r) where
  private
    module πβ = DisplacementAlgebra-on (structure πβ)
    module πβ = DisplacementAlgebra-on (structure πβ)
    open Product πβ πβ

  --------------------------------------------------------------------------------
  -- Ordering

  data lex< (x : β πβ β Γ β πβ β) (y : β πβ β Γ β πβ β) : Type (o β r) where
    fst< : πβ [ fst x < fst y ]α΅ β lex< x y
    fstβ‘ : fst x β‘ fst y β πβ [ snd x < snd y ]α΅ β lex< x y

  data lexβ€ (x : β πβ β Γ β πβ β) (y : β πβ β Γ β πβ β) : Type (o β r) where
    fst< : πβ [ fst x < fst y ]α΅ β lexβ€ x y
    fstβ‘ : fst x β‘ fst y β πβ [ snd x β€ snd y ]α΅ β lexβ€ x y

  from-lexβ€ : β {x y} β lexβ€ x y β non-strict lex< x y
  from-lexβ€ (fst< x1<y1) = inr (fst< x1<y1)
  from-lexβ€ (fstβ‘ x1β‘y1 (inl x2β‘y2)) = inl (Ξ£-pathp x1β‘y1 x2β‘y2)
  from-lexβ€ (fstβ‘ x1β‘y1 (inr x2<y2)) = inr (fstβ‘ x1β‘y1 x2<y2)

  to-lexβ€ : β {x y} β non-strict lex< x y β lexβ€ x y
  to-lexβ€ (inl xβ‘y) = fstβ‘ (ap fst xβ‘y) (inl (ap snd xβ‘y))
  to-lexβ€ (inr (fst< x1<y1)) = fst< x1<y1
  to-lexβ€ (inr (fstβ‘ x1β‘y1 x2<y2)) = fstβ‘ x1β‘y1 (inr x2<y2)

  lexβ€-fst : β {x y} β lexβ€ x y β πβ [ fst x β€ fst y ]α΅
  lexβ€-fst (fst< x1<y1)   = inr x1<y1
  lexβ€-fst (fstβ‘ x1β‘y1 _) = inl x1β‘y1

  lexβ€-both : β {x1 x2 y1 y2} β πβ [ x1 β€ y1 ]α΅ β πβ [ x2 β€ y2 ]α΅ β lexβ€ (x1 , x2) (y1 , y2)
  lexβ€-both (inl x1β‘y1) x2β€y2 = fstβ‘ x1β‘y1 x2β€y2
  lexβ€-both (inr x1<y1) x2β€y2 = fst< x1<y1

  lex<-irrefl : β x β lex< x x β β₯
  lex<-irrefl x (fst< x1<x1) = πβ.irrefl x1<x1
  lex<-irrefl x (fstβ‘ xβ x2<x2) = πβ.irrefl x2<x2

  lex<-trans : β x y z β lex< x y β lex< y z β lex< x z
  lex<-trans x y z (fst< x1<y1) (fst< y1<z1) = fst< (πβ.trans x1<y1 y1<z1)
  lex<-trans x y z (fst< x1<y1) (fstβ‘ y1β‘z1 _) = fst< (πβ.β‘-transr x1<y1 y1β‘z1)
  lex<-trans x y z (fstβ‘ x1β‘y1 x2<y2) (fst< y1<z1) = fst< (πβ.β‘-transl x1β‘y1 y1<z1)
  lex<-trans x y z (fstβ‘ x1β‘y1 x2<y2) (fstβ‘ y1β‘z1 y2<z2) = fstβ‘ (x1β‘y1 β y1β‘z1) (πβ.trans x2<y2 y2<z2)

  lex<-is-prop : β x y β is-prop (lex< x y)
  lex<-is-prop x y (fst< x1<y1)       (fst< x1<y1β²)        = ap lex<.fst< (πβ.<-is-prop x1<y1 x1<y1β²)
  lex<-is-prop x y (fst< x1<y1)       (fstβ‘ x1β‘y1 _)       = absurd (πβ.irrefl (πβ.β‘-transr x1<y1 (sym x1β‘y1)))
  lex<-is-prop x y (fstβ‘ x1β‘y1 _)     (fst< x1<y1)         = absurd (πβ.irrefl (πβ.β‘-transr x1<y1 (sym x1β‘y1)))
  lex<-is-prop x y (fstβ‘ x1β‘y1 x2<y2) (fstβ‘ x1β‘y1β² x2<y2β²) = apβ lex<.fstβ‘ (β πβ β-set _ _ x1β‘y1 x1β‘y1β²) (πβ.<-is-prop x2<y2 x2<y2β²)

  lex-is-strict-order : is-strict-order lex<
  lex-is-strict-order .is-strict-order.irrefl {x} = lex<-irrefl x
  lex-is-strict-order .is-strict-order.trans {x} {y} {z} = lex<-trans x y z
  lex-is-strict-order .is-strict-order.has-prop {x} {y} = lex<-is-prop x y

  --------------------------------------------------------------------------------
  -- Left Invariance

  lex-left-invariant : β x y z β lex< y z β lex< (x βΓ y) (x βΓ z)
  lex-left-invariant (x1 , x2) (y1 , y2) (z1 , z2) (fst< y1<z1) = fst< (πβ.left-invariant y1<z1)
  lex-left-invariant (x1 , x2) (y1 , y2) (z1 , z2) (fstβ‘ y1β‘z1 y2<z2) = fstβ‘ (ap (x1 πβ.β_) y1β‘z1) (πβ.left-invariant y2<z2)

  lex-is-displacement-algebra : is-displacement-algebra lex< Ξ΅Γ _βΓ_
  lex-is-displacement-algebra .is-displacement-algebra.has-monoid = βΓ-is-monoid
  lex-is-displacement-algebra .is-displacement-algebra.has-strict-order = lex-is-strict-order
  lex-is-displacement-algebra .is-displacement-algebra.left-invariant {x} {y} {z} = lex-left-invariant x y z

Lex : β {o r} β DisplacementAlgebra o r β DisplacementAlgebra o r β DisplacementAlgebra o (o β r)
Lex {o = o} {r = r} πβ πβ = displacement
  where
    open Product πβ πβ
    open Lex πβ πβ

    displacement : DisplacementAlgebra o (o β r)
    β displacement β =  β πβ β Γ β πβ β
    displacement .structure .DisplacementAlgebra-on._<_ = lex<
    displacement .structure .DisplacementAlgebra-on.Ξ΅ = Ξ΅Γ
    displacement .structure .DisplacementAlgebra-on._β_ = _βΓ_
    displacement .structure .DisplacementAlgebra-on.has-displacement-algebra = lex-is-displacement-algebra
    β displacement β-set = Γ-is-hlevel 2 β πβ β-set β πβ β-set

module LexProperties {o r} {πβ πβ : DisplacementAlgebra o r} where
  private
    module πβ = DisplacementAlgebra-on (structure πβ)
    module πβ = DisplacementAlgebra-on (structure πβ)
    open Product πβ πβ
    open Lex πβ πβ

  lexβ€? : (β x1 y1 β Dec (πβ [ x1 β€ y1 ]α΅)) β (β x2 y2 β Dec (πβ [ x2 β€ y2 ]α΅)) β β x y β Dec (lexβ€ x y)
  lexβ€? β€β? β€β? (x1 , y1) (x2 , y2) with β€β? x1 x2
  lexβ€? β€β? β€β? (x1 , y1) (x2 , y2) | yes (inl x1β‘x2) with β€β? y1 y2
  lexβ€? β€β? β€β? (x1 , y1) (x2 , y2) | yes (inl x1β‘x2) | yes y1β€y2 = yes (fstβ‘ x1β‘x2 y1β€y2)
  lexβ€? β€β? β€β? (x1 , y1) (x2 , y2) | yes (inl x1β‘x2) | no Β¬y1β€y2 = no Ξ» where
    (fst< x1<x2) β absurd (πβ.irrefl (πβ.β‘-transl (sym x1β‘x2) x1<x2))
    (fstβ‘ x1β‘x2 y1β€y2) β Β¬y1β€y2 y1β€y2
  lexβ€? β€β? β€β? (x1 , y1) (x2 , y2) | yes (inr x1<x2) = yes (fst< x1<x2)
  lexβ€? β€β? β€β? (x1 , y1) (x2 , y2) | no Β¬x1β€x2 = no Ξ» where
    (fst< x1<x2) β Β¬x1β€x2 (inr x1<x2)
    (fstβ‘ x1β‘x2 _) β Β¬x1β€x2 (inl (x1β‘x2))

  --------------------------------------------------------------------------------
  -- Ordered Monoids

  -- When πβ is /strictly/ right invariant and πβ is an ordered monoid, then 'Lex πβ πβ' is also an ordered monoid.
  lex-has-ordered-monoid : (β {x y z} β πβ [ x < y ]α΅ β πβ [ (x πβ.β z) < (y πβ.β z) ]α΅) β has-ordered-monoid πβ β has-ordered-monoid (Lex πβ πβ)
  lex-has-ordered-monoid πβ-strictly-right-invariant πβ-ordered-monoid =
    right-invariantβhas-ordered-monoid (Lex πβ πβ) Ξ» xβ€y β from-lexβ€ (lex-right-invariant _ _ _ (to-lexβ€ xβ€y))
    where
      module πβ-ordered-monoid = is-ordered-monoid (πβ-ordered-monoid)

      lex-right-invariant : β x y z β lexβ€ x y β lexβ€ (x βΓ z) (y βΓ z)
      lex-right-invariant (x1 , x2) (y1 , y2) (z1 , z2) (fst< x1<y1) = fst< (πβ-strictly-right-invariant x1<y1)
      lex-right-invariant (x1 , x2) (y1 , y2) (z1 , z2) (fstβ‘ x1β‘y1 x2β€y2) = fstβ‘ (ap (πβ._β z1) x1β‘y1) (πβ-ordered-monoid.right-invariant x2β€y2)

  --------------------------------------------------------------------------------
  -- Joins

  lex-has-joins : (β x1 y1 β Dec (πβ [ x1 β€ y1 ]α΅)) β (β x2 y2 β Dec (πβ [ x2 β€ y2 ]α΅))
                β has-joins πβ β has-joins πβ β has-bottom πβ β has-joins (Lex πβ πβ)
  lex-has-joins _β€β?_ _β€β?_ πβ-joins πβ-joins πβ-bottom = joins
    where
      module πβ-joins = has-joins πβ-joins
      module πβ-joins = has-joins πβ-joins
      module πβ-bottom = has-bottom (πβ-bottom)

      joins : has-joins (Lex πβ πβ)
      joins .has-joins.join (x1 , x2) (y1 , y2) with x1 β€β? (πβ-joins.join x1 y1) | y1 β€β? (πβ-joins.join x1 y1)
      ... | yes (inr x1<x1β¨y1) | yes (inr y1<x1β¨y1) = πβ-joins.join x1 y1 , πβ-bottom.bot
      ... | yes (inr x1<x1β¨y1) | yes (inl y1β‘x1β¨y1) = πβ-joins.join x1 y1 , y2
      ... | yes (inl x1β‘x1β¨y1) | yes (inr y1<x1β¨y1) = πβ-joins.join x1 y1 , x2
      ... | yes (inl x1β‘x1β¨y1) | yes (inl y1β‘x1β¨y1) = πβ-joins.join x1 y1 , πβ-joins.join x2 y2
      ... | yes (inl _)        | no Β¬y1β€x1β¨y1       = absurd (Β¬y1β€x1β¨y1 πβ-joins.joinr)
      ... | yes (inr _)        | no Β¬y1β€x1β¨y1       = absurd (Β¬y1β€x1β¨y1 πβ-joins.joinr)
      ... | no Β¬x1β€x1β¨y1       | _                  = absurd (Β¬x1β€x1β¨y1 πβ-joins.joinl)
      joins .has-joins.joinl {x1 , x2} {y1 , y2} with x1 β€β? (πβ-joins.join x1 y1) | y1 β€β? (πβ-joins.join x1 y1)
      ... | yes (inr x1<x1β¨y1) | yes (inr y1<x1β¨y1) = from-lexβ€ (fst< x1<x1β¨y1)
      ... | yes (inr x1<x1β¨y1) | yes (inl y1β‘x1β¨y1) = from-lexβ€ (fst< x1<x1β¨y1)
      ... | yes (inl x1β‘x1β¨y1) | yes (inr y1<x1β¨y1) = from-lexβ€ (fstβ‘ x1β‘x1β¨y1 (inl refl))
      ... | yes (inl x1β‘x1β¨y1) | yes (inl y1β‘x1β¨y1) = from-lexβ€ (fstβ‘ x1β‘x1β¨y1 πβ-joins.joinl)
      ... | yes (inl _)        | no Β¬y1β€x1β¨y1       = absurd (Β¬y1β€x1β¨y1 πβ-joins.joinr)
      ... | yes (inr _)        | no Β¬y1β€x1β¨y1       = absurd (Β¬y1β€x1β¨y1 πβ-joins.joinr)
      ... | no Β¬x1β€x1β¨y1       | _                  = absurd (Β¬x1β€x1β¨y1 πβ-joins.joinl)
      joins .has-joins.joinr {x1 , x2} {y1 , y2} with x1 β€β? (πβ-joins.join x1 y1) | y1 β€β? (πβ-joins.join x1 y1)
      ... | yes (inr x1<x1β¨y1) | yes (inr y1<x1β¨y1) = from-lexβ€ (fst< y1<x1β¨y1)
      ... | yes (inr x1<x1β¨y1) | yes (inl y1β‘x1β¨y1) = from-lexβ€ (fstβ‘ y1β‘x1β¨y1 (inl refl))
      ... | yes (inl x1β‘x1β¨y1) | yes (inr y1<x1β¨y1) = from-lexβ€ (fst< y1<x1β¨y1)
      ... | yes (inl x1β‘x1β¨y1) | yes (inl y1β‘x1β¨y1) = from-lexβ€ (fstβ‘ y1β‘x1β¨y1 πβ-joins.joinr)
      ... | yes (inl _)        | no Β¬y1β€x1β¨y1       = absurd (Β¬y1β€x1β¨y1 πβ-joins.joinr)
      ... | yes (inr _)        | no Β¬y1β€x1β¨y1       = absurd (Β¬y1β€x1β¨y1 πβ-joins.joinr)
      ... | no Β¬x1β€x1β¨y1       | _                  = absurd (Β¬x1β€x1β¨y1 πβ-joins.joinl)
      joins .has-joins.universal {x1 , x2} {y1 , y2} {z1 , z2} xβ€z yβ€z with x1 β€β? (πβ-joins.join x1 y1) | y1 β€β? (πβ-joins.join x1 y1) | to-lexβ€ xβ€z | to-lexβ€ yβ€z
      ... | yes (inr x1<x1β¨y1) | yes (inr y1<x1β¨y1) | xβ€z              | yβ€z = from-lexβ€ (lexβ€-both (πβ-joins.universal (lexβ€-fst xβ€z) (lexβ€-fst yβ€z)) (πβ-bottom.is-bottom z2))
      ... | yes (inr x1<x1β¨y1) | yes (inl y1β‘x1β¨y1) | xβ€z              | fst< y1<z1 = from-lexβ€ (fst< (πβ.β‘-transl (sym y1β‘x1β¨y1) y1<z1))
      ... | yes (inr x1<x1β¨y1) | yes (inl y1β‘x1β¨y1) | xβ€z              | fstβ‘ y1β‘z1 y2β€z2 = from-lexβ€ (fstβ‘ (sym y1β‘x1β¨y1 β y1β‘z1) y2β€z2)
      ... | yes (inl x1β‘x1β¨y1) | yes (inr y1<x1β¨y1) | fst< x1<z1       | yβ€z = from-lexβ€ (fst< (πβ.β‘-transl (sym x1β‘x1β¨y1) x1<z1))
      ... | yes (inl x1β‘x1β¨y1) | yes (inr y1<x1β¨y1) | fstβ‘ x1β‘z1 x2β€z2 | yβ€z = from-lexβ€ (fstβ‘ (sym x1β‘x1β¨y1 β x1β‘z1) x2β€z2)
      ... | yes (inl x1β‘x1β¨y1) | yes (inl y1β‘x1β¨y1) | fst< x1<z1       | yβ€z = from-lexβ€ (fst< (πβ.β‘-transl (sym x1β‘x1β¨y1) x1<z1))
      ... | yes (inl x1β‘x1β¨y1) | yes (inl y1β‘x1β¨y1) | fstβ‘ x1β‘z1 x2β€z2 | fst< y1<z1 = from-lexβ€ (fst< (πβ.β‘-transl (sym y1β‘x1β¨y1) y1<z1))
      ... | yes (inl x1β‘x1β¨y1) | yes (inl y1β‘x1β¨y1) | fstβ‘ x1β‘z1 x2β€z2 | fstβ‘ y1β‘z1 y2β€z2 = from-lexβ€ (fstβ‘ (sym x1β‘x1β¨y1 β x1β‘z1) (πβ-joins.universal x2β€z2 y2β€z2))
      ... | yes (inl _)        | no Β¬y1β€x1β¨y1       | xβ€z              | yβ€z = absurd (Β¬y1β€x1β¨y1 πβ-joins.joinr)
      ... | yes (inr _)        | no Β¬y1β€x1β¨y1       | xβ€z              | yβ€z = absurd (Β¬y1β€x1β¨y1 πβ-joins.joinr)
      ... | no Β¬x1β€x1β¨y1       | _                  | xβ€z              | yβ€z = absurd (Β¬x1β€x1β¨y1 πβ-joins.joinl)

  --------------------------------------------------------------------------------
  -- Bottoms

  lex-has-bottom : has-bottom πβ β has-bottom πβ β has-bottom (Lex πβ πβ)
  lex-has-bottom πβ-bottom πβ-bottom = bottom
    where
      module πβ-bottom = has-bottom (πβ-bottom)
      module πβ-bottom = has-bottom (πβ-bottom)

      bottom : has-bottom (Lex πβ πβ)
      bottom .has-bottom.bot = πβ-bottom.bot , πβ-bottom.bot
      bottom .has-bottom.is-bottom (x1 , x2) with πβ-bottom.is-bottom x1
      ... | inl bot1β‘x1 = from-lexβ€ (fstβ‘ bot1β‘x1 (πβ-bottom.is-bottom x2))
      ... | inr bot1<x1 = from-lexβ€ (fst< bot1<x1)
