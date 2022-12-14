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
-- Section 3.3.3
--
-- We can take the product of 2 displacement algebras. Algebraic structure
-- is given by the product of monoids, and ordering is given by the product of the
-- orders.

module Product {o r} (๐โ ๐โ : DisplacementAlgebra o r) where
  private
    module ๐โ = DisplacementAlgebra ๐โ
    module ๐โ = DisplacementAlgebra ๐โ

  --------------------------------------------------------------------------------
  -- Algebra

  _โร_ : โ ๐โ โ ร โ ๐โ โ โ โ ๐โ โ ร โ ๐โ โ โ โ ๐โ โ ร โ ๐โ โ
  (d1 , d2) โร (d1โฒ , d2โฒ) = (d1 ๐โ.โ d1โฒ) , (d2 ๐โ.โ d2โฒ)

  ฮตร : โ ๐โ โ ร โ ๐โ โ
  ฮตร = ๐โ.ฮต , ๐โ.ฮต

  โร-associative : โ (x y z : โ ๐โ โ ร โ ๐โ โ) โ (x โร (y โร z)) โก ((x โร y) โร z)
  โร-associative (d1 , d2) (d1โฒ , d2โฒ) (d1โณ , d2โณ) i = ๐โ.associative {d1} {d1โฒ} {d1โณ} i , ๐โ.associative {d2} {d2โฒ} {d2โณ} i

  โร-idl : โ (x : โ ๐โ โ ร โ ๐โ โ) โ (ฮตร โร x) โก x
  โร-idl (d1 , d2) i = ๐โ.idl {d1} i , ๐โ.idl {d2} i

  โร-idr : โ (x : โ ๐โ โ ร โ ๐โ โ) โ (x โร ฮตร) โก x
  โร-idr (d1 , d2) i = ๐โ.idr {d1} i , ๐โ.idr {d2} i

  โร-is-magma : is-magma _โร_
  โร-is-magma .has-is-set = ร-is-hlevel 2 โ ๐โ โ-set โ ๐โ โ-set

  โร-is-semigroup : is-semigroup _โร_
  โร-is-semigroup .has-is-magma = โร-is-magma
  โร-is-semigroup .associative {x} {y} {z} = โร-associative x y z

  โร-is-monoid : is-monoid ฮตร _โร_
  โร-is-monoid .has-is-semigroup = โร-is-semigroup
  โร-is-monoid .idl {x} = โร-idl x
  โร-is-monoid .idr {x} = โร-idr x

  --------------------------------------------------------------------------------
  -- Ordering

  -- NOTE: This version of the definition doesn't require a propositional truncation.
  data _โร<_ (x :  โ ๐โ โ ร โ ๐โ โ) (y : โ ๐โ โ ร โ ๐โ โ) : Type (o โ r) where
    fst< : ๐โ [ fst x < fst y ]แต โ snd x โก snd y โ x โร< y
    snd< : fst x โก fst y โ ๐โ [ snd x < snd y ]แต โ x โร< y
    both< :  ๐โ [ fst x < fst y ]แต โ ๐โ [ snd x < snd y ]แต โ x โร< y

  -- Instead of working with 'non-strict _โร<_', we define an equivalent
  -- definition that is simpler to handle.
  record _โรโค_ (x :  โ ๐โ โ ร โ ๐โ โ) (y : โ ๐โ โ ร โ ๐โ โ) : Type (o โ r) where
    constructor bothโค
    field
      fstโค : ๐โ [ fst x โค fst y ]แต
      sndโค : ๐โ [ snd x โค snd y ]แต

  open _โรโค_ public

  from-โรโค : โ {x y} โ x โรโค y โ non-strict _โร<_ x y
  from-โรโค (bothโค (inl x1โกy1) (inl x2โกy2)) = inl (ฮฃ-pathp x1โกy1 x2โกy2)
  from-โรโค (bothโค (inl x1โกy1) (inr x2<y2)) = inr (snd< x1โกy1 x2<y2)
  from-โรโค (bothโค (inr x1<y1) (inl x2โกy2)) = inr (fst< x1<y1 x2โกy2)
  from-โรโค (bothโค (inr x1<y1) (inr x2<y2)) = inr (both< x1<y1 x2<y2)

  to-โรโค : โ {x y} โ non-strict _โร<_ x y โ x โรโค y
  to-โรโค (inl xโกy) = bothโค (inl (ap fst xโกy)) (inl (ap snd xโกy))
  to-โรโค (inr (fst< x1<y1 x2โกy2)) = bothโค (inr x1<y1) (inl x2โกy2)
  to-โรโค (inr (snd< x1โกy1 x2<y2)) = bothโค (inl x1โกy1) (inr x2<y2)
  to-โรโค (inr (both< x1<y1 x2<y2)) = bothโค (inr x1<y1) (inr x2<y2)

  โร<-irrefl : โ x โ x โร< x โ โฅ
  โร<-irrefl _ (fst< x1<x1 _) = ๐โ.irrefl x1<x1
  โร<-irrefl _ (snd< _ x2<x2) = ๐โ.irrefl x2<x2
  โร<-irrefl _ (both< x1<x1 x2<x2) = ๐โ.irrefl x1<x1

  โร<-trans : โ x y z โ x โร< y โ y โร< z โ x โร< z
  โร<-trans _ _ _ (fst< x1<y1 x2โกy2)  (fst< y1<z1 y2โกz2)  = fst< (๐โ.trans x1<y1 y1<z1) (x2โกy2 โ y2โกz2)
  โร<-trans _ _ _ (fst< x1<y1 x2โกy2)  (snd< y1โกz1 y2<z2)  = both< (๐โ.โก-transr x1<y1 y1โกz1) (๐โ.โก-transl x2โกy2 y2<z2)
  โร<-trans _ _ _ (fst< x1<y1 x2โกy2)  (both< y1<z1 y2<z2) = both< (๐โ.trans x1<y1 y1<z1) (๐โ.โก-transl x2โกy2 y2<z2)
  โร<-trans _ _ _ (snd< x1โกy1 x2<y2)  (fst< y1<z1 y2โกz2)  = both< (๐โ.โก-transl x1โกy1 y1<z1) (๐โ.โก-transr x2<y2 y2โกz2)
  โร<-trans _ _ _ (snd< x1โกy1 x2<y2)  (snd< y1โกz1 y2<z2)  = snd< (x1โกy1 โ y1โกz1) (๐โ.trans x2<y2 y2<z2)
  โร<-trans _ _ _ (snd< x1โกy1 x2<y2)  (both< y1<z1 y2<z2) = both< (๐โ.โก-transl x1โกy1 y1<z1) (๐โ.trans x2<y2 y2<z2)
  โร<-trans _ _ _ (both< x1<y1 x2<y2) (fst< y1<z1 y2โกz2)  = both< (๐โ.trans x1<y1 y1<z1) (๐โ.โก-transr x2<y2 y2โกz2)
  โร<-trans _ _ _ (both< x1<y1 x2<y2) (snd< y1โกz1 y2<z2)  = both< (๐โ.โก-transr x1<y1 y1โกz1) (๐โ.trans x2<y2 y2<z2)
  โร<-trans _ _ _ (both< x1<y1 x2<y2) (both< y1<z1 y2<z2) = both< (๐โ.trans x1<y1 y1<z1) (๐โ.trans x2<y2 y2<z2)

  โร<-is-prop : โ x y โ is-prop (x โร< y)
  โร<-is-prop _ _ (fst< x1<y1 x2โกy2)  (fst< x1<y1โฒ x2โกy2โฒ)  = apโ fst< (๐โ.<-is-prop x1<y1 x1<y1โฒ) (โ ๐โ โ-set _ _ x2โกy2 x2โกy2โฒ)
  โร<-is-prop _ _ (fst< x1<y1 _)      (snd< x1โกy1 _)        = absurd (๐โ.irrefl (๐โ.โก-transr x1<y1 (sym x1โกy1)))
  โร<-is-prop _ _ (fst< _ x2โกy2)      (both< _ x2<y2)       = absurd (๐โ.irrefl (๐โ.โก-transr x2<y2 (sym x2โกy2)))
  โร<-is-prop _ _ (snd< x1โกy1 _)      (fst< x1<y1 _)        = absurd (๐โ.irrefl (๐โ.โก-transr x1<y1 (sym x1โกy1)))
  โร<-is-prop _ _ (snd< x1โกy1 x2<y2)  (snd< x1โกy1โฒ x2<y2โฒ)  = apโ snd< ( โ ๐โ โ-set _ _ x1โกy1 x1โกy1โฒ) (๐โ.<-is-prop x2<y2 x2<y2โฒ)
  โร<-is-prop _ _ (snd< x1โกy1 _)      (both< x1<y1 _)       = absurd (๐โ.irrefl (๐โ.โก-transr x1<y1 (sym x1โกy1)))
  โร<-is-prop _ _ (both< _ x2<y2)     (fst< _ x2โกy2)        = absurd (๐โ.irrefl (๐โ.โก-transr x2<y2 (sym x2โกy2)))
  โร<-is-prop _ _ (both< x1<y1 _)     (snd< x1โกy1 _)        = absurd (๐โ.irrefl (๐โ.โก-transr x1<y1 (sym x1โกy1)))
  โร<-is-prop _ _ (both< x1<y1 x2<y2) (both< x1<y1โฒ x2<y2โฒ) = apโ both< (๐โ.<-is-prop x1<y1 x1<y1โฒ) (๐โ.<-is-prop x2<y2 x2<y2โฒ)

  โร<-is-strict-order : is-strict-order _โร<_
  โร<-is-strict-order .is-strict-order.irrefl {x} = โร<-irrefl x
  โร<-is-strict-order .is-strict-order.trans {x} {y} {z} = โร<-trans x y z
  โร<-is-strict-order .is-strict-order.has-prop {x} {y} = โร<-is-prop x y

  --------------------------------------------------------------------------------
  -- Left Invariance

  โร-left-invariant : โ (x y z : โ ๐โ โ ร โ ๐โ โ) โ y โร< z โ (x โร y) โร< (x โร z)
  โร-left-invariant (x1 , x2) (y1 , y2) (z1 , z2) (fst< y1<z1 y2โกz2)  = fst< (๐โ.left-invariant y1<z1) (ap (x2 ๐โ.โ_) y2โกz2)
  โร-left-invariant (x1 , x2) (y1 , y2) (z1 , z2) (snd< y1โกz1 y2<z2)  = snd< (ap (x1 ๐โ.โ_) y1โกz1) (๐โ.left-invariant y2<z2)
  โร-left-invariant (x1 , x2) (y1 , y2) (z1 , z2) (both< y1<z1 y2<z2) = both< (๐โ.left-invariant y1<z1) (๐โ.left-invariant y2<z2)

  โร-is-displacement-algebra : is-displacement-algebra _โร<_ ฮตร _โร_
  โร-is-displacement-algebra .is-displacement-algebra.has-monoid = โร-is-monoid
  โร-is-displacement-algebra .is-displacement-algebra.has-strict-order = โร<-is-strict-order
  โร-is-displacement-algebra .is-displacement-algebra.left-invariant {x} {y} {z} = โร-left-invariant x y z

_โแต_ : โ {o r} โ DisplacementAlgebra o r โ DisplacementAlgebra o r โ DisplacementAlgebra o (o โ r)
โ ๐โ โแต ๐โ โ =  โ ๐โ โ ร โ ๐โ โ
(๐โ โแต ๐โ) .structure .DisplacementAlgebra-on._<_ = Product._โร<_ ๐โ ๐โ
(๐โ โแต ๐โ) .structure .DisplacementAlgebra-on.ฮต =  Product.ฮตร ๐โ ๐โ
(๐โ โแต ๐โ) .structure .DisplacementAlgebra-on._โ_ = Product._โร_ ๐โ ๐โ
(๐โ โแต ๐โ) .structure .DisplacementAlgebra-on.has-displacement-algebra = Product.โร-is-displacement-algebra ๐โ ๐โ
โ ๐โ โแต ๐โ โ-set = ร-is-hlevel 2  โ ๐โ โ-set โ ๐โ โ-set

module ProductProperties {o r} {๐โ ๐โ : DisplacementAlgebra o r}
                          where
  private
    module ๐โ = DisplacementAlgebra ๐โ
    module ๐โ = DisplacementAlgebra ๐โ
    open Product ๐โ ๐โ

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  โร-has-ordered-monoid : has-ordered-monoid ๐โ โ has-ordered-monoid ๐โ โ has-ordered-monoid (๐โ โแต ๐โ)
  โร-has-ordered-monoid ๐โ-ordered-monoid ๐โ-ordered-monoid =
    right-invariantโhas-ordered-monoid (๐โ โแต ๐โ) ฮป xโคy โ from-โรโค (โร-right-invariant _ _ _ (to-โรโค xโคy))
    where
      module ๐โ-ordered-monoid = is-ordered-monoid (๐โ-ordered-monoid)
      module ๐โ-ordered-monoid = is-ordered-monoid (๐โ-ordered-monoid)

      โร-right-invariant : โ x y z โ x โรโค y โ (x โร z) โรโค (y โร z)
      โร-right-invariant x y z (bothโค x1โคy1 x2โคy2) = bothโค (๐โ-ordered-monoid.right-invariant x1โคy1) (๐โ-ordered-monoid.right-invariant x2โคy2)
        
  --------------------------------------------------------------------------------
  -- Joins

  โร-has-joins : has-joins ๐โ โ has-joins ๐โ โ has-joins (๐โ โแต ๐โ)
  โร-has-joins ๐โ-joins ๐โ-joins = joins
    where
      module ๐โ-joins = has-joins ๐โ-joins
      module ๐โ-joins = has-joins ๐โ-joins

      joins : has-joins (๐โ โแต ๐โ)
      joins .has-joins.join (x1 , x2) (y1 , y2) = (๐โ-joins.join x1 y1) , (๐โ-joins.join x2 y2)
      joins .has-joins.joinl = from-โรโค (bothโค ๐โ-joins.joinl ๐โ-joins.joinl)
      joins .has-joins.joinr = from-โรโค (bothโค ๐โ-joins.joinr ๐โ-joins.joinr)
      joins .has-joins.universal {x1 , x2} {y1 , y2} {z1 , z2} xโคz yโคz =
        from-โรโค $ bothโค (๐โ-joins.universal (fstโค (to-โรโค xโคz)) (fstโค (to-โรโค yโคz)))
                         (๐โ-joins.universal (sndโค (to-โรโค xโคz)) (sndโค (to-โรโค yโคz)))

  --------------------------------------------------------------------------------
  -- Bottoms

  โร-has-bottom : has-bottom ๐โ โ has-bottom ๐โ โ has-bottom (๐โ โแต ๐โ)
  โร-has-bottom ๐โ-bottom ๐โ-bottom = bottom
    where
      module ๐โ-bottom = has-bottom (๐โ-bottom)
      module ๐โ-bottom = has-bottom (๐โ-bottom)

      bottom : has-bottom (๐โ โแต ๐โ)
      bottom .has-bottom.bot = ๐โ-bottom.bot , ๐โ-bottom.bot
      bottom .has-bottom.is-bottom (x1 , x2) = from-โรโค (bothโค (๐โ-bottom.is-bottom x1) (๐โ-bottom.is-bottom x2))
