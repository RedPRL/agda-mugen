open import Mugen.Data.Coimage

open import Mugen.Order.StrictOrder

open import Mugen.Prelude

module Mugen.Order.StrictOrder.Coimage where

--------------------------------------------------------------------------------
-- Coimages of Strictly Monotonic Maps
--
-- Given a strictly monotonic map 'f : X → Y', we can construct
-- a new strict order whose carrier set is 'X', quotiented by the equivalence
-- relation 'x ~ y iff f x = f y'.
--
-- This can be useful for constructing suborders as Coim f is /always/ a suborder of
-- of 'Y'.

module Coim-of-strictly-monotone
  {o r o' r'}
  {X : Strict-order o r} {Y : Strict-order o' r'}
  (f : Strictly-monotone X Y)
  where
  private
    module X = Strict-order X
    module Y = Strict-order Y
    open Coim-Path {A = ⌞ X ⌟} {B = ⌞ Y ⌟} (f #_) Y.has-is-set

    instance
      Y-<-hlevel : ∀ {x y n} → H-Level (x Y.< y) (suc n)
      Y-<-hlevel = prop-instance Y.<-thin

      Y-≤-hlevel : ∀ {x y n} → H-Level (x Y.≤ y) (suc n)
      Y-≤-hlevel = prop-instance Y.≤-thin

  private
    X/f : Type (o ⊔ o')
    X/f = Coim {A = ⌞ X ⌟} {B = ⌞ Y ⌟} (f #_)

  coim-lt : X/f → X/f → n-Type r' 1
  coim-lt =
    Coim-rec₂ (hlevel 2)
      (λ x y → el ((f # x) Y.< (f # y)) Y.<-thin)
      (λ w x y z p q → n-ua (prop-ext Y.<-thin Y.<-thin (subst₂ Y._<_ p q) (subst₂ Y._<_ (sym p) (sym q))))

  coim-le : X/f → X/f → n-Type (o' ⊔ r') 1
  coim-le =
    Coim-rec₂ (hlevel 2)
      (λ x y → el ((f # x) Y.≤ (f # y)) Y.≤-thin)
      (λ w x y z p q → n-ua (prop-ext Y.≤-thin Y.≤-thin (subst₂ Y._≤_ p q) (subst₂ Y._≤_ (sym p) (sym q))))

  _coim<_ : X/f → X/f → Type r'
  x coim< y = ∣ coim-lt x y ∣

  coim<-thin : ∀ x y → is-prop (x coim< y)
  coim<-thin x y = is-tr (coim-lt x y)

  coim<-irrefl : ∀ x → x coim< x → ⊥
  coim<-irrefl =
    Coim-elim-prop (λ x → hlevel 1)
      (λ _ → Y.<-irrefl)

  coim<-trans : ∀ x y z → x coim< y → y coim< z → x coim< z
  coim<-trans =
    Coim-elim-prop₃ (λ x y z → Π-is-hlevel 1 λ _ → Π-is-hlevel 1 (λ _ → coim<-thin x z))
      (λ _ _ _ → Y.<-trans)

  --------------------------------------------------------------------------------
  -- Characterizing ≤

  _coim≤_ : X/f → X/f → Type (o ⊔ o' ⊔ r')
  _coim≤_ = non-strict _coim<_

  coim≤-is-prop : ∀ x y → is-prop (x coim≤ y)
  coim≤-is-prop x y = disjoint-⊎-is-prop (squash x y) (coim<-thin x y) λ (x≡y , x<y) → coim<-irrefl y (subst _ x≡y x<y)

  coim≤→Y≤ : ∀ {x y} → x coim≤ y → Coim-image x Y.≤ Coim-image y
  coim≤→Y≤ {x} {y} =
    Coim-elim-prop₂ {C = λ x y → x coim≤ y → Coim-image x Y.≤ Coim-image y}
      (λ _ _ → hlevel 1)
      pf x y
      where
        pf : ∀ x y → inc x coim≤ inc y → f # x Y.≤ f # y
        pf x y (inl x≡y) = inl (Coim-path x≡y)
        pf x y (inr x<y) = inr x<y

  Y≤→coim≤ : ∀ {x y} → Coim-image x Y.≤ Coim-image y → x coim≤ y
  Y≤→coim≤ {x} {y} =
    Coim-elim-prop₂ {C = λ x y → Coim-image x Y.≤ Coim-image y → x coim≤ y}
    (λ _ _ → Π-is-hlevel 1 λ _ → coim≤-is-prop _ _)
    pf x y
    where
      pf : ∀ x y → f # x Y.≤ f # y → inc x coim≤ inc y
      pf x y (inl p) = inl (glue x y p)
      pf x y (inr x<y) = inr x<y

--------------------------------------------------------------------------------
-- Bundle

Coim-of-strictly-monotone
  : ∀ {o r o' r'}
  → {X : Strict-order o r} {Y : Strict-order o' r'}
  → (f : Strictly-monotone X Y)
  → Strict-order (o ⊔ o') r'
Coim-of-strictly-monotone {r' = r'} f = to-strict-order mk where
  open make-strict-order
  open Coim-of-strictly-monotone f

  mk : make-strict-order r' _
  mk ._<_ = _coim<_
  mk .<-irrefl {x} = coim<-irrefl x
  mk .<-trans {x} {y} {z} = coim<-trans x y z
  mk .<-thin {x} {y} = coim<-thin x y
  mk .has-is-set = squash
