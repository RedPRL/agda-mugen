module Mugen.Algebra.Displacement.Coimage where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.InfiniteProduct
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

open import Mugen.Data.Coimage

--------------------------------------------------------------------------------
-- Coimages of Displacement Algebra Homomorphisms
--
-- Given a displacement algebra homomorphism 'f : X → Y', we can construct
-- a new displacement algebra whose carrier set is 'X', quotiented by the equivalence
-- relation 'x ~ y iff f x = f y'.
--
-- This can be useful for constructing subalgebras, as Coim f is /always/ a subalgebra
-- of 'Y'.

module Coimage {o r} {X Y : DisplacementAlgebra o r} (f : DisplacementAlgebra-hom X Y) where
  private
    module X = DisplacementAlgebra X
    module Y = DisplacementAlgebra Y
    open DisplacementAlgebra-hom f
    open Coim-Path (f ⟨$⟩_) ⌞ Y ⌟-set

    instance
      Y-<-hlevel : ∀ {x y n} → H-Level (x Y.< y) (suc n)
      Y-<-hlevel = prop-instance Y.<-is-prop

      Y-≤-hlevel : ∀ {x y n} → H-Level (x Y.≤ y) (suc n)
      Y-≤-hlevel = prop-instance Y.≤-is-prop

  X/f : Type o
  X/f = Coim (f ⟨$⟩_)

  _⊗coim_ : X/f → X/f → X/f
  _⊗coim_ = Coim-map₂ (λ x y → x X.⊗ y) λ w x y z p q → 
    (pres-⊗ w y ∙ ap₂ Y._⊗_ p q ∙ sym (pres-⊗ x z)) 

  --------------------------------------------------------------------------------
  -- Algebra

  εcoim : X/f 
  εcoim = inc X.ε

  ⊗coim-idl : ∀ x → εcoim ⊗coim x ≡ x
  ⊗coim-idl = Coim-elim-prop (λ x → squash (εcoim ⊗coim x) x) (λ x i → inc (X.idl {x} i))

  ⊗coim-idr : ∀ x → x ⊗coim εcoim ≡ x
  ⊗coim-idr =
    Coim-elim-prop (λ x → squash (x ⊗coim εcoim) x)
      (λ x i → inc (X.idr {x} i))

  ⊗coim-assoc : ∀ x y z → x ⊗coim (y ⊗coim z) ≡ (x ⊗coim y) ⊗coim z
  ⊗coim-assoc =
    Coim-elim-prop₃ (λ x y z → squash (x ⊗coim (y ⊗coim z)) ((x ⊗coim y) ⊗coim z))
      (λ x y z i → inc (X.associative {x} {y} {z} i))

  ⊗coim-is-magma : is-magma _⊗coim_
  ⊗coim-is-magma .has-is-set = squash

  ⊗coim-is-semigroup : is-semigroup _⊗coim_
  ⊗coim-is-semigroup .has-is-magma = ⊗coim-is-magma
  ⊗coim-is-semigroup .associative {x} {y} {z} = ⊗coim-assoc x y z

  ⊗coim-is-monoid : is-monoid εcoim _⊗coim_
  ⊗coim-is-monoid .has-is-semigroup = ⊗coim-is-semigroup
  ⊗coim-is-monoid .idl {x} = ⊗coim-idl x
  ⊗coim-is-monoid .idr {x} = ⊗coim-idr x

  --------------------------------------------------------------------------------
  -- Order

  coim-lt : X/f → X/f → n-Type r 1
  coim-lt =
    Coim-rec₂ (hlevel 2)
      (λ x y → el ((f ⟨$⟩ x) Y.< (f ⟨$⟩ y)) Y.<-is-prop)
      (λ w x y z p q → n-ua (prop-ext Y.<-is-prop Y.<-is-prop (subst₂ Y._<_ p q) (subst₂ Y._<_ (sym p) (sym q))))

  coim-le : X/f → X/f → n-Type (o ⊔ r) 1
  coim-le =
    Coim-rec₂ (hlevel 2)
      (λ x y → el ((f ⟨$⟩ x) Y.≤ (f ⟨$⟩ y)) Y.≤-is-prop)
      (λ w x y z p q → n-ua (prop-ext Y.≤-is-prop Y.≤-is-prop (subst₂ Y._≤_ p q) (subst₂ Y._≤_ (sym p) (sym q))))

  _coim<_ : X/f → X/f → Type r
  x coim< y = ∣ coim-lt x y ∣


  coim<-is-prop : ∀ x y → is-prop (x coim< y)
  coim<-is-prop x y = is-tr (coim-lt x y)


  coim<-irrefl : ∀ x → x coim< x → ⊥
  coim<-irrefl =
    Coim-elim-prop (λ x → hlevel 1)
      (λ _ → Y.irrefl)

  coim<-trans : ∀ x y z → x coim< y → y coim< z → x coim< z
  coim<-trans =
    Coim-elim-prop₃ (λ x y z → Π-is-hlevel 1 λ _ → Π-is-hlevel 1 (λ _ → coim<-is-prop x z))
      (λ _ _ _ → Y.trans)

  coim<-is-strict-order : is-strict-order _coim<_
  coim<-is-strict-order .is-strict-order.irrefl {x} = coim<-irrefl x
  coim<-is-strict-order .is-strict-order.trans {x} {y} {z} = coim<-trans x y z
  coim<-is-strict-order .is-strict-order.has-prop {x} {y} = coim<-is-prop x y

  ⊗coim-left-invariant : ∀ x y z → y coim< z → (x ⊗coim y) coim< (x ⊗coim z)
  ⊗coim-left-invariant = Coim-elim-prop₃ (λ x y z → Π-is-hlevel 1 λ _ → coim<-is-prop (x ⊗coim y) (x ⊗coim z))
    λ x y z y<z → subst₂ Y._<_ (sym (pres-⊗ x y)) (sym (pres-⊗ x z)) (Y.left-invariant y<z)
 
  ⊗coim-is-displacement-algebra : is-displacement-algebra _coim<_ εcoim _⊗coim_
  ⊗coim-is-displacement-algebra .is-displacement-algebra.has-monoid = ⊗coim-is-monoid
  ⊗coim-is-displacement-algebra .is-displacement-algebra.has-strict-order = coim<-is-strict-order
  ⊗coim-is-displacement-algebra .is-displacement-algebra.left-invariant {x} {y} {z} = ⊗coim-left-invariant x y z

  --------------------------------------------------------------------------------
  -- Characterizing ≤

  _coim≤_ : X/f → X/f → Type (o ⊔ r)
  _coim≤_ = non-strict _coim<_

  coim≤-is-prop : ∀ x y → is-prop (x coim≤ y)
  coim≤-is-prop x y = disjoint-⊎-is-prop (squash x y) (coim<-is-prop x y) λ (x≡y , x<y) → coim<-irrefl y (subst _ x≡y x<y)

  coim≤→Y≤ : ∀ {x y} → x coim≤ y → Y [ Coim-image x ≤ Coim-image y ]ᵈ
  coim≤→Y≤ {x} {y} =
    Coim-elim-prop₂ {C = λ x y → x coim≤ y → Y [ Coim-image x ≤ Coim-image y ]ᵈ}
      (λ _ _ → hlevel 1)
      pf x y
      where
        pf : ∀ x y → inc x coim≤ inc y → Y [ f ⟨$⟩ x ≤ f ⟨$⟩ y ]ᵈ
        pf x y (inl x≡y) = inl (Coim-path x≡y)
        pf x y (inr x<y) = inr x<y

  Y≤→coim≤ : ∀ {x y} → Y [ Coim-image x ≤ Coim-image y ]ᵈ → x coim≤ y
  Y≤→coim≤ {x} {y} =
    Coim-elim-prop₂ {C = λ x y → Y [ Coim-image x ≤ Coim-image y ]ᵈ → x coim≤ y}
    (λ _ _ → Π-is-hlevel 1 λ _ → coim≤-is-prop _ _)
    pf x y
    where
      pf : ∀ x y → Y [ f ⟨$⟩ x ≤ f ⟨$⟩ y ]ᵈ → inc x coim≤ inc y
      pf x y (inl p) = inl (glue x y p)
      pf x y (inr x<y) = inr x<y

  private instance
    coim<-hlevel : ∀ {x y n} → H-Level (x coim< y) (suc n)
    coim<-hlevel {x = x} {y = y} = prop-instance (coim<-is-prop x y)


Coimage : ∀ {o r} {X Y : DisplacementAlgebra o r} (f : DisplacementAlgebra-hom X Y) → DisplacementAlgebra o r
Coimage {o} {r} f = displacement
  where
    open Coimage f

    displacement : DisplacementAlgebra o r
    ⌞ displacement ⌟ = X/f
    displacement .structure .DisplacementAlgebra-on._<_ = _coim<_
    displacement .structure .DisplacementAlgebra-on.ε = εcoim
    displacement .structure .DisplacementAlgebra-on._⊗_ = _⊗coim_
    displacement .structure .DisplacementAlgebra-on.has-displacement-algebra = ⊗coim-is-displacement-algebra
    ⌞ displacement ⌟-set = squash

--------------------------------------------------------------------------------
-- Subalgebra Structure
--
-- As noted before, for 'f : X → Y', 'Coim f' is always a subalgebra of 'Y'.

module _ {o r} {X Y : DisplacementAlgebra o r} {f : DisplacementAlgebra-hom X Y} where
  private
    open Coimage f
    module Y = DisplacementAlgebra Y
    module X/f = DisplacementAlgebra (Coimage f)
    open DisplacementAlgebra-hom f

  Coimage-subalgebra : is-displacement-subalgebra (Coimage f) Y
  Coimage-subalgebra = subalgebra
    where
      into : ⌞ Coimage f ⌟ → ⌞ Y ⌟
      into = Coim-rec  ⌞ Y ⌟-set (f ⟨$⟩_) λ _ _ p → p
  
      subalgebra : is-displacement-subalgebra (Coimage f) Y
      subalgebra .is-displacement-subalgebra.into ._⟨$⟩_ = into
      subalgebra .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-ε = pres-ε
      subalgebra .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-⊗ = Coim-elim-prop₂ (λ _ _ → ⌞ Y ⌟-set _ _) pres-⊗
      subalgebra .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.strictly-mono {x} {y} =
        Coim-elim-prop₂ {C = λ x y → x coim< y → into x Y.< into y} (λ _ _ → Π-is-hlevel 1 (λ _ → Y.<-is-prop)) (λ x y p → p) x y
      subalgebra .is-displacement-subalgebra.inj {x} {y} =
        Coim-elim-prop₂ {C = λ x y → into x ≡ into y → x ≡ y} (λ _ _ → Π-is-hlevel 1 λ _ → squash _ _) glue x y

--------------------------------------------------------------------------------
-- Joins

  Coimage-has-joins : (X-joins : has-joins X) → (Y-joins : has-joins Y) → preserves-joins X-joins Y-joins f → has-joins (Coimage f)
  Coimage-has-joins X-joins Y-joins f-preserves-joins = joins
    where
      module X-joins = has-joins X-joins
      module Y-joins = has-joins Y-joins

      coim-join : X/f → X/f → X/f
      coim-join = Coim-map₂ X-joins.join λ w x y z p q →
        f ⟨$⟩ X-joins .has-joins.join w y           ≡⟨ f-preserves-joins w y ⟩
        Y-joins .has-joins.join (f ⟨$⟩ w) (f ⟨$⟩ y) ≡⟨ ap₂ (Y-joins .has-joins.join) p q ⟩
        Y-joins .has-joins.join (f ⟨$⟩ x) (f ⟨$⟩ z) ≡˘⟨ f-preserves-joins x z ⟩
        f ⟨$⟩ X-joins .has-joins.join x z ∎

      coim-joinl : ∀ x y → inc x coim≤ coim-join (inc x) (inc y)
      coim-joinl x y with X-joins.joinl {x = x} {y = y}
      ... | inl x≡y = inl (ap inc x≡y)
      ... | inr x<y = inr (strictly-mono x<y)

      coim-joinr : ∀ x y → inc y coim≤ coim-join (inc x) (inc y)
      coim-joinr x y with X-joins.joinr {x = x} {y = y}
      ... | inl x≡y = inl (ap inc x≡y)
      ... | inr x<y = inr (strictly-mono x<y)

      coim-universal : ∀ x y z → (inc x) coim≤ (inc z) → (inc y) coim≤ (inc z) → coim-join (inc x) (inc y) coim≤ (inc z)
      coim-universal x y z x≤z y≤z =
        Y≤→coim≤ $ Y.≤-trans
          (inl (f-preserves-joins x y))
          (Y-joins.universal (coim≤→Y≤ x≤z) (coim≤→Y≤ y≤z))

      joins : has-joins (Coimage f)
      joins .has-joins.join = coim-join 
      joins .has-joins.joinl {x} {y} =
        Coim-elim-prop₂ {C = λ x y → x coim≤ (coim-join x y)}
          (λ x y → X/f.≤-is-prop) coim-joinl x y
      joins .has-joins.joinr {x} {y} =
        Coim-elim-prop₂ {C = λ x y → y coim≤ (coim-join x y)}
          (λ x y → X/f.≤-is-prop) coim-joinr x y
      joins .has-joins.universal {x} {y} {z} =
        Coim-elim-prop₃ {C = λ x y z → x coim≤ z → y coim≤ z → coim-join x y coim≤ z}
          (λ x y z → Π-is-hlevel 1 λ _ → Π-is-hlevel 1 λ _ → X/f.≤-is-prop) coim-universal x y z
