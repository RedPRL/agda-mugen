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

module Coimage {o r} {X Y : DisplacementAlgebra o r} (f : DisplacementAlgebra-hom X Y) where
  private
    module X = DisplacementAlgebra X
    module Y = DisplacementAlgebra Y
    open DisplacementAlgebra-hom f

  X/f : Type o
  X/f = Coim (f ⟨$⟩_)

  _⊗coim_ : X/f → X/f → X/f
  _⊗coim_ = Coim-rec₂ squash (λ x y → inc (x X.⊗ y)) λ w x y z p q → 
    glue (w X.⊗ y) (x X.⊗ z) (pres-⊗ w y ∙ ap₂ Y._⊗_ p q ∙ sym (pres-⊗ x z)) 

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

  coim-rel : X/f → X/f → n-Type r 1
  coim-rel =
    Coim-rec₂ (hlevel 2)
      (λ x y → el ((f ⟨$⟩ x) Y.< (f ⟨$⟩ y)) Y.<-is-prop)
      (λ w x y z p q → n-ua (prop-ext Y.<-is-prop Y.<-is-prop (subst₂ Y._<_ p q) (subst₂ Y._<_ (sym p) (sym q))))

  _coim<_ : X/f → X/f → Type r
  x coim< y = ∣ coim-rel x y ∣

  coim<-is-prop : ∀ x y → is-prop (x coim< y)
  coim<-is-prop x y = is-tr (coim-rel x y)

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
