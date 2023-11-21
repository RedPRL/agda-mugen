open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.InfiniteProduct
open import Mugen.Algebra.OrderedMonoid

open import Mugen.Order.StrictOrder
open import Mugen.Order.StrictOrder.Coimage

open import Mugen.Data.Coimage

module Mugen.Algebra.Displacement.Coimage where

--------------------------------------------------------------------------------
-- Coimages of Displacement Algebra Homomorphisms
--
-- Given a displacement algebra homomorphism 'f : X → Y', we can construct
-- a new displacement algebra whose carrier set is 'X', quotiented by the equivalence
-- relation 'x ~ y iff f x = f y'.
--
-- This can be useful for constructing subalgebras, as Coim f is /always/ a subalgebra
-- of 'Y'.
--
-- This is split from the construction of coimages of strictly monotone
-- maps for performance reasons. For that construction, see:
-- 'Mugen.Order.StrictOrder.Coimage'

module Coim-of-displacement-hom
  {o r o' r'}
  {X : Displacement-algebra o r} {Y : Displacement-algebra o' r'}
  (f : Displacement-algebra-hom X Y) where
  private
    module X = Displacement-algebra X
    module Y = Displacement-algebra Y
    open Displacement-algebra-hom f
    open Coim-of-strictly-monotone strict-hom public
    open Coim-Path {A = ⌞ X ⌟} {B = ⌞ Y ⌟} (f #_) Y.has-is-set

    instance
      Y-<-hlevel : ∀ {x y n} → H-Level (x Y.< y) (suc n)
      Y-<-hlevel = prop-instance Y.<-thin

      Y-≤-hlevel : ∀ {x y n} → H-Level (x Y.≤ y) (suc n)
      Y-≤-hlevel = prop-instance Y.≤-thin

    X/f : Type (o ⊔ o')
    X/f = Coim {A = ⌞ X ⌟} {B = ⌞ Y ⌟} (f #_)

  --------------------------------------------------------------------------------
  -- Algebra

  _⊗coim_ : X/f → X/f → X/f
  _⊗coim_ = Coim-map₂ (λ x y → x X.⊗ y) λ w x y z p q →
    (pres-⊗ w y ∙ ap₂ Y._⊗_ p q ∙ sym (pres-⊗ x z))

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

  --------------------------------------------------------------------------------
  -- Order

  ⊗coim-left-invariant : ∀ x y z → y coim< z → (x ⊗coim y) coim< (x ⊗coim z)
  ⊗coim-left-invariant = Coim-elim-prop₃ (λ x y z → Π-is-hlevel 1 λ _ → coim<-thin (x ⊗coim y) (x ⊗coim z))
    λ x y z y<z → subst₂ Y._<_ (sym (pres-⊗ x y)) (sym (pres-⊗ x z)) (Y.left-invariant y<z)

Coim-of-displacement-hom
  : ∀ {o r o' r'}
  → {X : Displacement-algebra o r} {Y : Displacement-algebra o' r'}
  → (f : Displacement-algebra-hom X Y)
  → Displacement-algebra (o ⊔ o') r'
Coim-of-displacement-hom f = to-displacement-algebra mk where
  open Displacement-algebra-hom f
  open Coim-of-displacement-hom f
  open make-displacement-algebra

  mk : make-displacement-algebra (Coim-of-strictly-monotone strict-hom)
  mk .ε = εcoim
  mk ._⊗_ = _⊗coim_
  mk .idl {x} = ⊗coim-idl x
  mk .idr {x} = ⊗coim-idr x
  mk .associative {x} {y} {z} = ⊗coim-assoc x y z
  mk .left-invariant {x} {y} {z} = ⊗coim-left-invariant x y z

--------------------------------------------------------------------------------
-- Subalgebra Structure
--
-- As noted before, for 'f : X → Y', 'Coim f' is always a subalgebra of 'Y'.

module _ {o r} {X Y : Displacement-algebra o r} {f : Displacement-algebra-hom X Y} where
  private
    X/f : Displacement-algebra (o ⊔ o) r
    X/f = Coim-of-displacement-hom f

    open Coim-of-displacement-hom f
    module Y = Displacement-algebra Y
    module X/f = Displacement-algebra X/f
    module f = Displacement-algebra-hom f

  Coimage-subalgebra : is-displacement-subalgebra X/f Y
  Coimage-subalgebra = to-displacement-subalgebra mk where
    open make-displacement-subalgebra

    witness : ⌞ X/f ⌟ → ⌞ Y ⌟
    witness = Coim-rec Y.has-is-set (f #_) (λ _ _ p → p)

    mk : make-displacement-subalgebra _ _
    mk .into = witness
    mk .pres-ε = f.pres-ε
    mk .pres-⊗ = Coim-elim-prop₂ (λ _ _ → Y.has-is-set _ _) f.pres-⊗
    mk .strictly-mono = Coim-elim-prop₂ (λ _ _ → Π-is-hlevel 1 λ _ → Y.<-thin) λ _ _ p → p
    mk .inj {x} {y} =
      Coim-elim-prop₂ {C = λ x y → witness x ≡ witness y → x ≡ y}
        (λ _ _ → Π-is-hlevel 1 λ _ → squash _ _)
        glue
        x y

--------------------------------------------------------------------------------
-- Joins

  Coim-of-displacement-hom-has-joins
    : (X-joins : has-joins X) → (Y-joins : has-joins Y)
    → preserves-joins X-joins Y-joins f
    → has-joins X/f
  Coim-of-displacement-hom-has-joins X-joins Y-joins f-preserves-joins = joins
    where
      module X-joins = has-joins X-joins
      module Y-joins = has-joins Y-joins

      coim-join : ⌞ X/f ⌟ → ⌞ X/f ⌟ → ⌞ X/f ⌟
      coim-join = Coim-map₂ X-joins.join λ w x y z p q →
        f # X-joins .has-joins.join w y           ≡⟨ f-preserves-joins w y ⟩
        Y-joins .has-joins.join (f # w) (f # y) ≡⟨ ap₂ (Y-joins .has-joins.join) p q ⟩
        Y-joins .has-joins.join (f # x) (f # z) ≡˘⟨ f-preserves-joins x z ⟩
        f # X-joins .has-joins.join x z ∎

      coim-joinl : ∀ x y → inc x coim≤ coim-join (inc x) (inc y)
      coim-joinl x y with X-joins.joinl {x = x} {y = y}
      ... | inl x≡y = inl (ap inc x≡y)
      ... | inr x<y = inr (f.strict-mono x<y)

      coim-joinr : ∀ x y → inc y coim≤ coim-join (inc x) (inc y)
      coim-joinr x y with X-joins.joinr {x = x} {y = y}
      ... | inl x≡y = inl (ap inc x≡y)
      ... | inr x<y = inr (f.strict-mono x<y)

      coim-universal : ∀ x y z → (inc x) coim≤ (inc z) → (inc y) coim≤ (inc z) → coim-join (inc x) (inc y) coim≤ (inc z)
      coim-universal x y z x≤z y≤z =
        Y≤→coim≤ $ Y.≤-trans
          (inl (f-preserves-joins x y))
          (Y-joins.universal (coim≤→Y≤ x≤z) (coim≤→Y≤ y≤z))

      joins : has-joins (Coim-of-displacement-hom f)
      joins .has-joins.join = coim-join
      joins .has-joins.joinl {x} {y} =
        Coim-elim-prop₂ {C = λ x y → x coim≤ (coim-join x y)}
          (λ x y → X/f.≤-thin) coim-joinl x y
      joins .has-joins.joinr {x} {y} =
        Coim-elim-prop₂ {C = λ x y → y coim≤ (coim-join x y)}
          (λ x y → X/f.≤-thin) coim-joinr x y
      joins .has-joins.universal {x} {y} {z} =
        Coim-elim-prop₃ {C = λ x y z → x coim≤ z → y coim≤ z → coim-join x y coim≤ z}
          (λ x y z → Π-is-hlevel 1 λ _ → Π-is-hlevel 1 λ _ → X/f.≤-thin) coim-universal x y z
