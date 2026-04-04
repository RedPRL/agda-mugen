-- vim: nowrap
module Mugen.Algebra.Displacement.Subalgebra where

open import Mugen.Prelude
open import Mugen.Algebra.OrderedMonoid
import Mugen.Order.Reasoning as Reasoning
open import Mugen.Order.StrictOrder
open import Mugen.Order.Lattice
open import Mugen.Algebra.Displacement

private variable
  o o' o'' r r' r'' : Level

--------------------------------------------------------------------------------
-- Subalgebras of Displacement Algebras

record is-full-subdisplacement
  {A : Poset o r} {B : Poset o' r'}
  (X : Displacement-on A) (Y : Displacement-on B)
  (f : Strictly-monotone A B)
  : Type (o ⊔ o' ⊔ r ⊔ r')
  where
  no-eta-equality
  field
    has-is-full-subposet : is-full-subposet f
    has-is-displacement-hom : is-displacement-hom X Y f
  open is-full-subposet has-is-full-subposet public
  open is-displacement-hom has-is-displacement-hom public

module _
  {A : Poset o r} {B : Poset o' r'} {C : Poset o'' r''}
  {X : Displacement-on A} {Y : Displacement-on B} {Z : Displacement-on C}
  where
  open is-full-subdisplacement

  ∘-is-full-subdisplacement
    : {f : Strictly-monotone B C} {g : Strictly-monotone A B}
    → is-full-subdisplacement Y Z f
    → is-full-subdisplacement X Y g
    → is-full-subdisplacement X Z (strictly-monotone-∘ f g)
  ∘-is-full-subdisplacement {f = f} {g = g} f-sub g-sub .has-is-full-subposet =
    ∘-is-full-subposet (f-sub .has-is-full-subposet) (g-sub .has-is-full-subposet)
  ∘-is-full-subdisplacement {f = f} {g = g} f-sub g-sub .has-is-displacement-hom =
    ∘-is-displacement-hom (f-sub .has-is-displacement-hom) (g-sub .has-is-displacement-hom)

--------------------------------------------------------------------------------
-- Builders for Subalgebras

record make-full-subdisplacement
  {A : Poset o r} {B : Poset o' r'}
  (X : Displacement-on A) (Y : Displacement-on B)
  (f : Strictly-monotone A B)
  : Type (o ⊔ o' ⊔ r ⊔ r')
  where
  no-eta-equality
  private
    module A = Reasoning A
    module B = Reasoning B
    module X = Displacement-on X
    module Y = Displacement-on Y
  field
    injective : ∀ {x y : ⌞ A ⌟} → f · x ≡ f · y → x ≡ y
    full : ∀ {x y : ⌞ A ⌟} → f · x B.≤ f · y → x A.≤ y
    pres-ε : f · X.ε ≡ Y.ε
    pres-⊗ : ∀ {x y} → f · (x X.⊗ y) ≡ f · x Y.⊗ f · y
    pres-≤ : ∀ {x y} → x A.≤ y → f · x B.≤ f · y

module _
  {A : Poset o r} {B : Poset o' r'}
  {X : Displacement-on A} {Y : Displacement-on B}
  {f : Strictly-monotone A B}
  where

  to-full-subdisplacement
    : make-full-subdisplacement X Y f
    → is-full-subdisplacement X Y f
  to-full-subdisplacement mk = sub where
    sub : is-full-subdisplacement X Y f
    sub .is-full-subdisplacement.has-is-full-subposet .is-full-subposet.injective =
      mk .make-full-subdisplacement.injective
    sub .is-full-subdisplacement.has-is-full-subposet .is-full-subposet.full =
      mk .make-full-subdisplacement.full
    sub .is-full-subdisplacement.has-is-displacement-hom .is-displacement-hom.pres-ε =
      mk .make-full-subdisplacement.pres-ε
    sub .is-full-subdisplacement.has-is-displacement-hom .is-displacement-hom.pres-⊗ =
      mk .make-full-subdisplacement.pres-⊗

record represents-full-subdisplacement
  {A : Poset o r} {B : Poset o' r'} (Y : Displacement-on B)
  {f : Strictly-monotone A B} (full-subposet : is-full-subposet f)
  : Type (o ⊔ o')
  where
  no-eta-equality

  private
    open is-full-subposet full-subposet
    module A = Reasoning A
    module B = Reasoning B
    module Y = Displacement-on Y
    module f = Strictly-monotone f

  field
    ε : ⌞ A ⌟
    _⊗_ : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟
    pres-ε : f · ε ≡ Y.ε
    pres-⊗ : ∀ {x y} → f · (x ⊗ y) ≡ f · x Y.⊗ f · y

  abstract
    idl : ∀ {x} → ε ⊗ x ≡ x
    idl {x} = injective $ pres-⊗ ∙ ap (Y._⊗ f · x) pres-ε ∙ Y.idl

    idr : ∀ {x} → x ⊗ ε ≡ x
    idr {x} = injective $ pres-⊗ ∙ ap (f · x Y.⊗_) pres-ε ∙ Y.idr

    associative : ∀ {x y z} → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
    associative {x} {y} {z} = injective $
      f · (x ⊗ (y ⊗ z))            ≡⟨ pres-⊗ ⟩
      f · x Y.⊗ f · (y ⊗ z)        ≡⟨ ap (f · x Y.⊗_) pres-⊗ ⟩
      f · x Y.⊗ (f · y Y.⊗ f · z)  ≡⟨ Y.associative ⟩
      (f · x Y.⊗ f · y) Y.⊗ f · z  ≡˘⟨ ap (Y._⊗ f · z) pres-⊗ ⟩
      f · (x ⊗ y) Y.⊗ f · z        ≡˘⟨ pres-⊗ ⟩
      f · ((x ⊗ y) ⊗ z)            ∎

    left-strict-invariant : ∀ {x y z} → y A.≤ z → (x ⊗ y) A.≤[ y ≡ z ] (x ⊗ z)
    left-strict-invariant {x} {y} {z} fy≤fz =
      Σ-map full (λ p → injective ⊙ p ⊙ ap· f) lemma
      where
        lemma : f · (x ⊗ y) B.≤[ f · y ≡ f · z ] f · (x ⊗ z)
        lemma = B.<+=→< (B.=+<→< pres-⊗ $ Y.left-strict-invariant $ f.pres-≤ fy≤fz) (sym pres-⊗)

  displacement-on : Displacement-on A
  displacement-on = to-displacement-on mk where
    mk : make-displacement A
    mk .make-displacement.ε = ε
    mk .make-displacement._⊗_ = _⊗_
    mk .make-displacement.idl = idl
    mk .make-displacement.idr = idr
    mk .make-displacement.associative = associative
    mk .make-displacement.left-strict-invariant = left-strict-invariant

  has-is-full-subdisplacement : is-full-subdisplacement displacement-on Y f
  has-is-full-subdisplacement .is-full-subdisplacement.has-is-full-subposet = full-subposet
  has-is-full-subdisplacement .is-full-subdisplacement.has-is-displacement-hom .is-displacement-hom.pres-ε = pres-ε
  has-is-full-subdisplacement .is-full-subdisplacement.has-is-displacement-hom .is-displacement-hom.pres-⊗ = pres-⊗
