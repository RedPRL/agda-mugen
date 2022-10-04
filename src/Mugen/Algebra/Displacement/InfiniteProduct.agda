module Mugen.Algebra.Displacement.InfiniteProduct where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Axioms.LPO
open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

module Inf {o r} (𝒟 : DisplacementAlgebra o r) where
  private
    module 𝒟 = DisplacementAlgebra 𝒟
    open 𝒟 using (ε; _⊗_)

  -- NOTE: This is classically equivalent to the definition presented in the paper,
  -- but less annoying to work with constructively.
  -- However, we still are required to assume one (potentially) non-constructive
  -- principle for showing later properties.
  record _inf<_ (f g : Nat → ⌞ 𝒟 ⌟) : Type (o ⊔ r) where
    constructor inf-<
    field
      ≤-everywhere : ∀ n → 𝒟 [ f n ≤ g n ]ᵈ 
      <-somewhere  : ∃[ n ∈ Nat ] (𝒟 [ f n < g n ]ᵈ)
 
  open _inf<_ public

  inf≤-everywhere : ∀ {f g} → non-strict _inf<_ f g → ∀ n → 𝒟 [ f n ≤ g n ]ᵈ
  inf≤-everywhere (inl f≡g) n = inl (happly f≡g n)
  inf≤-everywhere (inr f<g) n = ≤-everywhere f<g n

  inf<-irrefl : ∀ (f : Nat → ⌞ 𝒟 ⌟) → f inf< f → ⊥
  inf<-irrefl f f<f = ∥-∥-rec (hlevel 1) (λ { (_ , fn<fn) → 𝒟.irrefl fn<fn }) (<-somewhere f<f)

  inf<-trans : ∀ (f g h : Nat → ⌞ 𝒟 ⌟) → f inf< g → g inf< h → f inf< h
  inf<-trans f g h f<g g<h .≤-everywhere n = 𝒟.≤-trans (≤-everywhere f<g n) (≤-everywhere g<h n)
  inf<-trans f g h f<g g<h .<-somewhere = ∥-∥-map (λ { (n , fn<gn) → n , 𝒟.≤-transr fn<gn (≤-everywhere g<h n) }) (<-somewhere f<g)

  inf<-is-prop : ∀ f g  → is-prop (f inf< g) 
  inf<-is-prop f g f<g f<g′ i .≤-everywhere n = 𝒟.≤-is-prop (≤-everywhere f<g n) (≤-everywhere f<g′ n) i
  inf<-is-prop f g f<g f<g′ i .<-somewhere = squash (<-somewhere f<g) (<-somewhere f<g′) i

  inf-is-strict-order : is-strict-order _inf<_
  inf-is-strict-order .is-strict-order.irrefl {x} = inf<-irrefl x
  inf-is-strict-order .is-strict-order.trans {x} {y} {z} = inf<-trans x y z
  inf-is-strict-order .is-strict-order.has-prop {x} {y} = inf<-is-prop x y

  _⊗∞_ : (Nat → ⌞ 𝒟 ⌟) → (Nat → ⌞ 𝒟 ⌟) → (Nat → ⌞ 𝒟 ⌟)
  f ⊗∞ g = λ n → f n ⊗ g n

  ε∞ : Nat → ⌞ 𝒟 ⌟
  ε∞ _ = ε

  ⊗∞-associative : ∀ (f g h : Nat → ⌞ 𝒟 ⌟) → (f ⊗∞ (g ⊗∞ h)) ≡ ((f ⊗∞ g) ⊗∞ h)
  ⊗∞-associative f g h = funext λ x → 𝒟.associative 

  ⊗∞-idl : ∀ (f : Nat → ⌞ 𝒟 ⌟) → (ε∞ ⊗∞ f) ≡ f
  ⊗∞-idl f = funext λ x → 𝒟.idl 

  ⊗∞-idr : ∀ (f : Nat → ⌞ 𝒟 ⌟) → (f ⊗∞ ε∞) ≡ f
  ⊗∞-idr f = funext λ x → 𝒟.idr 

  ⊗∞-left-invariant : ∀ (f g h : Nat → ⌞ 𝒟 ⌟) → g inf< h → (f ⊗∞ g) inf< (f ⊗∞ h)
  ⊗∞-left-invariant f g h g<h .≤-everywhere n = 𝒟.left-invariant-≤ (≤-everywhere g<h n)
  ⊗∞-left-invariant f g h g<h .<-somewhere = ∥-∥-map (λ { (n , gn<hn) → n , 𝒟.left-invariant gn<hn }) (<-somewhere g<h)

  ⊗∞-is-magma : is-magma _⊗∞_
  ⊗∞-is-magma .has-is-set = Π-is-hlevel 2 (λ _ → ⌞ 𝒟 ⌟-set)

  ⊗∞-is-semigroup : is-semigroup _⊗∞_
  ⊗∞-is-semigroup .has-is-magma = ⊗∞-is-magma
  ⊗∞-is-semigroup .associative {f} {g} {h} = ⊗∞-associative f g h

  ⊗∞-is-monoid : is-monoid ε∞ _⊗∞_
  ⊗∞-is-monoid .has-is-semigroup = ⊗∞-is-semigroup
  ⊗∞-is-monoid .idl {f} = ⊗∞-idl f
  ⊗∞-is-monoid .idr {f} = ⊗∞-idr f

  ⊗∞-is-displacement-algebra : is-displacement-algebra _inf<_ ε∞ _⊗∞_
  ⊗∞-is-displacement-algebra .is-displacement-algebra.has-monoid = ⊗∞-is-monoid
  ⊗∞-is-displacement-algebra .is-displacement-algebra.has-strict-order = inf-is-strict-order
  ⊗∞-is-displacement-algebra .is-displacement-algebra.left-invariant {f} {g} {h} = ⊗∞-left-invariant f g h

InfProd : ∀ {o r} → DisplacementAlgebra o r → DisplacementAlgebra o (o ⊔ r)
InfProd {o = o} {r = r} 𝒟 = displacement
  where
    open Inf 𝒟

    displacement : DisplacementAlgebra o (o ⊔ r)
    ⌞ displacement ⌟ =  Nat → ⌞ 𝒟 ⌟
    displacement .structure .DisplacementAlgebra-on._<_ = _inf<_
    displacement .structure .DisplacementAlgebra-on.ε = ε∞
    displacement .structure .DisplacementAlgebra-on._⊗_ = _⊗∞_
    displacement .structure .DisplacementAlgebra-on.has-displacement-algebra = ⊗∞-is-displacement-algebra
    ⌞ displacement ⌟-set = Π-is-hlevel 2 (λ _ → ⌞ 𝒟 ⌟-set)

  -- All of these results requires a single non-constructive principle.
  -- Namely, we require that if '∀ n. f n ≤ g n', then 'f ≡ g', or there is some 'k' where 'f k < g k'.
  -- See Mugen.Axioms.LPO for a distillation of LPO into Markov's Principle + LEM
module InfProperties {o r} {𝒟 : DisplacementAlgebra o r} (_≡?_ : Discrete ⌞ 𝒟 ⌟) (𝒟-lpo : LPO (DA→SO 𝒟) _≡?_) where
  open Inf 𝒟
  open DisplacementAlgebra 𝒟

  lpo : ∀ {f g} → (∀ n → 𝒟 [ f n ≤ g n ]ᵈ) → InfProd 𝒟 [ f ≤ g ]ᵈ
  lpo p = ⊎-mapr (λ lt → Inf.inf-< p lt) (𝒟-lpo p)

  ⊗∞-has-ordered-monoid : (∀ {f g} → (∀ n → 𝒟 [ f n ≤ g n ]ᵈ) → non-strict _inf<_ f g) → has-ordered-monoid 𝒟 → has-ordered-monoid (InfProd 𝒟)
  ⊗∞-has-ordered-monoid lpo 𝒟-ordered-monoid = right-invariant→has-ordered-monoid (InfProd 𝒟) ⊗∞-right-invariant
    where
      open is-ordered-monoid 𝒟-ordered-monoid

      ⊗∞-right-invariant : ∀ {f g h} → non-strict _inf<_ f g → non-strict _inf<_ (f ⊗∞ h) (g ⊗∞ h)
      ⊗∞-right-invariant f≤g = lpo λ n → right-invariant (inf≤-everywhere f≤g n)

  ⊗∞-has-bottom : has-bottom 𝒟 → has-bottom (InfProd 𝒟)
  ⊗∞-has-bottom 𝒟-bottom = bottom
    where
      open has-bottom 𝒟-bottom

      bottom : has-bottom (InfProd 𝒟)
      bottom .has-bottom.bot _ = bot
      bottom .has-bottom.is-bottom f = lpo λ n → is-bottom (f n)

  ⊗∞-has-joins : has-joins 𝒟 → has-joins (InfProd 𝒟)
  ⊗∞-has-joins 𝒟-joins = joins
    where
      open has-joins 𝒟-joins

      joins : has-joins (InfProd 𝒟)
      joins .has-joins.join f g n = join (f n) (g n)
      joins .has-joins.joinl = lpo λ _ → joinl
      joins .has-joins.joinr = lpo λ _ → joinr
      joins .has-joins.universal f≤h g≤h = lpo λ n → universal (inf≤-everywhere f≤h n) (inf≤-everywhere g≤h n)

