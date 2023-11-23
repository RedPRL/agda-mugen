module Mugen.Algebra.Displacement.InfiniteProduct where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Axioms.LPO
open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

--------------------------------------------------------------------------------
-- Infinite Products
-- Section 3.3.5
--
-- The infinite product of a displacement algebra '𝒟' consists
-- of functions 'Nat → 𝒟'. Multiplication is performerd pointwise,
-- and ordering is given by 'f < g' if '∀ n. f n ≤ n' and '∃ n. f n < g n'.

module Inf {o r} (𝒟 : Displacement-algebra o r) where
  private
    module 𝒟 = Displacement-algebra 𝒟
    open 𝒟 using (ε; _⊗_)

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

  --------------------------------------------------------------------------------
  -- Algebra

  ⊗∞-is-magma : is-magma _⊗∞_
  ⊗∞-is-magma .has-is-set = Π-is-hlevel 2 (λ _ → 𝒟.has-is-set)

  ⊗∞-is-semigroup : is-semigroup _⊗∞_
  ⊗∞-is-semigroup .has-is-magma = ⊗∞-is-magma
  ⊗∞-is-semigroup .associative {f} {g} {h} = ⊗∞-associative f g h

  ⊗∞-is-monoid : is-monoid ε∞ _⊗∞_
  ⊗∞-is-monoid .has-is-semigroup = ⊗∞-is-semigroup
  ⊗∞-is-monoid .idl {f} = ⊗∞-idl f
  ⊗∞-is-monoid .idr {f} = ⊗∞-idr f

  --------------------------------------------------------------------------------
  -- Ordering

  record _inf<_ (f g : Nat → ⌞ 𝒟 ⌟) : Type (o ⊔ r) where
    constructor inf-<
    field
      ≤-everywhere : ∀ n →  f n 𝒟.≤ g n
      not-equal    : ¬ ∀ (n : Nat) → f n ≡ g n

  open _inf<_ public

  inf≤-everywhere : ∀ {f g} → non-strict _inf<_ f g → ∀ n → f n 𝒟.≤ g n
  inf≤-everywhere (inl f≡g) n = inl (happly f≡g n)
  inf≤-everywhere (inr f<g) n = ≤-everywhere f<g n

  inf<-irrefl : ∀ (f : Nat → ⌞ 𝒟 ⌟) → f inf< f → ⊥
  inf<-irrefl f f<f = not-equal f<f λ _ → refl

  inf<-trans : ∀ (f g h : Nat → ⌞ 𝒟 ⌟) → f inf< g → g inf< h → f inf< h
  inf<-trans f g h f<g g<h .≤-everywhere n = 𝒟.≤-trans (≤-everywhere f<g n) (≤-everywhere g<h n)
  inf<-trans f g h f<g g<h .not-equal f=h =
    g<h .not-equal λ n → 𝒟.≤-antisym (g<h .≤-everywhere n) $ subst (𝒟._≤ _) (f=h n) (f<g .≤-everywhere n)

  inf<-is-prop : ∀ f g → is-prop (f inf< g)
  inf<-is-prop f g f<g f<g′ i .≤-everywhere n = 𝒟.≤-thin (≤-everywhere f<g n) (≤-everywhere f<g′ n) i
  inf<-is-prop f g f<g f<g′ i .not-equal = hlevel 1 (f<g .not-equal) (f<g′ .not-equal) i

  --------------------------------------------------------------------------------
  -- Left Invariance

  ⊗∞-left-invariant : ∀ (f g h : Nat → ⌞ 𝒟 ⌟) → g inf< h → (f ⊗∞ g) inf< (f ⊗∞ h)
  ⊗∞-left-invariant f g h g<h .≤-everywhere n = 𝒟.left-invariant-≤ (≤-everywhere g<h n)
  ⊗∞-left-invariant f g h g<h .not-equal p =
    g<h .not-equal λ n → 𝒟.≤+≮→= (g<h .≤-everywhere n) (λ gn<hn → 𝒟.<-not-equal (𝒟.left-invariant gn<hn) (p n))


Inf : ∀ {o r} → Displacement-algebra o r → Strict-order o (o ⊔ r)
Inf {o = o} {r = r} 𝒟 = to-strict-order mk where
  module 𝒟 = Displacement-algebra 𝒟
  open Inf 𝒟
  open make-strict-order

  mk : make-strict-order (o ⊔ r) (Nat → ⌞ 𝒟 ⌟)
  mk ._<_ = _inf<_
  mk .<-irrefl {x} = inf<-irrefl x
  mk .<-trans {x} {y} {z} = inf<-trans x y z
  mk .<-thin {x} {y} = inf<-is-prop x y
  mk .has-is-set = Π-is-hlevel 2 λ _ → 𝒟.has-is-set

InfProd : ∀ {o r} → Displacement-algebra o r → Displacement-algebra o (o ⊔ r)
InfProd {o = o} {r = r} 𝒟 = to-displacement-algebra mk where
  module 𝒟 = Displacement-algebra 𝒟
  open Inf 𝒟
  open make-displacement-algebra

  mk : make-displacement-algebra (Inf 𝒟)
  mk .ε = ε∞
  mk ._⊗_ = _⊗∞_
  mk .idl {x} = ⊗∞-idl x
  mk .idr {x} = ⊗∞-idr x
  mk .associative {x} {y} {z} = ⊗∞-associative x y z
  mk .left-invariant {x} {y} {z} = ⊗∞-left-invariant x y z

-- All of the following results require a form of the Limited Principle of Omniscience,
-- which states that if '∀ n. f n ≤ g n', then 'f ≡ g', or there is some 'k' where 'f k < g k'.
-- See Mugen.Axioms.LPO for a distillation of LPO into Markov's Principle + LEM
module InfProperties
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (_≡?_ : Discrete ⌞ 𝒟 ⌟) (𝒟-wlpo : WLPO 𝒟.strict-order _≡?_)
  where
  private
    open Inf 𝒟
    module 𝒟∞ = Displacement-algebra (InfProd 𝒟)

    wlpo : ∀ {f g} → (∀ n → f n 𝒟.≤ g n) → f 𝒟∞.≤ g
    wlpo p = Dec-rec (λ f=g → inl $ funext f=g) (λ neq → inr $ Inf.inf-< p neq) (𝒟-wlpo p)

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  ⊗∞-has-ordered-monoid : has-ordered-monoid 𝒟 → has-ordered-monoid (InfProd 𝒟)
  ⊗∞-has-ordered-monoid 𝒟-om =
    right-invariant→has-ordered-monoid
      (InfProd 𝒟)
      ⊗∞-right-invariant
    where
      open is-ordered-monoid 𝒟-om

      ⊗∞-right-invariant : ∀ {f g h} → f 𝒟∞.≤ g → (f ⊗∞ h) 𝒟∞.≤ (g ⊗∞ h)
      ⊗∞-right-invariant f≤g = wlpo (λ n → right-invariant (inf≤-everywhere f≤g n))

  --------------------------------------------------------------------------------
  -- Joins

  ⊗∞-has-joins : has-joins 𝒟 → has-joins (InfProd 𝒟)
  ⊗∞-has-joins 𝒟-joins = joins
    where
      open has-joins 𝒟-joins

      joins : has-joins (InfProd 𝒟)
      joins .has-joins.join f g n = join (f n) (g n)
      joins .has-joins.joinl = wlpo λ _ → joinl
      joins .has-joins.joinr = wlpo λ _ → joinr
      joins .has-joins.universal f≤h g≤h = wlpo λ n → universal (inf≤-everywhere f≤h n) (inf≤-everywhere g≤h n)

  --------------------------------------------------------------------------------
  -- Bottom

  ⊗∞-has-bottom : has-bottom 𝒟 → has-bottom (InfProd 𝒟)
  ⊗∞-has-bottom 𝒟-bottom = bottom
    where
      open has-bottom 𝒟-bottom

      bottom : has-bottom (InfProd 𝒟)
      bottom .has-bottom.bot _ = bot
      bottom .has-bottom.is-bottom f = wlpo λ n → is-bottom (f n)
