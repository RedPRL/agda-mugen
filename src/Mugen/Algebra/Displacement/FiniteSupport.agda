module Mugen.Algebra.Displacement.FiniteSupport where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.InfiniteProduct
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

open import Mugen.Data.List
open import Mugen.Data.Nat hiding (_<_)
open import Data.Bool

module FinSupport {o r} (𝒟 : DisplacementAlgebra o r) where
  private
    module 𝒟 = DisplacementAlgebra 𝒟
    open 𝒟 using (ε; _⊗_)
    open Inf 𝒟

  --------------------------------------------------------------------------------
  -- Finitely Supported Functions
  --
  -- We represent support as a sort of Gap List, where each of the nats specifies
  -- the offset (plus one) from the last value that is not equal to 'ε'.
  -- For instance, the function
  --
  -- > λ x | x = 3 -> 10
  -- >     | x = 5 -> 13
  -- >     | x = 6 -> 100
  -- >     | otherwise -> ε
  --
  -- would be represented by the list [(2, 10), (1, 13), (0, 100)]

  Support : Type o
  Support = List (⌞ 𝒟 ⌟ × Nat)

  Support-is-set : is-set Support
  Support-is-set = ListPath.is-set→List-is-set (×-is-hlevel 2 ⌞ 𝒟 ⌟-set (hlevel 2))

  --------------------------------------------------------------------------------
  -- Algebra

  shift : Support → Support
  shift [] = []
  shift ((x , n) ∷ xs) = (x , suc n) ∷ xs

  merge : Support → Support → Support
  merge [] ys = ys
  merge (x ∷ xs) [] = x ∷ xs
  merge ((x , zero) ∷ xs) ((y , zero) ∷ ys) = (x ⊗ y , zero) ∷ merge xs ys
  merge ((x , zero) ∷ xs) ((y , suc n) ∷ ys) = (x , zero) ∷ merge xs ((y , n) ∷ ys)
  merge ((x , suc m) ∷ xs) ((y , zero) ∷ ys) = (y , zero) ∷ merge ((x , m) ∷ xs) ys
  merge ((x , suc m) ∷ xs) ((y , suc n) ∷ ys) = shift (merge ((x , m) ∷ xs) ((y , n) ∷ ys))

  merge-idl : ∀ xs → merge [] xs ≡ xs
  merge-idl _ = refl

  merge-idr : ∀ xs → merge xs [] ≡ xs
  merge-idr [] = refl
  merge-idr (x ∷ xs) = refl

  merge-shiftl : ∀ xs y ys → merge (shift xs) ((y , 0) ∷ ys) ≡ (y , 0) ∷ (merge xs ys)
  merge-shiftl [] y ys = refl
  merge-shiftl (x ∷ xs) y ys = refl

  merge-shiftr : ∀ x xs ys → merge ((x , 0) ∷ xs) (shift ys) ≡ (x , 0) ∷ (merge xs ys)
  merge-shiftr x xs [] = ap ((x , 0) ∷_) (sym (merge-idr xs))
  merge-shiftr x xs (y ∷ ys) = refl

  merge-shift-sucl : ∀ x n xs ys → merge ((x , suc n) ∷ xs) (shift ys) ≡ shift (merge ((x , n) ∷ xs) ys)
  merge-shift-sucl x n xs [] = refl
  merge-shift-sucl x n xs (y ∷ ys) = refl

  merge-shift-sucr : ∀ xs y n ys → merge (shift xs) ((y , suc n) ∷ ys) ≡ shift (merge xs ((y , n) ∷ ys))
  merge-shift-sucr [] y n ys = refl
  merge-shift-sucr (x ∷ xs) y n ys = refl

  merge-assoc : ∀ xs ys zs → merge xs (merge ys zs) ≡ merge (merge xs ys) zs
  merge-assoc [] ys zs = refl
  merge-assoc (x ∷ xs) [] zs = refl
  merge-assoc (x ∷ xs) (y ∷ ys) [] = sym (merge-idr (merge (x ∷ xs) (y ∷ ys)))
  merge-assoc ((x , zero) ∷ xs) ((y , zero) ∷ ys) ((z , zero) ∷ zs) =
    ap₂ _∷_ (ap (_, 0) 𝒟.associative) (merge-assoc xs ys zs)
  merge-assoc ((x , zero) ∷ xs) ((y , zero) ∷ ys) ((z , suc o) ∷ zs) =
    ap ((x ⊗ y , 0) ∷_) (merge-assoc xs ys ((z , o) ∷ zs))
  merge-assoc ((x , zero) ∷ xs) ((y , suc n) ∷ ys) ((z , zero) ∷ zs) =
    ap ((x ⊗ z , zero) ∷_) (merge-assoc xs ((y , n) ∷ ys) zs)
  merge-assoc ((x , zero) ∷ xs) ((y , suc n) ∷ ys) ((z , suc o) ∷ zs) =
    merge ((x , 0) ∷ xs) (shift (merge ((y , n) ∷ ys) ((z , o) ∷ zs))) ≡⟨ merge-shiftr x xs (merge ((y , n) ∷ ys) ((z , o) ∷ zs)) ⟩
    (x , 0) ∷ merge xs (merge ((y , n) ∷ ys) ((z , o) ∷ zs))           ≡⟨ ap ((x , 0) ∷_) (merge-assoc xs ((y , n) ∷ ys) ((z , o) ∷ zs)) ⟩
    (x , 0) ∷ merge (merge xs ((y , n) ∷ ys)) ((z , o) ∷ zs)           ∎
  merge-assoc ((x , suc m) ∷ xs) ((y , zero) ∷ ys) ((z , zero) ∷ zs) =
    ap (((y ⊗ z) , 0) ∷_) (merge-assoc ((x , m) ∷ xs) ys zs)
  merge-assoc ((x , suc m) ∷ xs) ((y , zero) ∷ ys) ((z , suc o) ∷ zs) =
    ap ((y , 0) ∷_) (merge-assoc ((x , m) ∷ xs) ys ((z , o) ∷ zs))
  merge-assoc ((x , suc m) ∷ xs) ((y , suc n) ∷ ys) ((z , zero) ∷ zs) =
    (z , 0) ∷ merge ((x , m) ∷ xs) (merge ((y , n) ∷ ys) zs)           ≡⟨ ap ((z , 0) ∷_) (merge-assoc ((x , m) ∷ xs) (((y , n) ∷ ys)) zs) ⟩
    (z , 0) ∷ merge (merge ((x , m) ∷ xs) ((y , n) ∷ ys)) zs           ≡˘⟨ merge-shiftl (merge ((x , m) ∷ xs) ((y , n) ∷ ys)) z zs ⟩
    merge (shift (merge ((x , m) ∷ xs) ((y , n) ∷ ys))) ((z , 0) ∷ zs) ∎
  merge-assoc ((x , suc m) ∷ xs) ((y , suc n) ∷ ys) ((z , suc o) ∷ zs) =
    merge ((x , suc m) ∷ xs) (shift (merge ((y , n) ∷ ys) ((z , o) ∷ zs))) ≡⟨ merge-shift-sucl x m xs (merge ((y , n) ∷ ys) ((z , o) ∷ zs)) ⟩
    shift (merge ((x , m) ∷ xs) (merge ((y , n) ∷ ys) ((z , o) ∷ zs)))     ≡⟨ ap shift (merge-assoc (((x , m) ∷ xs)) (((y , n) ∷ ys)) (((z , o) ∷ zs))) ⟩
    shift (merge (merge ((x , m) ∷ xs) (((y , n) ∷ ys))) (((z , o) ∷ zs))) ≡˘⟨ merge-shift-sucr (merge ((x , m) ∷ xs) ((y , n) ∷ ys)) z o zs ⟩
    merge (shift (merge ((x , m) ∷ xs) ((y , n) ∷ ys))) ((z , suc o) ∷ zs) ∎

  merge-is-magma : is-magma merge
  merge-is-magma .has-is-set = Support-is-set

  merge-is-semigroup : is-semigroup merge
  merge-is-semigroup .has-is-magma = merge-is-magma
  merge-is-semigroup .associative {xs} {ys} {zs} = merge-assoc xs ys zs

  merge-is-monoid : is-monoid [] merge 
  merge-is-monoid .has-is-semigroup = merge-is-semigroup
  merge-is-monoid .idl {xs} = merge-idl xs
  merge-is-monoid .idr {xs} = merge-idr xs

  --------------------------------------------------------------------------------
  -- Interpret Finite Support as an infinite product

  support : Support → Nat → ⌞ 𝒟 ⌟
  support [] n = ε
  support ((x , zero) ∷ xs) zero = x
  support ((x , zero) ∷ xs) (suc n) = support xs n
  support ((x , suc m) ∷ xs) zero = ε
  support ((x , suc m) ∷ xs) (suc n) = support ((x , m) ∷ xs) n

  shift-zero : ∀ xs → support (shift xs) zero ≡ ε
  shift-zero [] = refl
  shift-zero (x ∷ xs) = refl

  shift-suc : ∀ xs ix → support (shift xs) (suc ix) ≡ support xs ix
  shift-suc [] ix = refl
  shift-suc (x ∷ xs) ix = refl

  merge-sound : ∀ xs ys → support (merge xs ys) ≡ (support xs ⊗∞ support ys)
  merge-sound [] ys i n = 𝒟.idl {x = support ys n} (~ i)
  merge-sound (x ∷ xs) [] i n =
    𝒟.idr {x = support (x ∷ xs) n} (~ i)
  merge-sound ((x , zero) ∷ xs) ((y , zero) ∷ ys) i zero =
    x ⊗ y
  merge-sound ((x , zero) ∷ xs) ((y , zero) ∷ ys) i (suc ix) =
    merge-sound xs ys i ix
  merge-sound ((x , zero) ∷ xs) ((y , suc n) ∷ ys) i zero =
    𝒟.idr {x} (~ i)
  merge-sound ((x , zero) ∷ xs) ((y , suc n) ∷ ys) i (suc ix) =
    merge-sound xs ((y , n) ∷ ys) i ix
  merge-sound ((x , suc m) ∷ xs) ((y , zero) ∷ ys) i zero =
    𝒟.idl {y} (~ i)
  merge-sound ((x , suc m) ∷ xs) ((y , zero) ∷ ys) i (suc ix) =
    merge-sound ((x , m) ∷ xs) ys i ix
  merge-sound ((x , suc m) ∷ xs) ((y , suc n) ∷ ys) i zero =
    (shift-zero (merge ((x , m) ∷ xs) ((y , n) ∷ ys)) ∙ sym 𝒟.idl) i
  merge-sound ((x , suc m) ∷ xs) ((y , suc n) ∷ ys) i (suc ix) =
    (shift-suc (merge ((x , m) ∷ xs) ((y , n) ∷ ys)) ix ∙ happly (merge-sound ((x , m) ∷ xs) ((y , n) ∷ ys)) ix) i

  --------------------------------------------------------------------------------
  -- Ordering
  --
  -- For ease of use, we define the ordering of finitely supported functions
  -- via their interpretation into infinite products.

  _sup<_ : Support → Support → Type (o ⊔ r)
  xs sup< ys = support xs inf< support ys

  sup-is-strict-order : is-strict-order _sup<_
  sup-is-strict-order .is-strict-order.irrefl {xs} = inf<-irrefl (support xs)
  sup-is-strict-order .is-strict-order.trans {xs} {ys} {zs} = inf<-trans (support xs) (support ys) (support zs)
  sup-is-strict-order .is-strict-order.has-prop {xs} {ys} = inf<-is-prop (support xs) (support ys)

  merge-is-displacement-algebra : is-displacement-algebra _sup<_ [] merge
  merge-is-displacement-algebra .is-displacement-algebra.has-monoid = merge-is-monoid
  merge-is-displacement-algebra .is-displacement-algebra.has-strict-order = sup-is-strict-order
  merge-is-displacement-algebra .is-displacement-algebra.left-invariant {xs} {ys} {zs} ys<zs =
    subst (λ ϕ → ϕ inf< support (merge xs zs)) (sym (merge-sound xs ys)) $
    subst (λ ϕ → (support xs ⊗∞ support ys) inf< ϕ) (sym (merge-sound xs zs)) $
    ⊗∞-left-invariant (support xs) (support ys) (support zs) ys<zs

FiniteSupport : ∀ {o r} → DisplacementAlgebra o r → DisplacementAlgebra o (o ⊔ r)
FiniteSupport {o = o} {r = r} 𝒟 = displacement
  where
    open FinSupport 𝒟

    displacement : DisplacementAlgebra o (o ⊔ r)
    ⌞ displacement ⌟ = Support
    displacement .structure .DisplacementAlgebra-on._<_ = _sup<_
    displacement .structure .DisplacementAlgebra-on.ε = []
    displacement .structure .DisplacementAlgebra-on._⊗_ = merge
    displacement .structure .DisplacementAlgebra-on.has-displacement-algebra = merge-is-displacement-algebra
    ⌞ displacement ⌟-set = Support-is-set
