module Mugen.Algebra.Displacement.NearlyConstant where

open import 1Lab.Reflection.Record

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude

open import Mugen.Axioms.WLPO
open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Coimage
open import Mugen.Algebra.Displacement.InfiniteProduct
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

open import Mugen.Data.List

--------------------------------------------------------------------------------
-- Nearly Constant Functions
-- Section 3.3.5
--
-- A "nearly constant function" is some function 'f : Nat → 𝒟'
-- that differs from some fixed 'd : 𝒟' for only a finite set of 'n : Nat'
--
-- We represent these via prefix lists. IE: the function
--
-- > λ n → if n = 1 then 2 else if n = 3 then 1 else 5
--
-- will be represented as a pair (5, [5,2,5,3]). We will call the
-- first element of this pair "the base" of the function, and the
-- prefix list "the support".
--
-- However, there is a slight problem here when we go to show that
-- this is a subalgebra of 'InfProd': it's not injective! The problem
-- occurs when you have trailing base elements, meaning 2 lists can
-- denote the same function!
--
-- To resolve this, we say that a list is compact relative
-- to some 'base : 𝒟' if it does not have any trailing base's.
-- We then only work with compact lists in our displacement algebra.

module NearlyConst
  {o r}
  (𝒟 : Displacement-algebra o r)
  (let module 𝒟 = Displacement-algebra 𝒟)
  (cmp : ∀ x y → Tri 𝒟._<_ x y) where

  private
    open 𝒟 using (ε; _⊗_; _<_; _≤_)
    open Inf 𝒟

    instance
      HLevel-< : ∀ {x y} {n} → H-Level (x < y) (suc n)
      HLevel-< = prop-instance 𝒟.<-thin

      HLevel-≤ : ∀ {x y} {n} → H-Level (x ≤ y) (suc n)
      HLevel-≤ = prop-instance 𝒟.≤-thin

  _≡?_ : Discrete ⌞ 𝒟 ⌟
  x ≡? y =
    tri-elim
      (λ _ → Dec (x ≡ y))
      (λ x<y → no λ x≡y → 𝒟.<→≠ x<y x≡y)
      yes
      (λ y<x → no λ x≡y → 𝒟.<→≠ y<x (sym x≡y))
      (cmp x y)

  --------------------------------------------------------------------------------
  -- Indexing
  --
  -- This is how we turn a (support) list into a map 'Nat → ⌞ 𝒟 ⌟'.

  index : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → Nat → ⌞ 𝒟 ⌟
  index base [] n = base
  index base (x ∷ xs) zero = x
  index base (x ∷ xs) (suc n) = index base xs n

  --------------------------------------------------------------------------------
  -- Compactness Predicate and Normalization
  --
  -- A list is compact relative to the base if it has
  -- no trailing base's.
  --

  module _ (base :  ⌞ 𝒟 ⌟) where
    is-compact : List ⌞ 𝒟 ⌟ → Type o
    is-compact [] = Lift o ⊤
    is-compact (x ∷ []) = ¬ (x ≡ base)
    is-compact (_ ∷ y ∷ ys) = is-compact (y ∷ ys)

    -- A singleton list consisting of only 'base' is not compact.
    base-singleton-isnt-compact : ∀ {x xs} → x ≡ base → xs ≡ [] → is-compact (x ∷ xs) → ⊥
    base-singleton-isnt-compact {xs = []} x=base xs=[] is-compact = is-compact x=base
    base-singleton-isnt-compact {xs = _ ∷ _} x=base xs=[] is-compact = ∷≠[] xs=[]

    is-compact-tail : ∀ x xs → is-compact (x ∷ xs) → is-compact xs
    is-compact-tail x [] _ = lift tt
    is-compact-tail x (y ∷ ys) compact = compact

    is-compact-is-prop : ∀ xs → is-prop (is-compact xs)
    is-compact-is-prop [] = hlevel 1
    is-compact-is-prop (_ ∷ []) = hlevel 1
    is-compact-is-prop (_ ∷ y ∷ ys) = is-compact-is-prop (y ∷ ys)

    --------------------------------------------------------------------------------
    -- Compacting Lists
    --
    -- Now that we've defined a notion of normal form via
    -- 'is-compact', we want to define a normalization function that
    -- strips off all the trailing 'base' elements.

    compact-step : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟
    compact-step x [] with x ≡? base
    ... | yes _ = []
    ... | no _ = x ∷ []
    compact-step x (y ∷ ys) = x ∷ y ∷ ys

    compact : List ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟
    compact [] = []
    compact (x ∷ xs) = compact-step x (compact xs)

    compact-compacted : ∀ xs → is-compact xs → compact xs ≡ xs
    compact-compacted [] _ = refl
    compact-compacted (x ∷ []) x≠base with x ≡? base
    ... | yes x=base = absurd (x≠base x=base)
    ... | no _ = refl
    compact-compacted (x ∷ y ∷ ys) is-compact =
      ap (compact-step x) $ compact-compacted (y ∷ ys) is-compact

    compact-step-is-compact : ∀ x xs
      → is-compact xs
      → is-compact (compact-step x xs)
    compact-step-is-compact x [] _ with x ≡? base
    ... | yes _ = lift tt
    ... | no x≠base = x≠base
    compact-step-is-compact x (y ∷ ys) is-compact = is-compact

    compact-is-compact : ∀ xs → is-compact (compact xs)
    compact-is-compact [] = lift tt
    compact-is-compact (x ∷ xs) =
      compact-step-is-compact x (compact xs) (compact-is-compact xs)

    base→compact=[] : ∀ {x} → x ≡ base → compact (x ∷ []) ≡ []
    base→compact=[] {x} x=base with x ≡? base
    ... | yes _ = refl
    ... | no x≠base = absurd (x≠base x=base)

{-
    compact-last : ∀ xs ys y → compact xs ≡ ys #r y → y ≡ base → ⊥
    compact-last [] ys y p y=base = #r≠[] (sym p)
    compact-last (xs #r x) ys y p y=base with x ≡? base
    ... | yes x=base = compact-last xs ys y p y=base
    ... | no x≠base = x≠base (#r-last-inj p ∙ y=base)
-}

    --------------------------------------------------------------------------------
    -- Vanishing Lists
    --
    -- We say a list vanishes relative to some 'base' if it /only/ contains 'base'.
    -- Furthermore, we say a /backward/ list compacts relative to some base if
    -- it's compaction is equal to [].
    --
    -- These conditions may seems somewhat redundant. Why not define one as
    -- primary, and the reversed version with fwd/bwd? Indeed, both conditions
    -- are equivalent! However, the induction orders are different, and we want
    -- to *trust the natural recursion*.


{-
    vanish-step : ∀ x xs → x ≡ base → vanishes xs → vanishes (x ∷ xs)
    vanish-step x xs base! vanish = base! , vanish

    vanish-++ : ∀ xs ys → vanishes (xs ++ ys) → vanishes ys
    vanish-++ [] ys vanish = vanish
    vanish-++ (x ∷ xs) ys (_ , vanish) = vanish-++ xs ys vanish

    compacts-head-∷ : ∀ x xs → compact (bwd (x ∷ xs)) ≡ [] → x ≡ base
    compacts-head-∷ x xs compacts =
      vanish-head-∷ x xs $
      subst vanishes (fwd-bwd (x ∷ xs)) $
      vanishes-fwd (bwd (x ∷ xs)) compacts

    compacts-tail-∷ : ∀ x xs → compact (bwd (x ∷ xs)) ≡ [] → compact (bwd xs) ≡ []
    compacts-tail-∷ x xs compacts =
      compacts-bwd xs $
      vanish-tail-∷ x xs $
      subst vanishes (fwd-bwd (x ∷ xs)) $
      vanishes-fwd (bwd (x ∷ xs)) compacts

    compact-vanishr-++r : ∀ xs ys → compact ys ≡ [] → compact (xs ++r ys) ≡ compact xs
    compact-vanishr-++r xs [] ys-vanish = refl
    compact-vanishr-++r xs (ys #r y) ys-vanish with y ≡? base
    ... | yes _ = compact-vanishr-++r xs ys ys-vanish
    ... | no _ = absurd $ #r≠[] ys-vanish

    compact-++r : ∀ xs ys zs → compact ys ≡ compact zs → compact (xs ++r ys) ≡ compact (xs ++r zs)
    compact-++r xs [] [] p =
      refl
    compact-++r xs [] (zs #r z) p =
      sym (compact-vanishr-++r xs (zs #r z) (sym p))
    compact-++r xs (ys #r y) [] p =
      compact-vanishr-++r xs (ys #r y) p
    compact-++r xs (ys #r y) (zs #r z) =
      -- Cannot be done using with-abstraction /or/ a helper function because the termination
      -- checker gets confused.
      -- Ouch.
      Dec-elim (λ p → from-maybe ys p ≡ compact (zs #r z) → from-maybe (xs ++r ys) p ≡ compact (xs ++r (zs #r z)))
        (λ y-base! →
          Dec-elim (λ p → compact ys ≡ from-maybe zs p → compact (xs ++r ys) ≡ from-maybe (xs ++r zs) p)
            (λ z-base! p → compact-++r xs ys zs p)
            (λ ¬z-base p → compact-++r xs ys (zs #r z) (p ∙ sym (compact-done zs ¬z-base)) ∙ compact-done (xs ++r zs) ¬z-base)
            (z ≡? base))
        (λ ¬y-base →
          Dec-elim (λ p → ys #r y ≡ from-maybe zs p → (xs ++r ys) #r y ≡ from-maybe (xs ++r zs) p)
            (λ z-base! p → sym (compact-done ((xs ++r ys)) ¬y-base) ∙ compact-++r xs (ys #r y) zs (compact-done ys ¬y-base ∙ p))
            (λ ¬z-base p → ap (xs ++r_) p)
            (z ≡? base))
        (y ≡? base)

    compact-◁⊗ : ∀ xs ys zs → compact (bwd ys) ≡ compact (bwd zs) → compact (xs ◁⊗ ys) ≡ compact (xs ◁⊗ zs)
    compact-◁⊗ xs ys zs p =
      compact (xs ◁⊗ ys)      ≡⟨ ap compact (◁⊗-bwd xs ys) ⟩
      compact (xs ++r bwd ys) ≡⟨ compact-++r xs (bwd ys) (bwd zs) p ⟩
      compact (xs ++r bwd zs) ≡˘⟨ ap compact (◁⊗-bwd xs zs) ⟩
      compact (xs ◁⊗ zs) ∎

    compact-◁⊗-¬base : ∀ xs ys {x} → (x ≡ base → ⊥) → compact ((xs #r x) ◁⊗ ys) ≡ (xs #r x) ++r compact (bwd ys)
    compact-◁⊗-¬base xs ys {x = x} x≠base with inspect (compact (bwd ys))
    ... | [] , p =
      compact ((xs #r x) ◁⊗ ys) ≡⟨ compact-◁⊗ (xs #r x) ys [] p ⟩
      compact ((xs #r x))       ≡⟨ compact-done xs x≠base ⟩
      xs #r x                   ≡˘⟨ ap ((xs #r x) ++r_) p ⟩
      (xs #r x) ++r compact (bwd ys) ∎
    ... | cs #r c , p =
      compact ((xs #r x) ◁⊗ ys)                   ≡⟨ compact-◁⊗ (xs #r x) ys (fwd (cs #r c)) (p ∙ sym cs#rc-compact ∙ sym (ap compact (bwd-fwd (cs #r c)))) ⟩
      compact ((xs #r x) ◁⊗ fwd (cs #r c))        ≡⟨ ap compact (◁⊗-bwd (xs #r x) (fwd (cs #r c))) ⟩
      compact ((xs #r x) ++r bwd (fwd (cs #r c))) ≡⟨ ap (λ ϕ → compact ((xs #r x) ++r ϕ)) (bwd-fwd (cs #r c)) ⟩
      compact ((xs #r x) ++r (cs #r c))           ≡⟨ compact-done ((xs #r x) ++r cs) c≠base ⟩
      (xs #r x) ++r (cs #r c)                     ≡˘⟨ ap ((xs #r x) ++r_) p ⟩
      (xs #r x) ++r compact (bwd ys) ∎
      where
        c≠base : c ≡ base → ⊥
        c≠base = compact-last (bwd ys) cs c p

        cs#rc-compact : compact (cs #r c) ≡ cs #r c
        cs#rc-compact = compact-done cs c≠base
-}

    --------------------------------------------------------------------------------
    -- Indexing
    --
    -- This is how we embed a support list into a map 'Nat → ⌞ 𝒟 ⌟'.

    index-compact-step-zero : ∀ x xs
      → index base (compact-step x xs) zero ≡ x
    index-compact-step-zero x [] with x ≡? base
    ... | yes x=base = sym x=base
    ... | no _ = refl
    index-compact-step-zero x (_ ∷ _) = refl

    index-compact-step-suc : ∀ x xs n
      → index base (compact-step x xs) (suc n) ≡ index base xs n
    index-compact-step-suc x [] n with x ≡? base
    ... | yes _ = refl
    ... | no _ = refl
    index-compact-step-suc x (_ ∷ _) n = refl

    -- Indexing a compacted list is the same as indexing the uncompacted list.
    index-compact : ∀ xs n → index base (compact xs) n ≡ index base xs n
    index-compact [] n = refl
    index-compact (x ∷ xs) zero =
      index-compact-step-zero x (compact xs)
    index-compact (x ∷ xs) (suc n) =
      index base (compact-step x (compact xs)) (suc n)
        ≡⟨ index-compact-step-suc x (compact xs) n ⟩
      index base (compact xs) n
        ≡⟨ index-compact xs n ⟩
      index base xs n
        ∎

  --------------------------------------------------------------------------------
  -- Merging Lists
  --
  -- We start by defining how to merge two lists without performing
  -- compaction.

  merge-with : (⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟) → ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟
  merge-with _⊚_ b1 [] b2 [] = []
  merge-with _⊚_ b1 [] b2 (y ∷ ys) = (b1 ⊚ y) ∷ merge-with _⊚_ b1 [] b2 ys
  merge-with _⊚_ b1 (x ∷ xs) b2 [] = (x ⊚ b2) ∷ merge-with _⊚_ b1 xs b2 []
  merge-with _⊚_ b1 (x ∷ xs) b2 (y ∷ ys) = (x ⊚ y) ∷ merge-with _⊚_ b1 xs b2 ys

  merge-list : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟
  merge-list = merge-with _⊗_

  merge-list-idl : ∀ b2 ys → merge-list ε [] b2 ys ≡ ys
  merge-list-idl b2 [] = refl
  merge-list-idl b2 (y ∷ ys) = ap₂ _∷_ 𝒟.idl (merge-list-idl b2 ys)

  merge-list-idr : ∀ b1 xs → merge-list b1 xs ε [] ≡ xs
  merge-list-idr b1 [] = refl
  merge-list-idr b1 (x ∷ xs) = ap₂ _∷_ 𝒟.idr (merge-list-idr b1 xs)

  merge-list-assoc : ∀ b1 xs b2 ys b3 zs
    → merge-list b1 xs (b2 ⊗ b3) (merge-list b2 ys b3 zs)
    ≡ merge-list (b1 ⊗ b2) (merge-list b1 xs b2 ys) b3 zs
  merge-list-assoc b1 [] b2 [] b3 [] =
    refl
  merge-list-assoc b1 [] b2 [] b3 (z ∷ zs) =
    ap₂ _∷_ 𝒟.associative (merge-list-assoc b1 [] b2 [] b3 zs)
  merge-list-assoc b1 [] b2 (y ∷ ys) b3 [] =
    ap₂ _∷_ 𝒟.associative (merge-list-assoc b1 [] b2 ys b3 [])
  merge-list-assoc b1 [] b2 (y ∷ ys) b3 (z ∷ zs) =
    ap₂ _∷_ 𝒟.associative (merge-list-assoc b1 [] b2 ys b3 zs)
  merge-list-assoc b1 (x ∷ xs) b2 [] b3 [] =
    ap₂ _∷_ 𝒟.associative (merge-list-assoc b1 xs b2 [] b3 [])
  merge-list-assoc b1 (x ∷ xs) b2 [] b3 (z ∷ zs) =
    ap₂ _∷_ 𝒟.associative (merge-list-assoc b1 xs b2 [] b3 zs)
  merge-list-assoc b1 (x ∷ xs) b2 (y ∷ ys) b3 [] =
    ap₂ _∷_ 𝒟.associative (merge-list-assoc b1 xs b2 ys b3 [])
  merge-list-assoc b1 (x ∷ xs) b2 (y ∷ ys) b3 (z ∷ zs) =
    ap₂ _∷_ 𝒟.associative (merge-list-assoc b1 xs b2 ys b3 zs)

  --------------------------------------------------------------------------------
  -- Misc. Merging Lemmas

  compact-merge-basel : ∀ b1 x b2 ys → x ≡ b1
    → compact (b1 ⊗ b2) (merge-list b1 (x ∷ []) b2 ys)
    ≡ compact (b1 ⊗ b2) (merge-list b1 [] b2 ys)
  compact-merge-basel b1 x b2 [] x=b1 =
    base→compact=[] (b1 ⊗ b2) (ap (_⊗ b2) x=b1)
  compact-merge-basel b1 x b2 (y ∷ ys) x=b1 =
    ap (λ x → compact (b1 ⊗ b2) ((x ⊗ y) ∷ merge-list b1 [] b2 ys)) x=b1

  compact-merge-stepl : ∀ b1 x xs b2 ys
    → compact (b1 ⊗ b2) (merge-list b1 (compact-step b1 x xs) b2 ys)
    ≡ compact (b1 ⊗ b2) (merge-list b1 (x ∷ xs) b2 ys)
  compact-merge-stepl b1 x [] b2 ys with x ≡? b1
  ... | no x≠b1 = refl
  ... | yes x=b1 = sym $ compact-merge-basel b1 x b2 ys x=b1
  compact-merge-stepl b1 x (_ ∷ _) b2 ys = refl

  compact-merge-compactl : ∀ b1 xs b2 ys
    → compact (b1 ⊗ b2) (merge-list b1 (compact b1 xs) b2 ys)
    ≡ compact (b1 ⊗ b2) (merge-list b1 xs b2 ys)
  compact-merge-compactl b1 [] b2 ys = refl
  compact-merge-compactl b1 (x ∷ xs) b2 [] =
    compact (b1 ⊗ b2) (merge-list b1 (compact-step b1 x (compact b1 xs)) b2 [])
      ≡⟨ compact-merge-stepl b1 x (compact b1 xs) b2 [] ⟩
    compact-step (b1 ⊗ b2) (x ⊗ b2) (compact (b1 ⊗ b2) (merge-list b1 (compact b1 xs) b2 []))
      ≡⟨ ap (compact-step (b1 ⊗ b2) (x ⊗ b2)) $ compact-merge-compactl b1 xs b2 [] ⟩
    compact-step (b1 ⊗ b2) (x ⊗ b2) (compact (b1 ⊗ b2) (merge-list b1 xs b2 []))
      ∎
  compact-merge-compactl b1 (x ∷ xs) b2 (y ∷ ys) =
    compact (b1 ⊗ b2) (merge-list b1 (compact-step b1 x (compact b1 xs)) b2 (y ∷ ys))
      ≡⟨ compact-merge-stepl b1 x (compact b1 xs) b2 (y ∷ ys) ⟩
    compact-step (b1 ⊗ b2) (x ⊗ y) (compact (b1 ⊗ b2) (merge-list b1 (compact b1 xs) b2 ys))
      ≡⟨ ap (compact-step (b1 ⊗ b2) (x ⊗ y)) $ compact-merge-compactl b1 xs b2 ys ⟩
    compact-step (b1 ⊗ b2) (x ⊗ y) (compact (b1 ⊗ b2) (merge-list b1 xs b2 ys))
      ∎

  compact-merge-baser : ∀ b1 xs b2 y → y ≡ b2
    → compact (b1 ⊗ b2) (merge-list b1 xs b2 (y ∷ []))
    ≡ compact (b1 ⊗ b2) (merge-list b1 xs b2 [])
  compact-merge-baser b1 [] b2 y y=b2 =
    base→compact=[] (b1 ⊗ b2) (ap (b1 ⊗_) y=b2)
  compact-merge-baser b1 (x ∷ xs) b2 y y=b2 =
    ap (λ y → compact (b1 ⊗ b2) ((x ⊗ y) ∷ merge-list b1 xs b2 [])) y=b2

  compact-merge-stepr : ∀ b1 xs b2 y ys
    → compact (b1 ⊗ b2) (merge-list b1 xs b2 (compact-step b2 y ys))
    ≡ compact (b1 ⊗ b2) (merge-list b1 xs b2 (y ∷ ys))
  compact-merge-stepr b1 xs b2 y [] with y ≡? b2
  ... | no y≠b2 = refl
  ... | yes y=b2 = sym $ compact-merge-baser b1 xs b2 y y=b2
  compact-merge-stepr b1 xs b2 y (_ ∷ _) = refl

  compact-merge-compactr : ∀ b1 xs b2 ys
    → compact (b1 ⊗ b2) (merge-list b1 xs b2 (compact b2 ys))
    ≡ compact (b1 ⊗ b2) (merge-list b1 xs b2 ys)
  compact-merge-compactr b1 xs b2 [] = refl
  compact-merge-compactr b1 [] b2 (y ∷ ys) =
    compact (b1 ⊗ b2) (merge-list b1 [] b2 (compact-step b2 y (compact b2 ys)))
      ≡⟨ compact-merge-stepr b1 [] b2 y (compact b2 ys) ⟩
    compact-step (b1 ⊗ b2) (b1 ⊗ y) (compact (b1 ⊗ b2) (merge-list b1 [] b2 (compact b2 ys)))
      ≡⟨ ap (compact-step (b1 ⊗ b2) (b1 ⊗ y)) $ compact-merge-compactr b1 [] b2 ys ⟩
    compact-step (b1 ⊗ b2) (b1 ⊗ y) (compact (b1 ⊗ b2) (merge-list b1 [] b2 ys))
      ∎
  compact-merge-compactr b1 (x ∷ xs) b2 (y ∷ ys) =
    compact (b1 ⊗ b2) (merge-list b1 (x ∷ xs) b2 (compact-step b2 y (compact b2 ys)))
      ≡⟨ compact-merge-stepr b1 (x ∷ xs) b2 y (compact b2 ys) ⟩
    compact-step (b1 ⊗ b2) (x ⊗ y) (compact (b1 ⊗ b2) (merge-list b1 xs b2 (compact b2 ys)))
      ≡⟨ ap (compact-step (b1 ⊗ b2) (x ⊗ y)) $ compact-merge-compactr b1 xs b2 ys ⟩
    compact-step (b1 ⊗ b2) (x ⊗ y) (compact (b1 ⊗ b2) (merge-list b1 xs b2 ys))
      ∎

  --------------------------------------------------------------------------------
  -- Compact Support Lists
  --
  -- These will be the actual elements of our displacement algebra.
  -- A SupportList consists of a choice of base, and a compact list
  -- relative to that base.

  record SupportList : Type o where
    constructor support-list
    no-eta-equality
    field
      base : ⌞ 𝒟 ⌟
      elts : List ⌞ 𝒟 ⌟
      compacted : is-compact base elts

  open SupportList

  -- Paths in support lists are determined by paths between the bases + paths between the elements.
  support-list-path : ∀ {xs ys : SupportList} → xs .base ≡ ys .base → xs .elts ≡ ys .elts → xs ≡ ys
  support-list-path p q i .base = p i
  support-list-path p q i .elts = q i
  support-list-path {xs = xs} {ys = ys} p q i .compacted =
    is-prop→pathp (λ i → is-compact-is-prop (p i) (q i)) (xs .compacted) (ys .compacted) i

  private unquoteDecl eqv = declare-record-iso eqv (quote SupportList)

  SupportList-is-set : is-set SupportList
  SupportList-is-set =
    is-hlevel≃ 2 (Iso→Equiv eqv) $
      Σ-is-hlevel 2 (hlevel 2) λ base →
      Σ-is-hlevel 2 (ListPath.List-is-hlevel 0 𝒟.has-is-set) λ xs →
      is-prop→is-set (is-compact-is-prop base xs)

  -- Smart constructor for SupportList that compacts the list.
  compact-support : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → SupportList
  compact-support base xs .SupportList.base = base
  compact-support base xs .SupportList.elts = compact base xs
  compact-support base xs .SupportList.compacted = compact-is-compact base xs

  -- This is a common goal, so we define some shorthand.
  merge-support : SupportList → SupportList → List ⌞ 𝒟 ⌟
  merge-support xs ys = merge-list (xs .base) (xs .elts) (ys .base) (ys .elts)
  {-# INLINE merge-support #-}

  -- Lifting of 'merge-list' to SupportLists.
  merge : SupportList → SupportList → SupportList
  merge xs ys .SupportList.base = xs .base ⊗ ys .base
  merge xs ys .SupportList.elts = compact (xs .base ⊗ ys .base) (merge-support xs ys)
  merge xs ys .SupportList.compacted = compact-is-compact (xs .base ⊗ ys .base) (merge-support xs ys)

  -- The empty SupportList.
  empty : SupportList
  empty .base = ε
  empty .elts = []
  empty .compacted = lift tt

  -- Compacting a support lists elements does nothing
  elts-compact : ∀ xs → compact (xs .base) (xs .elts) ≡ xs .elts
  elts-compact xs = compact-compacted (xs .base) (xs .elts) (xs .compacted)

  -- 'index' for 'SupportList'
  into : SupportList → Nat → ⌞ 𝒟 ⌟
  into xs n = index (xs .base) (xs .elts) n

  --------------------------------------------------------------------------------
  -- Properties of Merge + SupportLists
  --
  -- Identity and associativity of 'merge-list' lifts to
  -- 'merge'. However, we need to do some shuffling about
  -- of the various 'compact' calls. Thankfully we already
  -- proved all the compaction lemmas!

  -- Lifting of 'merge-list-idl' to support lists.
  merge-idl : ∀ xs → merge empty xs ≡ xs
  merge-idl xs = support-list-path 𝒟.idl $
    compact (ε ⊗ xs .base) (merge-list ε [] (xs .base) (xs .elts))
      ≡⟨ ap₂ compact 𝒟.idl (merge-list-idl (xs .base) (xs .elts)) ⟩
    compact (xs .base) (xs .elts)
      ≡⟨ elts-compact xs ⟩
    xs .elts ∎

  -- Lifting of 'merge-list-idr' to support lists.
  merge-idr : ∀ xs → merge xs empty ≡ xs
  merge-idr xs = support-list-path 𝒟.idr $
    compact (xs .base ⊗ ε) (merge-list (xs .base) (xs .elts) ε [])
      ≡⟨ ap₂ compact 𝒟.idr (merge-list-idr (xs .base) (xs .elts)) ⟩
    compact (xs .base) (xs .elts)
      ≡⟨ elts-compact xs ⟩
    xs .elts ∎

  -- Lifting of 'merge-assoc' to support lists.
  merge-assoc : ∀ xs ys zs → merge xs (merge ys zs) ≡ merge (merge xs ys) zs
  merge-assoc xs ys zs = support-list-path 𝒟.associative $
    compact (xs .base ⊗ (ys .base ⊗ zs .base)) (merge-support xs (compact-support _ (merge-support ys zs)))
      ≡⟨ compact-merge-compactr _ (xs .elts) _ (merge-support ys zs) ⟩
    compact (xs .base ⊗ (ys .base ⊗ zs .base)) (merge-list _ (xs .elts) _ (merge-support ys zs))
      ≡⟨ ap₂ compact 𝒟.associative (merge-list-assoc _ (xs .elts) _ (ys .elts) _ (zs .elts)) ⟩
    compact ((xs .base ⊗ ys .base) ⊗ zs .base) (merge-list _ (merge-support xs ys) _ (zs .elts))
      ≡˘⟨ compact-merge-compactl _ (merge-support xs ys) _ (zs .elts) ⟩
    compact ((xs .base ⊗ ys .base) ⊗ zs .base) (merge-support (compact-support _ (merge-support xs ys)) zs)
      ∎

  --------------------------------------------------------------------------------
  -- Order

  -- FIXME: reuse inf<

  module _ (b1 : ⌞ 𝒟 ⌟) (xs : List ⌞ 𝒟 ⌟) (b2 : ⌞ 𝒟 ⌟) (ys : List ⌞ 𝒟 ⌟) where
    -- ≤ for lists relative to a base.
    list≤ : Type (o ⊔ r)
    list≤ = ∀ (n : Nat) → index b1 xs n ≤ index b2 ys n

    -- = for lists relative to a base.
    list= : Type o
    list= = ∀ (n : Nat) → index b1 xs n ≡ index b2 ys n

    -- < for lists relative to a base.
    list< : Type (o ⊔ r)
    list< = list≤ × (¬ list=)

    -- We can transform a proof of < into a proof of ≤.
    list<→≤ : list< → list≤
    list<→≤ (xs≤ys , _) = xs≤ys

    list≤-is-prop : is-prop list≤
    list≤-is-prop = hlevel 1

    list<-is-prop : is-prop list<
    list<-is-prop = hlevel 1

  --------------------------------------------------------------------------------
  -- Misc. Lemmas about ≤ and <

  base<→list< : ∀ b1 xs b2 ys → xs ≡ ys → b1 < b2 → list< b1 xs b2 ys
  base<→list< b1 [] b2 [] xs=ys b1<b2 = (λ n → inr b1<b2) , (λ p → 𝒟.<→≠ b1<b2 (p 0))
  base<→list< b1 [] b2 (_ ∷ _) xs=ys b1<b2 = absurd $ ∷≠[] (sym xs=ys)
  base<→list< b1 (_ ∷ _) b2 [] xs=ys b1<b2 = absurd $ ∷≠[] xs=ys
  base<→list< b1 (x ∷ xs) b2 (y ∷ ys) x∷xs=y∷ys b1<b2 =
    let xs≤ys , xs≠ys = base<→list< b1 xs b2 ys (∷-tail-inj x∷xs=y∷ys) b1<b2 in
    (λ { zero → inl (∷-head-inj x∷xs=y∷ys)
       ; (suc n) → xs≤ys n }) ,
    (λ xs=ys → xs≠ys (xs=ys ⊙ suc))

  list≤→base≤ : ∀ b1 xs b2 ys → list≤ b1 xs b2 ys → b1 ≤ b2
  list≤→base≤ b1 [] b2 [] []≤[] = []≤[] 0
  list≤→base≤ b1 [] b2 (y ∷ ys) []≤y∷ys = list≤→base≤ b1 [] b2 ys ([]≤y∷ys ⊙ suc)
  list≤→base≤ b1 (x ∷ xs) b2 [] x∷xs≤[] = list≤→base≤ b1 xs b2 [] (x∷xs≤[] ⊙ suc)
  list≤→base≤ b1 (x ∷ xs) b2 (y ∷ ys) x∷xs≤y∷ys = list≤→base≤ b1 xs b2 ys (x∷xs≤y∷ys ⊙ suc)

  list=? : ∀ b1 xs b2 ys → Dec (list= b1 xs b2 ys)
  list=? b1 [] b2 [] with b1 ≡? b2
  ... | yes b1=b2 = yes λ n → b1=b2
  ... | no b1≠b2 = no λ p → b1≠b2 (p 0)
  list=? b1 (x ∷ xs) b2 [] with x ≡? b2
  ... | no x≠b2 = no λ p → x≠b2 (p 0)
  ... | yes x=b2 with list=? b1 xs b2 []
  ...   | no xs≠[] = no λ p → xs≠[] (p ⊙ suc)
  ...   | yes xs=[] = yes λ { zero → x=b2; (suc n) → xs=[] n }
  list=? b1 [] b2 (y ∷ ys) with b1 ≡? y
  ... | no b1≠y = no λ p → b1≠y (p 0)
  ... | yes b1=y with list=? b1 [] b2 ys
  ...   | no []≠ys = no λ p → []≠ys (p ⊙ suc)
  ...   | yes []=ys = yes λ { zero → b1=y; (suc n) → []=ys n }
  list=? b1 (x ∷ xs) b2 (y ∷ ys) with x ≡? y
  ... | no x≠y = no λ p → x≠y (p 0)
  ... | yes x=y with list=? b1 xs b2 ys
  ...   | no xs≠ys = no λ p → xs≠ys (p ⊙ suc)
  ...   | yes xs=ys = yes λ { zero → x=y; (suc n) → xs=ys n }

  compact-index-inj : ∀ b1 xs b2 ys
    → is-compact b1 xs
    → is-compact b2 ys
    → list= b1 xs b2 ys
    → (b1 ≡ b2) × (xs ≡ ys)
  compact-index-inj b1 [] b2 [] _ _ p =
    p 0 , refl
  compact-index-inj b1 (x ∷ xs) b2 [] x∷xs-compact []-compact p =
    let xs-compact = is-compact-tail b1 x xs x∷xs-compact in
    let b1=b2 , xs=[] = compact-index-inj b1 xs b2 [] xs-compact []-compact (p ⊙ suc) in
    absurd $ base-singleton-isnt-compact b1 (p 0 ∙ sym b1=b2) xs=[] x∷xs-compact
  compact-index-inj b1 [] b2 (y ∷ ys) []-compact y∷ys-compact p =
    let ys-compact = is-compact-tail b2 y ys y∷ys-compact in
    let b1=b2 , []=ys = compact-index-inj b1 [] b2 ys []-compact ys-compact (p ⊙ suc) in
    absurd $ base-singleton-isnt-compact b2 (sym (p 0) ∙ b1=b2) (sym []=ys) y∷ys-compact
  compact-index-inj b1 (x ∷ xs) b2 (y ∷ ys) x∷xs-compact y∷ys-compact p =
    let xs-compact = is-compact-tail b1 x xs x∷xs-compact in
    let ys-compact = is-compact-tail b2 y ys y∷ys-compact in
    let b1=b2 , xs=ys = compact-index-inj b1 xs b2 ys xs-compact ys-compact (p ⊙ suc) in
    b1=b2 , ap₂ _∷_ (p 0) xs=ys

  --------------------------------------------------------------------------------
  -- Order Structure for ≤ and <
  --
  -- Lots of big case bashes here! This is all super mechanical,
  -- and just involves getting things to compute.

  list≤-refl : ∀ b xs → list≤ b xs b xs
  list≤-refl b xs n = inl refl

  list<-irrefl : ∀ b xs → list< b xs b xs → ⊥
  list<-irrefl b xs (_ , xs≠xs) = xs≠xs λ _ → refl

  list≤-trans : ∀ b1 xs b2 ys b3 zs → list≤ b1 xs b2 ys → list≤ b2 ys b3 zs → list≤ b1 xs b3 zs
  list≤-trans b1 xs b2 ys b3 zs xs≤ys ys≤zs n = 𝒟.≤-trans (xs≤ys n) (ys≤zs n)

  list≤-transr : ∀ b1 xs b2 ys b3 zs → list< b1 xs b2 ys → list≤ b2 ys b3 zs → list< b1 xs b3 zs
  list≤-transr b1 xs b2 ys b3 zs (xs≤ys , xs≠ys) ys≤zs =
    list≤-trans b1 xs b2 ys b3 zs xs≤ys ys≤zs ,
    (λ xs=zs → xs≠ys λ n → 𝒟.≤-antisym (xs≤ys n) $ subst (_ ≤_) (sym $ xs=zs n) (ys≤zs n))

  list≤-transl : ∀ b1 xs b2 ys b3 zs → list≤ b1 xs b2 ys → list< b2 ys b3 zs → list< b1 xs b3 zs
  list≤-transl b1 xs b2 ys b3 zs xs≤ys (ys≤zs , ys≠zs)=
    list≤-trans b1 xs b2 ys b3 zs xs≤ys ys≤zs ,
    (λ xs=zs → ys≠zs λ n → 𝒟.≤-antisym (ys≤zs n) $ subst (_≤ _) (xs=zs n) (xs≤ys n))

  list<-trans : ∀ b1 xs b2 ys b3 zs → list< b1 xs b2 ys → list< b2 ys b3 zs → list< b1 xs b3 zs
  list<-trans b1 xs b2 ys b3 zs xs<ys ys<zs = list≤-transl b1 xs b2 ys b3 zs (list<→≤ b1 xs b2 ys xs<ys) ys<zs

  --------------------------------------------------------------------------------
  -- Heterogenous Compositions

  _slist<_ : SupportList → SupportList → Type (o ⊔ r)
  xs slist< ys = list< (xs .base) (xs .elts) (ys .base) (ys .elts)

  _slist≤_ : SupportList → SupportList → Type (o ⊔ r)
  xs slist≤ ys = list≤ (xs .base) (xs .elts) (ys .base) (ys .elts)

  --------------------------------------------------------------------------------
  -- Converting between non-strict and the nice ≤

  non-strict→slist≤ : ∀ xs ys → non-strict _slist<_ xs ys → xs slist≤ ys
  non-strict→slist≤ xs ys (inl xs≡ys) n = inl $ ap (λ xs → index (base xs) (elts xs) n) xs≡ys
  non-strict→slist≤ xs ys (inr xs<ys) = list<→≤ (base xs) (elts xs) (base ys) (elts ys) xs<ys

  into-inj : ∀ xs ys → list= (xs .base) (xs .elts) (ys .base) (ys .elts) → xs ≡ ys
  into-inj xs ys list= =
    let b1=b2 , xs=ys = compact-index-inj (base xs) (elts xs) (base ys) (elts ys) (compacted xs) (compacted ys) list= in
    support-list-path b1=b2 xs=ys

  slist≤→non-strict : ∀ xs ys → xs slist≤ ys → non-strict _slist<_ xs ys
  slist≤→non-strict xs ys xs≤ys =
    Dec-rec (inl ⊙ into-inj xs ys) (λ list≠ → inr $ xs≤ys , list≠) $
    list=? (base xs) (elts xs) (base ys) (elts ys)

  --------------------------------------------------------------------------------
  -- Compaction + Orderings

  compact-= : ∀ b xs → list= b (compact b xs) b xs
  compact-= = index-compact

  compact-mono-≤ : ∀ b1 xs b2 ys → list≤ b1 xs b2 ys → list≤ b1 (compact b1 xs) b2 (compact b2 ys)
  compact-mono-≤ b1 xs b2 ys xs≤ys n =
    coe1→0 (λ i → index-compact b1 xs n i ≤ index-compact b2 ys n i) (xs≤ys n)

  compact-mono-< : ∀ b1 xs b2 ys → list< b1 xs b2 ys → list< b1 (compact b1 xs) b2 (compact b2 ys)
  compact-mono-< b1 xs b2 ys (xs≤ys , xs≠ys) =
    compact-mono-≤ b1 xs b2 ys xs≤ys ,
    (λ cxs=cys → xs≠ys λ n → sym (compact-= b1 xs n) ∙ cxs=cys n ∙ compact-= b2 ys n)

  --------------------------------------------------------------------------------
  -- Left-Invariance

  list≤-left-invariant : ∀ b1 xs b2 ys b3 zs
    → list≤ b2 ys b3 zs
    → list≤ (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs)
  list≤-left-invariant b1 [] b2 [] b3 [] ys≤zs n = 𝒟.≤-left-invariant (ys≤zs n)
  list≤-left-invariant b1 [] b2 [] b3 (_ ∷ _) ys≤zs zero = 𝒟.≤-left-invariant (ys≤zs zero)
  list≤-left-invariant b1 [] b2 (_ ∷ _) b3 [] ys≤zs zero = 𝒟.≤-left-invariant (ys≤zs zero)
  list≤-left-invariant b1 [] b2 (_ ∷ _) b3 (_ ∷ _) ys≤zs zero = 𝒟.≤-left-invariant (ys≤zs zero)
  list≤-left-invariant b1 (_ ∷ _) b2 [] b3 [] ys≤zs zero = 𝒟.≤-left-invariant (ys≤zs zero)
  list≤-left-invariant b1 (_ ∷ _) b2 [] b3 (_ ∷ _) ys≤zs zero = 𝒟.≤-left-invariant (ys≤zs zero)
  list≤-left-invariant b1 (_ ∷ _) b2 (_ ∷ _) b3 [] ys≤zs zero = 𝒟.≤-left-invariant (ys≤zs zero)
  list≤-left-invariant b1 (_ ∷ _) b2 (_ ∷ _) b3 (_ ∷ _) ys≤zs zero = 𝒟.≤-left-invariant (ys≤zs zero)
  list≤-left-invariant b1 [] b2 [] b3 (_ ∷ zs) ys≤zs (suc n) = list≤-left-invariant b1 [] b2 [] b3 zs (ys≤zs ⊙ suc) n
  list≤-left-invariant b1 [] b2 (_ ∷ ys) b3 [] ys≤zs (suc n) = list≤-left-invariant b1 [] b2 ys b3 [] (ys≤zs ⊙ suc) n
  list≤-left-invariant b1 [] b2 (_ ∷ ys) b3 (_ ∷ zs) ys≤zs (suc n) = list≤-left-invariant b1 [] b2 ys b3 zs (ys≤zs ⊙ suc) n
  list≤-left-invariant b1 (_ ∷ xs) b2 [] b3 [] ys≤zs (suc n) = list≤-left-invariant b1 xs b2 [] b3 [] (ys≤zs ⊙ suc) n
  list≤-left-invariant b1 (_ ∷ xs) b2 [] b3 (_ ∷ zs) ys≤zs (suc n) = list≤-left-invariant b1 xs b2 [] b3 zs (ys≤zs ⊙ suc) n
  list≤-left-invariant b1 (_ ∷ xs) b2 (_ ∷ ys) b3 [] ys≤zs (suc n) = list≤-left-invariant b1 xs b2 ys b3 [] (ys≤zs ⊙ suc) n
  list≤-left-invariant b1 (_ ∷ xs) b2 (_ ∷ ys) b3 (_ ∷ zs) ys≤zs (suc n) = list≤-left-invariant b1 xs b2 ys b3 zs (ys≤zs ⊙ suc) n

  -- FIXME: can do without decidable equality!
  ⊗-injr : ∀ {b1 b2 b3} → (b1 ⊗ b2) ≡ (b1 ⊗ b3) → b2 ≡ b3
  ⊗-injr {b2 = b2} {b3 = b3} b1⊗b2=b1⊗b3 with cmp b2 b3
  ... | lt b2<b3 = absurd $ 𝒟.<→≠ (𝒟.left-invariant b2<b3) b1⊗b2=b1⊗b3
  ... | gt b2>b3 = absurd $ 𝒟.<→≠ (𝒟.left-invariant b2>b3) (sym b1⊗b2=b1⊗b3)
  ... | eq b2=b3 = b2=b3

  merge-list-inj : ∀ b1 xs b2 ys b3 zs
    → list= (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs)
    → list= b2 ys b3 zs
  merge-list-inj b1 [] b2 [] b3 [] p n = ⊗-injr (p n)
  merge-list-inj b1 [] b2 [] b3 (_ ∷ _) p zero = ⊗-injr (p zero)
  merge-list-inj b1 [] b2 (_ ∷ _) b3 [] p zero = ⊗-injr (p zero)
  merge-list-inj b1 [] b2 (_ ∷ _) b3 (_ ∷ _) p zero = ⊗-injr (p zero)
  merge-list-inj b1 (_ ∷ _) b2 [] b3 [] p zero = ⊗-injr (p zero)
  merge-list-inj b1 (_ ∷ _) b2 [] b3 (_ ∷ _) p zero = ⊗-injr (p zero)
  merge-list-inj b1 (_ ∷ _) b2 (_ ∷ _) b3 [] p zero = ⊗-injr (p zero)
  merge-list-inj b1 (_ ∷ _) b2 (_ ∷ _) b3 (_ ∷ _) p zero = ⊗-injr (p zero)
  merge-list-inj b1 [] b2 [] b3 (_ ∷ zs) p (suc n) = merge-list-inj b1 [] b2 [] b3 zs (p ⊙ suc) n
  merge-list-inj b1 [] b2 (_ ∷ ys) b3 [] p (suc n) = merge-list-inj b1 [] b2 ys b3 [] (p ⊙ suc) n
  merge-list-inj b1 [] b2 (_ ∷ ys) b3 (_ ∷ zs) p (suc n) = merge-list-inj b1 [] b2 ys b3 zs (p ⊙ suc) n
  merge-list-inj b1 (_ ∷ xs) b2 [] b3 [] p (suc n) = merge-list-inj b1 xs b2 [] b3 [] (p ⊙ suc) n
  merge-list-inj b1 (_ ∷ xs) b2 [] b3 (_ ∷ zs) p (suc n) = merge-list-inj b1 xs b2 [] b3 zs (p ⊙ suc) n
  merge-list-inj b1 (_ ∷ xs) b2 (_ ∷ ys) b3 [] p (suc n) = merge-list-inj b1 xs b2 ys b3 [] (p ⊙ suc) n
  merge-list-inj b1 (_ ∷ xs) b2 (_ ∷ ys) b3 (_ ∷ zs) p (suc n) = merge-list-inj b1 xs b2 ys b3 zs (p ⊙ suc) n

  list<-left-invariant : ∀ b1 xs b2 ys b3 zs
    → list< b2 ys b3 zs
    → list< (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs)
  list<-left-invariant b1 xs b2 ys b3 zs (ys≤zs , ys≠zs) =
    list≤-left-invariant b1 xs b2 ys b3 zs ys≤zs ,
    (ys≠zs ⊙ merge-list-inj b1 xs b2 ys b3 zs)

  slist<-left-invariant : ∀ xs ys zs → ys slist< zs → (merge xs ys) slist< (merge xs zs)
  slist<-left-invariant xs ys zs ys<zs =
    compact-mono-<
      (xs .base ⊗ ys .base) (merge-list (xs .base) (xs .elts) (ys .base) (ys .elts))
      (xs .base ⊗ zs .base) (merge-list (xs .base) (xs .elts) (zs .base) (zs .elts))
      (list<-left-invariant (xs .base) (xs .elts) (ys .base) (ys .elts) (zs .base) (zs .elts) ys<zs)

  --------------------------------------------------------------------------------
  -- Indexing and Merging

  index-mono : ∀ b1 xs b2 ys → list≤ b1 xs b2 ys → ∀ n → (index b1 xs n) ≤ (index b2 ys n)
  index-mono b1 xs b2 ys xs≤ys = xs≤ys

  index-strictly-mono : ∀ b1 xs b2 ys → list< b1 xs b2 ys → (index b1 xs) inf< (index b2 ys)
  index-strictly-mono b1 xs b2 ys (xs≤ys , xs≠ys) .≤-everywhere = xs≤ys
  index-strictly-mono b1 xs b2 ys (xs≤ys , xs≠ys) .not-equal = xs≠ys

  into-preserves-⊗ : ∀ xs ys n → into (merge xs ys) n ≡ (into xs ⊗∞ into ys) n
  into-preserves-⊗ xs ys n =
    index (xs .base ⊗ ys .base) (compact (xs .base ⊗ ys .base) (merge-list (xs .base) (xs .elts) (ys .base) (ys .elts))) n
      ≡⟨ index-compact (xs .base ⊗ ys .base) (merge-list (xs .base) (xs .elts) (ys .base) (ys .elts)) n ⟩
    index (xs .base ⊗ ys .base) (merge-list (xs .base) (xs .elts) (ys .base) (ys .elts)) n
      ≡⟨ go (xs .base) (xs .elts) (ys .base) (ys .elts) n ⟩
    (into xs ⊗∞ into ys) n
      ∎
    where
      go : ∀ b1 xs b2 ys n → index (b1 ⊗ b2) (merge-list b1 xs b2 ys) n ≡ (index b1 xs ⊗∞ index b2 ys) n
      go b1 [] b2 [] n = refl
      go b1 [] b2 (y ∷ ys) zero = refl
      go b1 [] b2 (y ∷ ys) (suc n) = go b1 [] b2 ys n
      go b1 (x ∷ xs) b2 [] zero = refl
      go b1 (x ∷ xs) b2 [] (suc n) = go b1 xs b2 [] n
      go b1 (x ∷ xs) b2 (y ∷ ys) zero = refl
      go b1 (x ∷ xs) b2 (y ∷ ys) (suc n) = go b1 xs b2 ys n

--------------------------------------------------------------------------------
-- Bundled Instances

module _ {o r} (𝒟 : Displacement-algebra o r) (cmp : ∀ x y → Tri (Displacement-algebra._<_ 𝒟) x y) where
  open NearlyConst 𝒟 cmp
  open SupportList

  NearlyConstant : Displacement-algebra o (o ⊔ r)
  NearlyConstant = to-displacement-algebra mk where
    mk-strict : make-strict-order (o ⊔ r) SupportList
    mk-strict .make-strict-order._<_ = _slist<_
    mk-strict .make-strict-order.<-irrefl {xs} =
      list<-irrefl (xs .base) (xs .elts)
    mk-strict .make-strict-order.<-trans {xs} {ys} {zs} =
      list<-trans (xs .base) (xs .elts) (ys .base) (ys .elts) (zs .base) (zs .elts)
    mk-strict .make-strict-order.<-thin {xs} {ys} =
      list<-is-prop (xs .base) (xs .elts) (ys .base) (ys .elts)
    mk-strict .make-strict-order.has-is-set = SupportList-is-set

    mk : make-displacement-algebra (to-strict-order mk-strict)
    mk .make-displacement-algebra.ε = empty
    mk .make-displacement-algebra._⊗_ = merge
    mk .make-displacement-algebra.idl = merge-idl _
    mk .make-displacement-algebra.idr = merge-idr _
    mk .make-displacement-algebra.associative = merge-assoc _ _ _
    mk .make-displacement-algebra.left-invariant {xs} {ys} {zs} =
      slist<-left-invariant xs ys zs

--------------------------------------------------------------------------------
-- Subalgebra Structure

module _ {o r} {𝒟 : Displacement-algebra o r} (cmp : ∀ x y → Tri (Displacement-algebra._<_ 𝒟) x y) where
  private
    module 𝒟 = Displacement-algebra 𝒟
    open 𝒟 using (ε; _⊗_; _<_; _≤_)
    open NearlyConst 𝒟 cmp
    open Inf 𝒟
    open SupportList

  NearlyConstant⊆InfProd : is-displacement-subalgebra (NearlyConstant 𝒟 cmp) (InfProd 𝒟)
  NearlyConstant⊆InfProd = to-displacement-subalgebra mk where
    mk : make-displacement-subalgebra (NearlyConstant 𝒟 cmp) (InfProd 𝒟)
    mk .make-displacement-subalgebra.into = into
    mk .make-displacement-subalgebra.pres-ε = refl
    mk .make-displacement-subalgebra.pres-⊗ xs ys =
      funext (into-preserves-⊗ xs ys)
    mk .make-displacement-subalgebra.strictly-mono xs ys =
      index-strictly-mono (xs .base) (xs .elts) (ys .base) (ys .elts)
    mk .make-displacement-subalgebra.inj {xs} {ys} p = into-inj xs ys (happly p)

--------------------------------------------------------------------------------
-- Ordered Monoid

module _
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (𝒟-ordered-monoid : has-ordered-monoid 𝒟)
  (cmp : ∀ x y → Tri 𝒟._<_ x y)
  where
  open 𝒟 using (ε; _⊗_; _<_; _≤_)
  open NearlyConst 𝒟 cmp
  open Inf 𝒟
  open is-ordered-monoid 𝒟-ordered-monoid
  open SupportList

  list≤-right-invariant : ∀ b1 xs b2 ys b3 zs
    → list≤ b1 xs b2 ys
    → list≤ (b1 ⊗ b3) (merge-list b1 xs b3 zs) (b2 ⊗ b3) (merge-list b2 ys b3 zs)
  list≤-right-invariant b1 [] b2 [] b3 [] xs≤ys n = right-invariant (xs≤ys n)
  list≤-right-invariant b1 [] b2 [] b3 (_ ∷ _) xs≤ys zero = right-invariant (xs≤ys zero)
  list≤-right-invariant b1 [] b2 (_ ∷ _) b3 [] xs≤ys zero = right-invariant (xs≤ys zero)
  list≤-right-invariant b1 [] b2 (_ ∷ _) b3 (_ ∷ _) xs≤ys zero = right-invariant (xs≤ys zero)
  list≤-right-invariant b1 (_ ∷ _) b2 [] b3 [] xs≤ys zero = right-invariant (xs≤ys zero)
  list≤-right-invariant b1 (_ ∷ _) b2 [] b3 (_ ∷ _) xs≤ys zero = right-invariant (xs≤ys zero)
  list≤-right-invariant b1 (_ ∷ _) b2 (_ ∷ _) b3 [] xs≤ys zero = right-invariant (xs≤ys zero)
  list≤-right-invariant b1 (_ ∷ _) b2 (_ ∷ _) b3 (_ ∷ _) xs≤ys zero = right-invariant (xs≤ys zero)
  list≤-right-invariant b1 [] b2 [] b3 (_ ∷ zs) xs≤ys (suc n) = list≤-right-invariant b1 [] b2 [] b3 zs (xs≤ys ⊙ suc) n
  list≤-right-invariant b1 [] b2 (_ ∷ ys) b3 [] xs≤ys (suc n) = list≤-right-invariant b1 [] b2 ys b3 [] (xs≤ys ⊙ suc) n
  list≤-right-invariant b1 [] b2 (_ ∷ ys) b3 (_ ∷ zs) xs≤ys (suc n) = list≤-right-invariant b1 [] b2 ys b3 zs (xs≤ys ⊙ suc) n
  list≤-right-invariant b1 (_ ∷ xs) b2 [] b3 [] xs≤ys (suc n) = list≤-right-invariant b1 xs b2 [] b3 [] (xs≤ys ⊙ suc) n
  list≤-right-invariant b1 (_ ∷ xs) b2 [] b3 (_ ∷ zs) xs≤ys (suc n) = list≤-right-invariant b1 xs b2 [] b3 zs (xs≤ys ⊙ suc) n
  list≤-right-invariant b1 (_ ∷ xs) b2 (_ ∷ ys) b3 [] xs≤ys (suc n) = list≤-right-invariant b1 xs b2 ys b3 [] (xs≤ys ⊙ suc) n
  list≤-right-invariant b1 (_ ∷ xs) b2 (_ ∷ ys) b3 (_ ∷ zs) xs≤ys (suc n) = list≤-right-invariant b1 xs b2 ys b3 zs (xs≤ys ⊙ suc) n

  merge-right-invariant : ∀ xs ys zs → non-strict _slist<_ xs ys → non-strict _slist<_ (merge xs zs) (merge ys zs)
  merge-right-invariant xs ys zs xs≤ys =
    slist≤→non-strict (merge xs zs) (merge ys zs) $
      list≤-trans
        (xs .base ⊗ zs .base) (compact (xs .base ⊗ zs .base) $ merge-list (xs .base) (xs .elts) (zs .base) (zs .elts))
        (xs .base ⊗ zs .base) (merge-list (xs .base) (xs .elts) (zs .base) (zs .elts))
        (ys .base ⊗ zs .base) (compact (ys .base ⊗ zs .base) $ merge-list (ys .base) (ys .elts) (zs .base) (zs .elts))
        (λ n → inl $ compact-= (xs .base ⊗ zs .base) (merge-list (xs .base) (xs .elts) (zs .base) (zs .elts)) n) $
      list≤-trans
        (xs .base ⊗ zs .base) (merge-list (xs .base) (xs .elts) (zs .base) (zs .elts))
        (ys .base ⊗ zs .base) (merge-list (ys .base) (ys .elts) (zs .base) (zs .elts))
        (ys .base ⊗ zs .base) (compact (ys .base ⊗ zs .base) $ merge-list (ys .base) (ys .elts) (zs .base) (zs .elts))
        (list≤-right-invariant (xs .base) (xs .elts) (ys .base) (ys .elts) (zs .base) (zs .elts) (non-strict→slist≤ xs ys xs≤ys))
        (λ n → inl $ sym $ compact-= (ys .base ⊗ zs .base) (merge-list (ys .base) (ys .elts) (zs .base) (zs .elts)) n)

  nearly-constant-has-ordered-monoid : has-ordered-monoid (NearlyConstant 𝒟 cmp)
  nearly-constant-has-ordered-monoid =
    right-invariant→has-ordered-monoid (NearlyConstant 𝒟 cmp) λ {xs} {ys} {zs} xs≤ys →
      merge-right-invariant xs ys zs xs≤ys

--------------------------------------------------------------------------------
-- Joins

module NearlyConstJoins
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (𝒟-joins : has-joins 𝒟) (cmp : ∀ x y → Tri 𝒟._<_ x y)
  where
  open 𝒟 using (ε; _⊗_; _<_; _≤_)
  open NearlyConst 𝒟 cmp
  open Inf 𝒟
  open has-joins 𝒟-joins
  open SupportList

  join-list : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟
  join-list = merge-with join

  join-support : SupportList → SupportList → SupportList
  join-support xs ys .base = join (xs .base) (ys .base)
  join-support xs ys .elts = compact (join (xs .base) (ys .base)) (join-list (xs .base) (xs .elts) (ys .base) (ys .elts))
  join-support xs ys .compacted = compact-is-compact (join (xs .base) (ys .base)) (join-list (xs .base) (xs .elts) (ys .base) (ys .elts))

  join-list-joinl : ∀ b1 xs b2 ys → list≤ b1 xs (join b1 b2) (join-list b1 xs b2 ys)
  join-list-joinl b1 [] b2 [] n = joinl
  join-list-joinl b1 [] b2 (y ∷ ys) zero = joinl
  join-list-joinl b1 [] b2 (y ∷ ys) (suc n) = join-list-joinl b1 [] b2 ys n
  join-list-joinl b1 (x ∷ xs) b2 [] zero = joinl
  join-list-joinl b1 (x ∷ xs) b2 [] (suc n) = join-list-joinl b1 xs b2 [] n
  join-list-joinl b1 (x ∷ xs) b2 (y ∷ ys) zero = joinl
  join-list-joinl b1 (x ∷ xs) b2 (y ∷ ys) (suc n) = join-list-joinl b1 xs b2 ys n

  join-list-joinr : ∀ b1 xs b2 ys → list≤ b2 ys (join b1 b2) (join-list b1 xs b2 ys)
  join-list-joinr b1 [] b2 [] n = joinr
  join-list-joinr b1 [] b2 (y ∷ ys) zero = joinr
  join-list-joinr b1 [] b2 (y ∷ ys) (suc n) = join-list-joinr b1 [] b2 ys n
  join-list-joinr b1 (x ∷ xs) b2 [] zero = joinr
  join-list-joinr b1 (x ∷ xs) b2 [] (suc n) = join-list-joinr b1 xs b2 [] n
  join-list-joinr b1 (x ∷ xs) b2 (y ∷ ys) zero = joinr
  join-list-joinr b1 (x ∷ xs) b2 (y ∷ ys) (suc n) = join-list-joinr b1 xs b2 ys n

{- TODO
  join-list-universal : ∀ b1 xs b2 ys b3 zs
                        → merge-list≤ b1 xs b3 zs
                        → merge-list≤ b2 ys b3 zs
                        → merge-list≤ (join b1 b2) (join-list b1 xs b2 ys) b3 zs
  join-list-universal b1 xs b2 ys b3 zs = go xs ys zs
    where
      step≤ : ∀ xs ys zs {x y z}
              → tri-rec
                (merge-list≤ b1 xs b3 zs)
                (merge-list≤ b1 xs b3 zs)
                (Lift (o ⊔ r) ⊥)
                (cmp x z)
              → tri-rec
                (merge-list≤ b2 ys b3 zs)
                (merge-list≤ b2 ys b3 zs)
                (Lift (o ⊔ r) ⊥)
                (cmp y z)
              → tri-rec
                (merge-list≤ (join b1 b2) (join-list b1 xs b2 ys) b3 zs)
                (merge-list≤ (join b1 b2) (join-list b1 xs b2 ys) b3 zs)
                (Lift (o ⊔ r) ⊥)
                (cmp (join x y) z)
      step≤ xs ys zs {x = x} {y = y} {z = z} xs≤ys ys≤zs with cmp x z | cmp y z
      ... | lt x<z | lt y<z =
        merge-list≤-step≤ (join b1 b2) (join-list b1 xs b2 ys) b3 zs (universal (inr x<z) (inr y<z)) (join-list-universal b1 xs b2 ys b3 zs xs≤ys ys≤zs)
      ... | lt x<z | eq y≡z =
        merge-list≤-step≤ (join b1 b2) (join-list b1 xs b2 ys) b3 zs (universal (inr x<z) (inl y≡z)) (join-list-universal b1 xs b2 ys b3 zs xs≤ys ys≤zs)
      ... | eq x≡z | lt y<z =
        merge-list≤-step≤ (join b1 b2) (join-list b1 xs b2 ys) b3 zs (universal (inl x≡z) (inr y<z)) (join-list-universal b1 xs b2 ys b3 zs xs≤ys ys≤zs)
      ... | eq x≡z | eq y≡z =
        merge-list≤-step≤ (join b1 b2) (join-list b1 xs b2 ys) b3 zs (universal (inl x≡z) (inl y≡z)) (join-list-universal b1 xs b2 ys b3 zs xs≤ys ys≤zs)

      go : ∀ xs ys zs → merge-list≤ b1 xs b3 zs → merge-list≤ b2 ys b3 zs → merge-list≤ (join b1 b2) (join-list b1 xs b2 ys) b3 zs
      go [] [] [] xs≤zs ys≤zs =
        universal xs≤zs ys≤zs
      go [] [] (z ∷ zs) xs≤zs ys≤zs =
        step≤ [] [] zs xs≤zs ys≤zs
      go [] (y ∷ ys) [] b1≤b3 ys≤zs =
        step≤ [] ys [] (merge-list≤-step≤ b1 [] b3 [] b1≤b3 b1≤b3) ys≤zs
      go [] (y ∷ ys) (z ∷ zs) xs≤zs ys≤zs =
        step≤ [] ys zs xs≤zs ys≤zs
      go (x ∷ xs) [] [] xs≤zs b2≤b3 =
        step≤ xs [] [] xs≤zs (merge-list≤-step≤ b2 [] b3 [] b2≤b3 b2≤b3)
      go (x ∷ xs) [] (z ∷ zs) xs≤zs ys≤zs =
        step≤ xs [] zs xs≤zs ys≤zs
      go (x ∷ xs) (y ∷ ys) [] xs≤zs ys≤zs =
        step≤ xs ys [] xs≤zs ys≤zs
      go (x ∷ xs) (y ∷ ys) (z ∷ zs) xs≤zs ys≤zs =
        step≤ xs ys zs xs≤zs ys≤zs

  nearly-constant-has-joins : has-joins (NearlyConstant 𝒟 cmp)
  nearly-constant-has-joins .has-joins.join =
    join-support
  nearly-constant-has-joins .has-joins.joinl {xs} {ys} =
    merge≤→non-strict xs (join-support xs ys) $
      merge-list≤-trans
        (xs .base) (xs .elts)
        (join (xs .base) (ys .base)) (fwd $ bwd $ join-list (xs .base) (xs .elts) (ys .base) (ys .elts))
        (join (xs .base) (ys .base)) (fwd $ compact (join (xs .base) (ys .base)) $ bwd $ join-list (xs .base) (xs .elts) (ys .base) (ys .elts))
        (subst (λ ϕ → merge-list≤ (xs .base) (xs .elts) (join (xs .base) (ys .base)) ϕ)
          (sym $ fwd-bwd $ join-list (xs .base) (xs .elts) (ys .base) (ys .elts))
          (join-list-joinl (xs .base) (xs .elts) (ys .base) (ys .elts)))
        (compact-≤ (join (xs .base) (ys .base)) (bwd $ join-list (xs .base) (xs .elts) (ys .base) (ys .elts)))
  nearly-constant-has-joins .has-joins.joinr {xs} {ys} =
    merge≤→non-strict ys (join-support xs ys) $
      merge-list≤-trans
        (ys .base) (ys .elts)
        (join (xs .base) (ys .base)) (fwd $ bwd $ join-list (xs .base) (xs .elts) (ys .base) (ys .elts))
        (join (xs .base) (ys .base)) (fwd $ compact (join (xs .base) (ys .base)) $ bwd $ join-list (xs .base) (xs .elts) (ys .base) (ys .elts))
        (subst (λ ϕ → merge-list≤ (ys .base) (ys .elts) (join (xs .base) (ys .base)) ϕ)
          (sym $ fwd-bwd $ join-list (xs .base) (xs .elts) (ys .base) (ys .elts))
          (join-list-joinr (xs .base) (xs .elts) (ys .base) (ys .elts)))
        (compact-≤ (join (xs .base) (ys .base)) (bwd $ join-list (xs .base) (xs .elts) (ys .base) (ys .elts)))
  nearly-constant-has-joins .has-joins.universal {xs} {ys} {zs} xs≤zs ys≤zs =
    merge≤→non-strict (join-support xs ys) zs $
      merge-list≤-trans
        (join (xs .base) (ys .base)) (fwd $ compact (join (xs .base) (ys .base)) $ bwd (join-list (xs .base) (xs .elts) (ys .base) (ys .elts)))
        (join (xs .base) (ys .base)) (fwd $ bwd $ join-list (xs .base) (xs .elts) (ys .base) (ys .elts))
        (zs .base) (zs .elts)
        (compact-≥ (join (xs .base) (ys .base)) (bwd $ join-list (xs .base) (xs .elts) (ys .base) (ys .elts)))
        (subst (λ ϕ → merge-list≤ (join (xs .base) (ys .base)) ϕ (zs .base) (zs .elts))
          (sym $ fwd-bwd ( join-list (xs .base) (xs .elts) (ys .base) (ys .elts)))
          (join-list-universal (xs .base) (xs .elts) (ys .base) (ys .elts) (zs .base) (zs .elts)
            (non-strict→merge≤ xs zs xs≤zs)
            (non-strict→merge≤ ys zs ys≤zs)))

  -- NOTE: 'into' preserves joins regardless of WLPO, but the joins InfProd aren't /provably/
  -- joins unless we have WLPO, hence the extra module.
  into-preserves-join : ∀ xs ys n → into (join-support xs ys) n ≡ join (into xs n) (into ys n)
  into-preserves-join  xs ys n =
    into (join-support xs ys) n
      ≡⟨ index-compact (join (xs .base) (ys .base)) (join-list (xs .base) (xs .elts) (ys .base) (ys .elts)) n ⟩
    index (join (xs .base) (ys .base)) (join-list (xs .base) (xs .elts) (ys .base) (ys .elts)) n
      ≡⟨ go (xs .base) (xs .elts) (ys .base) (ys .elts) n ⟩
    join (into xs n) (into ys n) ∎
    where
      go : ∀ b1 xs b2 ys n → index (join b1 b2) (join-list b1 xs b2 ys) n ≡ join (index b1 xs n) (index b2 ys n)
      go b1 [] b2 [] n = refl
      go b1 [] b2 (y ∷ ys) zero = refl
      go b1 [] b2 (y ∷ ys) (suc n) = go b1 [] b2 ys n
      go b1 (x ∷ xs) b2 [] zero = refl
      go b1 (x ∷ xs) b2 [] (suc n) = go b1 xs b2 [] n
      go b1 (x ∷ xs) b2 (y ∷ ys) zero = refl
      go b1 (x ∷ xs) b2 (y ∷ ys) (suc n) = go b1 xs b2 ys n

  module _ (𝒟-lpo : WLPO 𝒟.strict-order _≡?_) where
    open InfProperties {𝒟 = 𝒟} _≡?_ 𝒟-lpo

    nearly-constant-is-subsemilattice : is-displacement-subsemilattice nearly-constant-has-joins (⊗∞-has-joins 𝒟-joins)
    nearly-constant-is-subsemilattice .is-displacement-subsemilattice.has-displacement-subalgebra = NearlyConstant⊆InfProd cmp
    nearly-constant-is-subsemilattice .is-displacement-subsemilattice.pres-joins x y = funext (into-preserves-join x y)
-}

--------------------------------------------------------------------------------
-- Bottoms

module _
  {o r}
  {𝒟 : Displacement-algebra o r}
  (let module 𝒟 = Displacement-algebra 𝒟)
  (𝒟-bottom : has-bottom 𝒟)
  (cmp : ∀ x y → Tri (Displacement-algebra._<_ 𝒟) x y) (b : ⌞ 𝒟 ⌟)
  where
  open 𝒟 using (ε; _⊗_; _<_; _≤_)
  open NearlyConst 𝒟 cmp
  open Inf 𝒟
  open SupportList
  open has-bottom 𝒟-bottom

  bot-list : SupportList
  bot-list = support-list bot [] (lift tt)

  bot-list-is-bottom : ∀ b xs → list≤ bot [] b xs
  bot-list-is-bottom b xs n = is-bottom _

  nearly-constant-has-bottom : has-bottom (NearlyConstant 𝒟 cmp)
  nearly-constant-has-bottom .has-bottom.bot = bot-list
  nearly-constant-has-bottom .has-bottom.is-bottom xs =
    slist≤→non-strict bot-list xs $ bot-list-is-bottom (xs .base) (xs .elts)

{- TODO
  module _ (𝒟-wlpo : WLPO 𝒟.strict-order _≡?_) where
    open InfProperties {𝒟 = 𝒟} _≡?_ 𝒟-lpo

    nearly-constant-is-bounded-subalgebra : is-bounded-displacement-subalgebra nearly-constant-has-bottom (⊗∞-has-bottom 𝒟-bottom)
    nearly-constant-is-bounded-subalgebra .is-bounded-displacement-subalgebra.has-displacement-subalgebra = NearlyConstant⊆InfProd cmp
    nearly-constant-is-bounded-subalgebra .is-bounded-displacement-subalgebra.pres-bottom = refl
-}
