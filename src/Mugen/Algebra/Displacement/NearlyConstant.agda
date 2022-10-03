module Mugen.Algebra.Displacement.NearlyConstant where

open import 1Lab.Reflection.Record

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.Displacement.Coimage
open import Mugen.Algebra.Displacement.InfiniteProduct
open import Mugen.Algebra.OrderedMonoid
open import Mugen.Order.StrictOrder

open import Mugen.Data.List

module NearlyConst {o r} (𝒟 : DisplacementAlgebra o r) (cmp : ∀ x y → Tri (DisplacementAlgebra._<_ 𝒟) x y) where

  private
    module 𝒟 = DisplacementAlgebra 𝒟
    open 𝒟 using (ε; _⊗_; _<_; _≤_)
    open Inf 𝒟

    instance
      HLevel-< : ∀ {x y} {n} → H-Level (x < y) (suc n)
      HLevel-< = prop-instance 𝒟.<-is-prop

      HLevel-≤ : ∀ {x y} {n} → H-Level (x ≤ y) (suc n)
      HLevel-≤ = prop-instance 𝒟.≤-is-prop

  _≡?_ : Discrete ⌞ 𝒟 ⌟
  x ≡? y =
    tri-elim
      (λ _ → Dec (x ≡ y))
      (λ x<y → no λ x≡y → 𝒟.irrefl (𝒟.≡-transl (sym x≡y) x<y))
      yes
      (λ y<x → no λ x≡y → 𝒟.irrefl (𝒟.≡-transl x≡y y<x))
      (cmp x y)

  is-compact : ⌞ 𝒟 ⌟ → Bwd ⌞ 𝒟 ⌟ → Type
  is-compact base [] = ⊤
  is-compact base (xs #r x) =
    case _
      (λ _ → ⊥)
      (λ _ → ⊤)
      (x ≡? base)

  is-compact-case : ∀ {x base : ⌞ 𝒟 ⌟} → Dec (x ≡ base) → Type
  is-compact-case p = 
    case _
      (λ _ → ⊥)
      (λ _ → ⊤)
      p

  -- Propositional computation helpers for 'is-compact'
  ¬base-is-compact : ∀ xs {x base} → (x ≡ base → ⊥) → is-compact base (xs #r x)
  ¬base-is-compact xs {x = x} {base = base} ¬base with x ≡? base 
  ... | yes base! = ¬base base!
  ... | no _ = tt

  base-isnt-compact : ∀ xs {x base} → x ≡ base → is-compact base (xs #r x) → ⊥
  base-isnt-compact xs {x = x} {base = base} base! is-compact with x ≡? base
  ... | no ¬base = ¬base base!

  base-isnt-compact-∷ : ∀ {xs x base} → xs ≡ [] → x ≡ base → is-compact base (bwd (x ∷ xs)) → ⊥
  base-isnt-compact-∷ {xs = []} p base! is-compact = base-isnt-compact [] base! is-compact
  base-isnt-compact-∷ {xs = x ∷ xs} p base! is-compact = ∷≠[] p

  is-compact-++r : ∀ xs ys base → is-compact base (xs ++r ys) → is-compact base ys
  is-compact-++r xs [] base compact = tt
  is-compact-++r xs (ys #r x) base compact with x ≡? base
  ... | no ¬base = tt

  is-compact-tail : ∀ x xs base → is-compact base (bwd (x ∷ xs)) → is-compact base (bwd xs)
  is-compact-tail x xs base compact =
     is-compact-++r ([] #r x) (bwd xs) base (subst (is-compact base) (bwd-++ (x ∷ []) xs) compact)

  is-compact-is-prop : ∀ base xs → is-prop (is-compact base xs)
  is-compact-is-prop base [] = hlevel 1
  is-compact-is-prop base (xs #r x) with x ≡? base
  ... | yes _ = hlevel 1
  ... | no _ = hlevel 1

  -- Remove all trailing 'base' elements
  compact : ⌞ 𝒟 ⌟ → Bwd ⌞ 𝒟 ⌟ → Bwd ⌞ 𝒟 ⌟
  compact base [] = []
  compact base (xs #r x) =
    case _
      (λ _ → compact base xs)
      (λ _ → xs #r x)
      (x ≡? base)

  compact-case : ∀ xs {x base} → Dec (x ≡ base) → Bwd ⌞ 𝒟 ⌟
  compact-case xs {x = x} {base = base} p =
    case _
      (λ _ → compact base xs)
      (λ _ → xs #r x)
      p

  -- Propositional computation helpers for 'compact'
  compact-step : ∀ xs {x base} → x ≡ base → compact base (xs #r x) ≡ compact base xs
  compact-step xs {x = x} {base = base} base! with x ≡? base
  ... | yes _ = refl
  ... | no ¬base = absurd $ ¬base base!

  compact-done : ∀ xs {x base} → (x ≡ base → ⊥) → compact base (xs #r x) ≡ xs #r x
  compact-done xs {x = x} {base = base} ¬base with x ≡? base
  ... | yes base! = absurd $ ¬base base!
  ... | no _ = refl

  compact-compacted : ∀ base xs → is-compact base xs → compact base xs ≡ xs
  compact-compacted base [] is-compact = refl
  compact-compacted base (xs #r x) is-compact with x ≡? base
  ... | no _ = refl

  compact-is-compact : ∀ base xs → is-compact base (compact base xs)
  compact-is-compact base [] = tt
  compact-is-compact base (xs #r x) with x ≡? base
  ... | yes _ = compact-is-compact base xs
  ... | no ¬base = ¬base-is-compact xs ¬base

  compact-last : ∀ base xs ys y → compact base xs ≡ ys #r y → y ≡ base → ⊥
  compact-last base [] ys y p y≡base = #r≠[] (sym p)
  compact-last base (xs #r x) ys y p y≡base with x ≡? base
  ... | yes x≡base = compact-last base xs ys y p y≡base
  ... | no x≠base = x≠base (#r-last-inj p ∙ y≡base)

  --------------------------------------------------------------------------------
  -- Vanishing Lists
  -- 
  -- We say a list vanishes relative to some base 'b' if it /only/ contains 'b'.
  -- Furthermore, we say a /backward/ list compacts relative to some base if 
  -- it's compaction is equal to [].
  --
  -- These conditions may seems somewhat redundant. Why not define one as
  -- primary, and the reversed version with fwd/bwd? Indeed, both conditions
  -- are equivalent! However, the induction orders are different, and we want
  -- to *trust the natural recursion*.

  vanishes : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → Type
  vanishes b [] = ⊤
  vanishes b (x ∷ xs) =
    case _
      (λ _ → vanishes b xs)
      (λ _ → ⊥)
      (x ≡? b)

  vanish-step : ∀ base x xs → x ≡ base → vanishes base xs → vanishes base (x ∷ xs)
  vanish-step base x xs base! vanish with x ≡? base
  ... | yes _ = vanish
  ... | no ¬base = absurd $ ¬base base!

  vanishes-◁⊗-compact : ∀ base xs ys → compact base xs ≡ [] → vanishes base ys → compact base (xs ◁⊗ ys) ≡ []
  vanishes-◁⊗-compact base xs [] compacts vanishes = compacts
  vanishes-◁⊗-compact base xs (y ∷ ys) compacts vanishes with y ≡? base
  ... | yes base! = vanishes-◁⊗-compact base (xs #r y) ys (compact-step xs base! ∙ compacts) vanishes

  vanishes-⊗▷-compact : ∀ base xs ys → compact base xs ≡ [] → vanishes base ys → vanishes base (xs ⊗▷ ys)
  vanishes-⊗▷-compact base [] ys compacts vanishes = vanishes
  vanishes-⊗▷-compact base (xs #r x) ys compacts vanishes with x ≡? base
  ... | yes base! = vanishes-⊗▷-compact base xs (x ∷ ys) compacts (vanish-step base x ys base! vanishes)
  ... | no _ = absurd $ #r≠[] compacts

  compacts-bwd : ∀ base xs → vanishes base xs → compact base (bwd xs) ≡ []
  compacts-bwd base xs vanishes = vanishes-◁⊗-compact base [] xs refl vanishes

  compacts-fwd : ∀ base xs → vanishes base (fwd xs) → compact base xs ≡ []
  compacts-fwd base xs vanishes = subst (λ ϕ → compact base ϕ ≡ []) (bwd-fwd xs) (compacts-bwd base (fwd xs) vanishes)

  vanishes-fwd : ∀ base xs → compact base xs ≡ [] → vanishes base (fwd xs)
  vanishes-fwd base xs compacts = vanishes-⊗▷-compact base xs [] compacts tt

  vanishes-bwd : ∀ base xs → compact base (bwd xs) ≡ [] → vanishes base xs
  vanishes-bwd base xs compacts = subst (vanishes base) (fwd-bwd xs) (vanishes-fwd base (bwd xs) compacts)

  vanish-++ : ∀ {base} xs ys → vanishes base (xs ++ ys) → vanishes base ys
  vanish-++ [] ys vanish = vanish
  vanish-++ {base = base} (x ∷ xs) ys vanish with x ≡? base
  ... | yes _ = vanish-++ xs ys vanish

  vanish-head-∷ : ∀ base x xs → vanishes base (x ∷ xs) → x ≡ base
  vanish-head-∷ base x xs v with x ≡? base
  ... | yes base! = base!

  vanish-tail-∷ : ∀ base x xs → vanishes base (x ∷ xs) → vanishes base xs
  vanish-tail-∷ base x xs vanish with x ≡? base
  ... | yes base! = vanish

  compacts-head-∷ : ∀ base x xs → compact base (bwd (x ∷ xs)) ≡ [] → x ≡ base
  compacts-head-∷ base x xs compacts =
    vanish-head-∷ base x xs $
    subst (vanishes base) (fwd-bwd (x ∷ xs)) $
    vanishes-fwd base (bwd (x ∷ xs)) compacts 

  compacts-tail-∷ : ∀ base x xs → compact base (bwd (x ∷ xs)) ≡ [] → compact base (bwd xs) ≡ []
  compacts-tail-∷ base x xs compacts =
    compacts-bwd base xs $
    vanish-tail-∷ base x xs $
    subst (vanishes base) (fwd-bwd (x ∷ xs)) $
    vanishes-fwd base (bwd (x ∷ xs)) compacts 

  compact-vanishr-++r : ∀ {base} xs ys → compact base ys ≡ [] → compact base (xs ++r ys) ≡ compact base xs
  compact-vanishr-++r {base = base} xs [] ys-vanish = refl
  compact-vanishr-++r {base = base} xs (ys #r y) ys-vanish with y ≡? base
  ... | yes _ = compact-vanishr-++r xs ys ys-vanish
  ... | no _ = absurd $ #r≠[] ys-vanish

  compact-++r : ∀ {base} xs ys zs → compact base ys ≡ compact base zs → compact base (xs ++r ys) ≡ compact base (xs ++r zs)
  compact-++r {base = base} xs [] [] p =
    refl
  compact-++r {base = base} xs [] (zs #r z) p =
    sym (compact-vanishr-++r xs (zs #r z) (sym p))
  compact-++r {base = base} xs (ys #r y) [] p =
    compact-vanishr-++r xs (ys #r y) p
  compact-++r {base = base} xs (ys #r y) (zs #r z) =
    -- Cannot be done using with-abstraction /or/ a helper function because the termination
    -- checker gets confused.
    -- Ouch.
    case (λ p → compact-case ys p ≡ compact base (zs #r z) → compact-case (xs ++r ys) p ≡ compact base (xs ++r (zs #r z)))
      (λ y-base! →
        case (λ p → compact base ys ≡ compact-case zs p → compact base (xs ++r ys) ≡ compact-case (xs ++r zs) p)
          (λ z-base! p → compact-++r xs ys zs p)
          (λ ¬z-base p → compact-++r xs ys (zs #r z) (p ∙ sym (compact-done zs ¬z-base)) ∙ compact-done (xs ++r zs) ¬z-base)
          (z ≡? base))
      (λ ¬y-base →
        case (λ p → ys #r y ≡ compact-case zs p → (xs ++r ys) #r y ≡ compact-case (xs ++r zs) p)
          (λ z-base! p → sym (compact-done ((xs ++r ys)) ¬y-base) ∙ compact-++r xs (ys #r y) zs (compact-done ys ¬y-base ∙ p))
          (λ ¬z-base p → ap (xs ++r_) p)
          (z ≡? base))
      (y ≡? base)

  compact-◁⊗ : ∀ {base} xs ys zs → compact base (bwd ys) ≡ compact base (bwd zs) → compact base (xs ◁⊗ ys) ≡ compact base (xs ◁⊗ zs)
  compact-◁⊗ {base = base} xs ys zs p =
    compact base (xs ◁⊗ ys)      ≡⟨ ap (compact base) (◁⊗-bwd xs ys) ⟩
    compact base (xs ++r bwd ys) ≡⟨ compact-++r xs (bwd ys) (bwd zs) p ⟩
    compact base (xs ++r bwd zs) ≡˘⟨ ap (compact base) (◁⊗-bwd xs zs) ⟩
    compact base (xs ◁⊗ zs) ∎

  compact-◁⊗-¬base : ∀ xs ys {x base} → (x ≡ base → ⊥) → compact base ((xs #r x) ◁⊗ ys) ≡ (xs #r x) ++r compact base (bwd ys)
  compact-◁⊗-¬base xs ys {x = x} {base = base} x≠base with inspect (compact base (bwd ys))
  ... | [] , p =
    compact base ((xs #r x) ◁⊗ ys) ≡⟨ compact-◁⊗ (xs #r x) ys [] p ⟩
    compact base ((xs #r x))       ≡⟨ compact-done xs x≠base ⟩
    xs #r x                        ≡˘⟨ ap ((xs #r x) ++r_) p ⟩
    (xs #r x) ++r compact base (bwd ys) ∎
  ... | cs #r c , p =
    compact base ((xs #r x) ◁⊗ ys)                   ≡⟨ compact-◁⊗ (xs #r x) ys (fwd (cs #r c)) (p ∙ sym cs#rc-compact ∙ sym (ap (compact base) (bwd-fwd (cs #r c)))) ⟩
    compact base ((xs #r x) ◁⊗ fwd (cs #r c))        ≡⟨ ap (compact base) (◁⊗-bwd (xs #r x) (fwd (cs #r c))) ⟩
    compact base ((xs #r x) ++r bwd (fwd (cs #r c))) ≡⟨ ap (λ ϕ → compact base ((xs #r x) ++r ϕ)) (bwd-fwd (cs #r c)) ⟩
    compact base ((xs #r x) ++r (cs #r c))           ≡⟨ compact-done ((xs #r x) ++r cs) c≠base ⟩
    (xs #r x) ++r (cs #r c)                          ≡˘⟨ ap ((xs #r x) ++r_) p ⟩
    (xs #r x) ++r compact base (bwd ys) ∎
    where
      c≠base : c ≡ base → ⊥
      c≠base = compact-last base (bwd ys) cs c p

      cs#rc-compact : compact base (cs #r c) ≡ cs #r c
      cs#rc-compact = compact-done cs c≠base

  --------------------------------------------------------------------------------
  -- Merging Lists
  -- 
  -- We start by defining how to merge two lists without performing
  -- compaction.

  merge-with : (⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟) → ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟
  merge-with f b1 [] b2 [] = []
  merge-with f b1 [] b2 (y ∷ ys) = f b1 y ∷ merge-with f b1 [] b2 ys
  merge-with f b1 (x ∷ xs) b2 [] = f x b2 ∷ merge-with f b1 xs b2 []
  merge-with f b1 (x ∷ xs) b2 (y ∷ ys) = f x y ∷ merge-with f b1 xs b2 ys

  merge-list : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟
  merge-list = merge-with _⊗_

  module _ where
    private variable
      b1 b2 b3 : ⌞ 𝒟 ⌟
      xs ys zs : List ⌞ 𝒟 ⌟

    merge-list-idl : ∀ ys → merge-list ε [] b2 ys ≡ ys
    merge-list-idl [] = refl
    merge-list-idl (y ∷ ys) = ap₂ _∷_ 𝒟.idl (merge-list-idl ys)

    merge-list-idr : ∀ xs → merge-list b1 xs ε [] ≡ xs
    merge-list-idr [] = refl
    merge-list-idr (x ∷ xs) = ap₂ _∷_ 𝒟.idr (merge-list-idr xs)

    merge-list-assoc : ∀ xs ys zs → merge-list b1 xs (b2 ⊗ b3) (merge-list b2 ys b3 zs) ≡ merge-list (b1 ⊗ b2) (merge-list b1 xs b2 ys) b3 zs
    merge-list-assoc = go _ _ _
      where
        go : ∀ b1 b2 b3 xs ys zs → merge-list b1 xs (b2 ⊗ b3) (merge-list b2 ys b3 zs) ≡ merge-list (b1 ⊗ b2) (merge-list b1 xs b2 ys) b3 zs
        go b1 b2 b3 [] [] [] =
          refl
        go b1 b2 b3 [] [] (z ∷ zs) =
          ap₂ _∷_ 𝒟.associative (go b1 b2 b3 [] [] zs)
        go b1 b2 b3 [] (y ∷ ys) [] =
          ap₂ _∷_ 𝒟.associative (go b1 b2 b3 [] ys [])
        go b1 b2 b3 [] (y ∷ ys) (z ∷ zs) =
          ap₂ _∷_ 𝒟.associative (go b1 b2 b3 [] ys zs)
        go b1 b2 b3 (x ∷ xs) [] [] =
          ap₂ _∷_ 𝒟.associative (go b1 b2 b3 xs [] [])
        go b1 b2 b3 (x ∷ xs) [] (z ∷ zs) =
          ap₂ _∷_ 𝒟.associative (go b1 b2 b3 xs [] zs)
        go b1 b2 b3 (x ∷ xs) (y ∷ ys) [] =
          ap₂ _∷_ 𝒟.associative (go b1 b2 b3 xs ys [])
        go b1 b2 b3 (x ∷ xs) (y ∷ ys) (z ∷ zs) =
          ap₂ _∷_ 𝒟.associative (go b1 b2 b3 xs ys zs)

    merge-list-∷rl : ∀ b1 xs b2 ys → compact (b1 ⊗ b2) (bwd (merge-list b1 (xs ∷r b1) b2 ys)) ≡ compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 ys))
    merge-list-∷rl b1 [] b2 [] =
      compact-step [] refl
    merge-list-∷rl b1 [] b2 (y ∷ ys) =
      refl
    merge-list-∷rl b1 (x ∷ xs) b2 [] =
      compact (b1 ⊗ b2) (bwd ((x ⊗ b2) ∷ merge-list b1 (xs ∷r b1) b2 []))
        ≡⟨ ap (compact (b1 ⊗ b2)) (bwd-++ ((x ⊗ b2) ∷ []) (merge-list b1 (xs ∷r b1) b2 [])) ⟩
      compact (b1 ⊗ b2) (bwd ((x ⊗ b2) ∷ []) ++r bwd (merge-list b1 (xs ∷r b1) b2 []))
        ≡⟨ compact-++r (bwd ((x ⊗ b2) ∷ [])) (bwd (merge-list b1 (xs ∷r b1) b2 [])) (bwd (merge-list b1 xs b2 [])) (merge-list-∷rl b1 xs b2 []) ⟩
      compact (b1 ⊗ b2) (bwd ((x ⊗ b2) ∷ []) ++r bwd (merge-list b1 xs b2 []))
        ≡˘⟨ ap (compact (b1 ⊗ b2)) (bwd-++ ((x ⊗ b2) ∷ []) (merge-list b1 xs b2 [])) ⟩
      compact (b1 ⊗ b2) (bwd ((x ⊗ b2) ∷ merge-list b1 xs b2 []))
        ∎
    merge-list-∷rl b1 (x ∷ xs) b2 (y ∷ ys) =
      compact (b1 ⊗ b2) (bwd ((x ⊗ y) ∷ merge-list b1 (xs ∷r b1) b2 ys))
        ≡⟨ ap (compact (b1 ⊗ b2)) (bwd-++ ((x ⊗ y) ∷ []) (merge-list b1 (xs ∷r b1) b2 ys)) ⟩
      compact (b1 ⊗ b2) (bwd ((x ⊗ y) ∷ []) ++r bwd (merge-list b1 (xs ∷r b1) b2 ys))
        ≡⟨ compact-++r (bwd ((x ⊗ y) ∷ [])) (bwd (merge-list b1 (xs ∷r b1) b2 ys)) ((bwd (merge-list b1 xs b2 ys))) (merge-list-∷rl b1 xs b2 ys) ⟩
      compact (b1 ⊗ b2) (bwd ((x ⊗ y) ∷ []) ++r bwd (merge-list b1 xs b2 ys))
        ≡˘⟨ ap (compact (b1 ⊗ b2)) (bwd-++ ((x ⊗ y) ∷ []) (merge-list b1 xs b2 ys)) ⟩
      compact (b1 ⊗ b2) (bwd ((x ⊗ y) ∷ merge-list b1 xs b2 ys))
        ∎

  merge-list-∷rr : ∀ b1 xs b2 ys → compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (ys ∷r b2))) ≡ compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 ys))
  merge-list-∷rr b1 [] b2 [] =
    compact-step [] refl
  merge-list-∷rr b1 [] b2 (y ∷ ys) =
    compact (b1 ⊗ b2) (bwd ((b1 ⊗ y) ∷ merge-list b1 [] b2 (ys ∷r b2)))
      ≡⟨ ap (compact (b1 ⊗ b2)) (bwd-++ (((b1 ⊗ y) ∷ [])) (merge-list b1 [] b2 (ys ∷r b2))) ⟩
    compact (b1 ⊗ b2) (bwd ((b1 ⊗ y) ∷ []) ++r bwd (merge-list b1 [] b2 (ys ∷r b2)))
      ≡⟨ compact-++r (bwd ((b1 ⊗ y) ∷ [])) (bwd (merge-list b1 [] b2 (ys ∷r b2))) ( bwd (merge-list b1 [] b2 ys)) (merge-list-∷rr b1 [] b2 ys) ⟩
    compact (b1 ⊗ b2) (bwd ((b1 ⊗ y) ∷ []) ++r bwd (merge-list b1 [] b2 ys))
      ≡˘⟨ ap (compact (b1 ⊗ b2)) (bwd-++ (((b1 ⊗ y) ∷ [])) (merge-list b1 [] b2 ys)) ⟩
    compact (b1 ⊗ b2) (bwd ((b1 ⊗ y) ∷ merge-list b1 [] b2 ys))
      ∎
  merge-list-∷rr b1 (x ∷ xs) b2 [] =
    refl
  merge-list-∷rr b1 (x ∷ xs) b2 (y ∷ ys) =
    compact (b1 ⊗ b2) (bwd ((x ⊗ y) ∷ merge-list b1 xs b2 (ys ∷r b2)))
      ≡⟨ ap (compact (b1 ⊗ b2)) (bwd-++ (((x ⊗ y) ∷ [])) (merge-list b1 xs b2 (ys ∷r b2))) ⟩
    compact (b1 ⊗ b2) (bwd ((x ⊗ y) ∷ []) ++r bwd (merge-list b1 xs b2 (ys ∷r b2)))
      ≡⟨ compact-++r (bwd ((x ⊗ y) ∷ [])) (bwd (merge-list b1 xs b2 (ys ∷r b2))) (bwd (merge-list b1 xs b2 ys)) (merge-list-∷rr b1 xs b2 ys) ⟩
    compact (b1 ⊗ b2) (bwd ((x ⊗ y) ∷ []) ++r bwd (merge-list b1 xs b2 ys))
      ≡˘⟨ ap (compact (b1 ⊗ b2)) (bwd-++ (((x ⊗ y) ∷ [])) (merge-list b1 xs b2 ys)) ⟩
    compact (b1 ⊗ b2) (bwd (merge-list b1 (x ∷ xs) b2 (y ∷ ys)))
      ∎

  merge-list-#rl : ∀ b1 xs b2 ys → compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd (xs #r b1)) b2 ys)) ≡ compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd xs) b2 ys))
  merge-list-#rl b1 xs b2 ys =
    compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd (xs #r b1)) b2 ys))
      ≡⟨ ap (λ ϕ → compact (b1 ⊗ b2) (bwd (merge-list b1 ϕ b2 ys))) (fwd-++r xs ([] #r b1)) ⟩
    compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd xs ∷r b1) b2 ys))
      ≡⟨ merge-list-∷rl b1 (fwd xs) b2 ys ⟩
    compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd xs) b2 ys)) ∎

  merge-list-#rr : ∀ b1 xs b2 ys → compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd (ys #r b2)))) ≡ compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd ys)))
  merge-list-#rr b1 xs b2 ys =
    compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd (ys #r b2))))
      ≡⟨ ap (λ ϕ → compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 ϕ))) (fwd-++r ys ([] #r b2)) ⟩
    compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd ys ++ fwd ([] #r b2))))
      ≡⟨ merge-list-∷rr b1 xs b2 (fwd ys) ⟩
    compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd ys)))
      ∎

  compact-mergel : ∀ b1 xs b2 ys → compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd (compact b1 xs)) b2 ys)) ≡ compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd xs) b2 ys))
  compact-mergel b1 [] b2 ys =
    refl
  compact-mergel b1 (xs #r x) b2 ys with x ≡? b1
  ... | yes base! =
    compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd (compact b1 xs)) b2 ys))
      ≡⟨ compact-mergel b1 xs b2 ys ⟩
    compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd xs) b2 ys))
      ≡˘⟨ merge-list-#rl b1 xs b2 ys ⟩
    compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd (xs #r b1)) b2 ys))
      ≡⟨ ap (λ ϕ → compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd (xs #r ϕ)) b2 ys))) (sym base!) ⟩
    compact (b1 ⊗ b2) (bwd (merge-list b1 (fwd (xs #r x)) b2 ys))
      ∎
  ... | no ¬base =
    refl

  compact-merger : ∀ b1 xs b2 ys → compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd (compact b2 ys)))) ≡ compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd ys)))
  compact-merger b1 xs b2 [] =
    refl
  compact-merger b1 xs b2 (ys #r y) with y ≡? b2
  ... | yes base! =
    compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd (compact b2 ys))))
      ≡⟨ compact-merger b1 xs b2 ys ⟩
    compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd ys)))
      ≡˘⟨ merge-list-#rr b1 xs b2 ys ⟩
    compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd (ys #r b2))))
      ≡⟨ ap (λ ϕ → compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd (ys #r ϕ))))) (sym base!) ⟩
    compact (b1 ⊗ b2) (bwd (merge-list b1 xs b2 (fwd (ys #r y))))
      ∎
  ... | no ¬base =
    refl
 
  --------------------------------------------------------------------------------
  -- Compact Support Lists

  record SupportList : Type o where
    constructor support-list
    no-eta-equality
    field
      base : ⌞ 𝒟 ⌟
      elts : Bwd ⌞ 𝒟 ⌟
      compacted : is-compact base elts

    list : List ⌞ 𝒟 ⌟
    list = fwd elts

  open SupportList

  support-list-path : ∀ {xs ys : SupportList} → xs .base ≡ ys .base → xs .elts ≡ ys .elts → xs ≡ ys
  support-list-path p q i .base = p i
  support-list-path p q i .elts = q i
  support-list-path {xs = xs} {ys = ys} p q i .compacted =
    is-prop→pathp (λ i → is-compact-is-prop (p i) (q i)) (xs .compacted) (ys .compacted) i

  private unquoteDecl eqv = declare-record-iso eqv (quote SupportList)

  SupportList-is-set : is-set SupportList
  SupportList-is-set =
    is-hlevel≃ 2 (Iso→Equiv eqv e⁻¹) $
      Σ-is-hlevel 2 (hlevel 2) λ base →
      Σ-is-hlevel 2 (Bwd-is-hlevel 0  ⌞ 𝒟 ⌟-set) λ xs →
      is-prop→is-set (is-compact-is-prop base xs)

  -- Smart constructor for SupportList.
  compact-support : ⌞ 𝒟 ⌟ → Bwd ⌞ 𝒟 ⌟ → SupportList
  compact-support base xs .SupportList.base = base
  compact-support base xs .SupportList.elts = compact base xs
  compact-support base xs .SupportList.compacted = compact-is-compact base xs

  merge : SupportList → SupportList → SupportList
  merge xs ys .SupportList.base = xs .base ⊗ ys .base
  merge xs ys .SupportList.elts = compact (xs .base ⊗ ys .base) (bwd (merge-list (xs .base) (list xs) (ys .base) (list ys)))
  merge xs ys .SupportList.compacted = compact-is-compact (xs .base ⊗ ys .base) (bwd (merge-list (xs .base) (list xs) (ys .base) (list ys)))

  empty : SupportList
  empty .base = ε
  empty .elts = []
  empty .compacted = tt

  elts-compact : ∀ xs → compact (xs .base) (xs .elts) ≡ xs .elts
  elts-compact xs = compact-compacted (xs .base) (xs .elts) (xs .compacted)

  merge-support : SupportList → SupportList → List ⌞ 𝒟 ⌟
  merge-support xs ys = merge-list (xs .base) (list xs) (ys .base) (list ys)
  {-# INLINE merge-support #-}

  merge-idl : ∀ xs → merge empty xs ≡ xs
  merge-idl xs = support-list-path 𝒟.idl $
    compact (ε ⊗ xs .base) (bwd (merge-list ε [] (xs .base) (list xs)))
      ≡⟨ ap (λ ϕ → compact (ε ⊗ xs .base) (bwd ϕ)) (merge-list-idl (list xs)) ⟩
    compact (ε ⊗ xs .base) (bwd (list xs))
     ≡⟨ ap₂ compact 𝒟.idl (bwd-fwd (xs .elts)) ⟩
    compact (xs .base) (xs .elts)
      ≡⟨ elts-compact xs ⟩
    xs .elts ∎

  merge-idr : ∀ xs → merge xs empty ≡ xs
  merge-idr xs = support-list-path 𝒟.idr $
    compact (xs .base ⊗ ε) (bwd (merge-list (xs .base) (list xs) ε []))
      ≡⟨ ap (λ ϕ → compact (xs .base ⊗ ε) (bwd ϕ)) (merge-list-idr (list xs)) ⟩
    compact (xs .base ⊗ ε) (bwd (list xs))
      ≡⟨ ap₂ compact 𝒟.idr (bwd-fwd (xs .elts)) ⟩
    compact (xs .base) (xs .elts)
      ≡⟨ elts-compact xs ⟩
    xs .elts ∎
  
  merge-assoc : ∀ xs ys zs → merge xs (merge ys zs) ≡ merge (merge xs ys) zs
  merge-assoc xs ys zs = support-list-path 𝒟.associative $
    compact (xs .base ⊗ (ys .base ⊗ zs .base)) (bwd (merge-list _ (list xs) _ (fwd (compact _ (bwd (merge-support ys zs))))))
      ≡⟨ compact-merger _ (list xs) _ (bwd (merge-support ys zs)) ⟩
    compact (xs .base ⊗ (ys .base ⊗ zs .base)) (bwd (merge-list _ (list xs) _ (fwd (bwd (merge-support ys zs)))))
      ≡⟨ ap (λ ϕ → compact (xs .base ⊗ (ys .base ⊗ zs .base)) (bwd (merge-list _ (list xs) _ ϕ))) (fwd-bwd (merge-support ys zs)) ⟩
    compact (xs .base ⊗ (ys .base ⊗ zs .base)) (bwd (merge-list _ (list xs) _ (merge-list (ys .base) (list ys) (zs .base) (list zs))))
      ≡⟨ ap₂ compact 𝒟.associative (ap bwd (merge-list-assoc (list xs) (list ys) (list zs))) ⟩
    compact ((xs .base ⊗ ys .base) ⊗ zs .base) (bwd (merge-list _ (merge-support xs ys) _ (list zs)))
      ≡˘⟨ ap (λ ϕ → compact ((xs .base ⊗ ys .base) ⊗ zs .base) (bwd (merge-list _ ϕ _ (list zs)))) (fwd-bwd (merge-support xs ys)) ⟩
    compact ((xs .base ⊗ ys .base) ⊗ zs .base) (bwd (merge-list _ (fwd (bwd (merge-support xs ys))) _ (list zs)))
      ≡˘⟨ compact-mergel _ (bwd (merge-support xs ys)) _ (list zs) ⟩
    compact ((xs .base ⊗ ys .base) ⊗ zs .base) (bwd (merge-list _ (fwd (compact _ (bwd (merge-support xs ys)))) _ (list zs)))
      ∎

  --------------------------------------------------------------------------------
  -- Algebraic Structure

  merge-is-magma : is-magma merge
  merge-is-magma .has-is-set = SupportList-is-set

  merge-is-semigroup : is-semigroup merge
  merge-is-semigroup .has-is-magma = merge-is-magma
  merge-is-semigroup .associative {xs} {ys} {zs} = merge-assoc xs ys zs

  merge-is-monoid : is-monoid empty merge
  merge-is-monoid .has-is-semigroup = merge-is-semigroup
  merge-is-monoid .idl {xs} = merge-idl xs
  merge-is-monoid .idr {ys} = merge-idr ys

  --------------------------------------------------------------------------------
  -- Order
  -- We choose to have our orders compute like this, as we get to avoid
  -- a propositional truncation compared to the All _≤_ + Some _<_ represenation.

  merge-list≤ : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → Type (o ⊔ r)
  merge-list≤ b1 [] b2 [] =
    b1 ≤ b2
  merge-list≤ b1 [] b2 (y ∷ ys) =
    tri-rec
      (merge-list≤ b1 [] b2 ys)
      (merge-list≤ b1 [] b2 ys)
      (Lift _ ⊥)
      (cmp b1 y)
  merge-list≤ b1 (x ∷ xs) b2 [] =
    tri-rec
      (merge-list≤ b1 xs b2 [])
      (merge-list≤ b1 xs b2 [])
      (Lift _ ⊥)
      (cmp x b2)
  merge-list≤ b1 (x ∷ xs) b2 (y ∷ ys) =
    tri-rec
      (merge-list≤ b1 xs b2 ys)
      (merge-list≤ b1 xs b2 ys)
      (Lift _ ⊥)
      (cmp x y)

  merge-list< : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → Type (o ⊔ r)
  merge-list< b1 [] b2 [] =
    Lift o (b1 < b2)
  merge-list< b1 [] b2 (y ∷ ys) =
    tri-rec
      (merge-list≤ b1 [] b2 ys)
      (merge-list< b1 [] b2 ys)
      (Lift _ ⊥)
      (cmp b1 y)
  merge-list< b1 (x ∷ xs) b2 [] =
    tri-rec
      (merge-list≤ b1 xs b2 [])
      (merge-list< b1 xs b2 [])
      (Lift _ ⊥)
      (cmp x b2)
  merge-list< b1 (x ∷ xs) b2 (y ∷ ys) =
    tri-rec
      (merge-list≤ b1 xs b2 ys)
      (merge-list< b1 xs b2 ys)
      (Lift _ ⊥)
      (cmp x y)

  merge-list-base< : ∀ b1 xs b2 ys → xs ≡ ys → b1 < b2 → merge-list< b1 xs b2 ys
  merge-list-base< b1 [] b2 [] p b1<b2 = lift b1<b2
  merge-list-base< b1 [] b2 (y ∷ ys) p b1<b2 = absurd $ ∷≠[] (sym p)
  merge-list-base< b1 (x ∷ xs) b2 [] p b1<b2 = absurd $ ∷≠[] p
  merge-list-base< b1 (x ∷ xs) b2 (y ∷ ys) p b1<b2 with cmp x y
  ... | lt x<y = absurd $ 𝒟.irrefl (𝒟.≡-transl (sym $ ∷-head-inj p) x<y)
  ... | eq _ = merge-list-base< b1 xs b2 ys (∷-tail-inj p) b1<b2
  ... | gt y<x = lift $ 𝒟.irrefl (𝒟.≡-transl (∷-head-inj p) y<x)

  merge-list≤→base≤ : ∀ b1 xs b2 ys → merge-list≤ b1 xs b2 ys → b1 ≤ b2
  merge-list≤→base≤ b1 [] b2 [] xs≤ys = xs≤ys
  merge-list≤→base≤ b1 [] b2 (y ∷ ys) xs≤ys with cmp b1 y
  ... | lt _ = merge-list≤→base≤ b1 [] b2 ys xs≤ys
  ... | eq _ = merge-list≤→base≤ b1 [] b2 ys xs≤ys
  merge-list≤→base≤ b1 (x ∷ xs) b2 [] xs≤ys with cmp x b2
  ... | lt _ = merge-list≤→base≤ b1 xs b2 [] xs≤ys
  ... | eq _ = merge-list≤→base≤ b1 xs b2 [] xs≤ys
  merge-list≤→base≤ b1 (x ∷ xs) b2 (y ∷ ys) xs≤ys with cmp x y
  ... | lt _ = merge-list≤→base≤ b1 xs b2 ys xs≤ys
  ... | eq _ = merge-list≤→base≤ b1 xs b2 ys xs≤ys

  merge-list≤-is-prop : ∀ b1 xs b2 ys → is-prop (merge-list≤ b1 xs b2 ys)
  merge-list≤-is-prop b1 [] b2 [] = hlevel 1
  merge-list≤-is-prop b1 [] b2 (y ∷ ys) with cmp b1 y
  ... | lt _ = merge-list≤-is-prop b1 [] b2 ys
  ... | eq _ = merge-list≤-is-prop b1 [] b2 ys
  ... | gt _ = hlevel 1
  merge-list≤-is-prop b1 (x ∷ xs) b2 [] with cmp x b2
  ... | lt _ = merge-list≤-is-prop b1 xs b2 []
  ... | eq _ = merge-list≤-is-prop b1 xs b2 []
  ... | gt _ = hlevel 1
  merge-list≤-is-prop b1 (x ∷ xs) b2 (y ∷ ys) with cmp x y
  ... | lt _ = merge-list≤-is-prop b1 xs b2 ys
  ... | eq _ = merge-list≤-is-prop b1 xs b2 ys
  ... | gt _ = hlevel 1

  merge-list<-is-prop : ∀ b1 xs b2 ys → is-prop (merge-list< b1 xs b2 ys)
  merge-list<-is-prop b1 [] b2 [] = hlevel 1
  merge-list<-is-prop b1 [] b2 (y ∷ ys) with cmp b1 y
  ... | lt _ = merge-list≤-is-prop b1 [] b2 ys
  ... | eq _ = merge-list<-is-prop b1 [] b2 ys
  ... | gt _ = hlevel 1
  merge-list<-is-prop b1 (x ∷ xs) b2 [] with cmp x b2
  ... | lt _ = merge-list≤-is-prop b1 xs b2 []
  ... | eq _ = merge-list<-is-prop b1 xs b2 []
  ... | gt _ = hlevel 1
  merge-list<-is-prop b1 (x ∷ xs) b2 (y ∷ ys) with cmp x y
  ... | lt _ = merge-list≤-is-prop b1 xs b2 ys
  ... | eq _ = merge-list<-is-prop b1 xs b2 ys
  ... | gt _ = hlevel 1

  -- Computational helpers for merge-list≤ and merge-list<
  merge-list≤-step≤ : ∀ b1 xs b2 ys {x y} → x ≤ y → merge-list≤ b1 xs b2 ys → tri-rec (merge-list≤ b1 xs b2 ys) (merge-list≤ b1 xs b2 ys) (Lift _ ⊥) (cmp x y)
  merge-list≤-step≤ _ _ _ _ {x = x} {y = y} (inl x≡y) pf with cmp x y
  ... | lt _ = pf
  ... | eq _ = pf
  ... | gt y<x = lift (𝒟.irrefl (𝒟.≡-transl x≡y y<x))
  merge-list≤-step≤ _ _ _ _ {x = x} {y = y} (inr x<y) pf with cmp x y 
  ... | lt _ = pf
  ... | eq _ = pf
  ... | gt y<x = lift (𝒟.asym x<y y<x)

  merge-list<-step< : ∀ b1 xs b2 ys {x y} → x < y → merge-list≤ b1 xs b2 ys → tri-rec (merge-list≤ b1 xs b2 ys) (merge-list< b1 xs b2 ys) (Lift _ ⊥) (cmp x y)
  merge-list<-step< _ _ _ _ {x = x} {y = y} x<y pf with cmp x y 
  ... | lt _ = pf
  ... | eq x≡y = absurd (𝒟.irrefl (𝒟.≡-transl (sym x≡y) x<y))
  ... | gt y<x = lift (𝒟.asym x<y y<x)

  merge-list<-step≡ : ∀ b1 xs b2 ys {x y} → x ≡ y → merge-list< b1 xs b2 ys → tri-rec (merge-list≤ b1 xs b2 ys) (merge-list< b1 xs b2 ys) (Lift _ ⊥) (cmp x y)
  merge-list<-step≡ _ _ _ _ {x = x} {y = y} x≡y pf with cmp x y 
  ... | lt x<y = absurd (𝒟.irrefl (𝒟.≡-transl (sym x≡y) x<y))
  ... | eq _ = pf
  ... | gt y<x = lift (𝒟.irrefl (𝒟.≡-transl x≡y y<x))

  merge-list≤-vanish : ∀ b xs → vanishes b xs → merge-list≤ b xs b []
  merge-list≤-vanish b [] vanish = inl refl
  merge-list≤-vanish b (x ∷ xs) vanish =
    merge-list≤-step≤ b xs b []
      (inl (vanish-head-∷ b x xs vanish))
      (merge-list≤-vanish b xs (vanish-tail-∷ b x xs vanish))

  merge-list≥-vanish : ∀ b xs → vanishes b xs → merge-list≤ b [] b xs
  merge-list≥-vanish b [] vanish = inl refl
  merge-list≥-vanish b (x ∷ xs) vanish =
    merge-list≤-step≤ b [] b xs
      (inl (sym $ vanish-head-∷ b x xs vanish))
      (merge-list≥-vanish b xs (vanish-tail-∷ b x xs vanish))

  merge-list≤-++-vanish : ∀ b xs ys → vanishes b ys → merge-list≤ b (xs ++ ys) b xs
  merge-list≤-++-vanish b [] ys ys-vanish = merge-list≤-vanish b ys ys-vanish
  merge-list≤-++-vanish b (x ∷ xs) ys ys-vanish with cmp x x
  ... | lt x<x = absurd $ 𝒟.irrefl x<x
  ... | eq x≡x = merge-list≤-++-vanish b xs ys ys-vanish
  ... | gt x<x = absurd $ 𝒟.irrefl x<x

  merge-list≥-++-vanish : ∀ b xs ys → vanishes b ys → merge-list≤ b xs b (xs ++ ys)
  merge-list≥-++-vanish b [] ys ys-vanish = merge-list≥-vanish b ys ys-vanish
  merge-list≥-++-vanish b (x ∷ xs) ys ys-vanish with cmp x x
  ... | lt x<x = absurd $ 𝒟.irrefl x<x
  ... | eq x≡x = merge-list≥-++-vanish b xs ys ys-vanish
  ... | gt x<x = absurd $ 𝒟.irrefl x<x

  merge-list≤-⊗▷-vanish : ∀ b xs ys → vanishes b ys → merge-list≤ b (xs ⊗▷ ys) b (fwd xs)
  merge-list≤-⊗▷-vanish b xs ys ys-vanish =
    subst (λ ϕ → merge-list≤ b ϕ b (fwd xs))
      (sym $ ⊗▷-fwd xs ys)
      (merge-list≤-++-vanish b (fwd xs) ys ys-vanish)

  merge-list≥-⊗▷-vanish : ∀ b xs ys → vanishes b ys → merge-list≤ b (fwd xs) b (xs ⊗▷ ys)
  merge-list≥-⊗▷-vanish b xs ys ys-vanish =
    subst (λ ϕ → merge-list≤ b (fwd xs) b ϕ)
      (sym $ ⊗▷-fwd xs ys)
      (merge-list≥-++-vanish b (fwd xs) ys ys-vanish)

  weaken-< : ∀ b1 xs b2 ys → merge-list< b1 xs b2 ys → merge-list≤ b1 xs b2 ys
  weaken-< b1 [] b2 [] (lift b1<b2) = inr b1<b2
  weaken-< b1 [] b2 (y ∷ ys) xs<ys with cmp b1 y
  ... | lt _ = xs<ys
  ... | eq _ = weaken-< b1 [] b2 ys xs<ys
  ... | gt _ = xs<ys
  weaken-< b1 (x ∷ xs) b2 [] xs<ys with cmp x b2
  ... | lt _ = xs<ys
  ... | eq _ = weaken-< b1 xs b2 [] xs<ys
  weaken-< b1 (x ∷ xs) b2 (y ∷ ys) xs<ys with cmp x y
  ... | lt _ = xs<ys
  ... | eq _ = weaken-< b1 xs b2 ys xs<ys

  merge-list≤-refl : ∀ b xs → merge-list≤ b xs b xs
  merge-list≤-refl b [] = inl refl
  merge-list≤-refl b (x ∷ xs) with cmp x x
  ... | lt x<x = absurd $ 𝒟.irrefl x<x
  ... | eq x≡x = merge-list≤-refl b xs
  ... | gt x<x = absurd $ 𝒟.irrefl x<x

  merge-list<-irrefl : ∀ b xs → merge-list< b xs b xs → ⊥
  merge-list<-irrefl b [] (lift b<b) = 𝒟.irrefl b<b
  merge-list<-irrefl b (x ∷ xs) xs<xs with cmp x x
  ... | lt x<x = 𝒟.irrefl x<x
  ... | eq x≡x = merge-list<-irrefl b xs xs<xs

  merge-list≤-trans : ∀ b1 xs b2 ys b3 zs → merge-list≤ b1 xs b2 ys → merge-list≤ b2 ys b3 zs → merge-list≤ b1 xs b3 zs
  merge-list≤-trans b1 xs b2 ys b3 zs = go xs ys zs
    where
      go : ∀ xs ys zs → merge-list≤ b1 xs b2 ys → merge-list≤ b2 ys b3 zs → merge-list≤ b1 xs b3 zs
      go [] [] [] b1≤b2 b2≤b3 =
        𝒟.≤-trans b1≤b2 b2≤b3
      go [] [] (z ∷ zs) b1≤b2 ys≤zs with cmp b2 z
      ... | lt b2<z = merge-list≤-step≤ b1 [] b3 zs (𝒟.≤-trans b1≤b2 (inr b2<z)) (go [] [] zs b1≤b2 ys≤zs)
      ... | eq b2≡z = merge-list≤-step≤ b1 [] b3 zs (𝒟.≤-trans b1≤b2 (inl b2≡z)) (go [] [] zs b1≤b2 ys≤zs)
      go [] (y ∷ ys) [] xs≤ys ys≤zs with cmp b1 y | cmp y b3
      ... | lt b1<y | lt y<b3 = inr (𝒟.trans b1<y y<b3)
      ... | lt b1<y | eq y≡b3 = inr (𝒟.≡-transr b1<y y≡b3)
      ... | eq b1≡y | lt y<b3 = inr (𝒟.≡-transl b1≡y y<b3)
      ... | eq b1≡y | eq y≡b3 = inl (b1≡y ∙ y≡b3)
      go [] (y ∷ ys) (z ∷ zs) xs≤ys ys≤zs with cmp b1 y | cmp y z
      ... | lt b1<y | lt y<z = merge-list≤-step≤ b1 [] b3 zs (inr (𝒟.trans b1<y y<z)) (go [] ys zs xs≤ys ys≤zs)
      ... | lt b1<y | eq y≡z = merge-list≤-step≤ b1 [] b3 zs (inr (𝒟.≡-transr b1<y y≡z)) (go [] ys zs xs≤ys ys≤zs)
      ... | eq b1≡y | lt y<z = merge-list≤-step≤ b1 [] b3 zs (inr (𝒟.≡-transl b1≡y y<z)) (go [] ys zs xs≤ys ys≤zs)
      ... | eq b1≡y | eq y≡z = merge-list≤-step≤ b1 [] b3 zs (inl (b1≡y ∙ y≡z)) (go [] ys zs xs≤ys ys≤zs)
      go (x ∷ xs) [] [] xs≤ys b2≤b3 with cmp x b2
      ... | lt x<b2 = merge-list≤-step≤ b1 xs b3 [] (𝒟.≤-trans (inr x<b2) b2≤b3) (go xs [] [] xs≤ys b2≤b3)
      ... | eq x≡b2 = merge-list≤-step≤ b1 xs b3 [] (𝒟.≤-trans (inl x≡b2) b2≤b3) (go xs [] [] xs≤ys b2≤b3)
      go (x ∷ xs) [] (z ∷ zs) xs≤ys ys≤zs with cmp x b2 | cmp b2 z
      ... | lt x<b2 | lt b2<z = merge-list≤-step≤ b1 xs b3 zs (inr (𝒟.trans x<b2 b2<z)) (go xs [] zs xs≤ys ys≤zs)
      ... | lt x<b2 | eq b2≡z = merge-list≤-step≤ b1 xs b3 zs (inr (𝒟.≡-transr x<b2 b2≡z)) (go xs [] zs xs≤ys ys≤zs)
      ... | eq x≡b2 | lt b2<z = merge-list≤-step≤ b1 xs b3 zs (inr (𝒟.≡-transl x≡b2 b2<z)) (go xs [] zs xs≤ys ys≤zs)
      ... | eq x≡b2 | eq b2≡z = merge-list≤-step≤ b1 xs b3 zs (inl (x≡b2 ∙ b2≡z)) (go xs [] zs xs≤ys ys≤zs)
      go (x ∷ xs) (y ∷ ys) [] xs≤ys ys≤zs with cmp x y | cmp y b3
      ... | lt x<y | lt y<b3 = merge-list≤-step≤ b1 xs b3 [] (inr (𝒟.trans x<y y<b3)) (go xs ys [] xs≤ys ys≤zs)
      ... | lt x<y | eq y≡b3 = merge-list≤-step≤ b1 xs b3 [] (inr (𝒟.≡-transr x<y y≡b3)) (go xs ys [] xs≤ys ys≤zs)
      ... | eq x≡y | lt y<b3 = merge-list≤-step≤ b1 xs b3 [] (inr (𝒟.≡-transl x≡y y<b3)) (go xs ys [] xs≤ys ys≤zs)
      ... | eq x≡y | eq y≡b3 = merge-list≤-step≤ b1 xs b3 [] (inl (x≡y ∙ y≡b3)) (go xs ys [] xs≤ys ys≤zs)
      go (x ∷ xs) (y ∷ ys) (z ∷ zs) xs≤ys ys≤zs with cmp x y | cmp y z
      ... | lt x<y | lt y<z = merge-list≤-step≤ b1 xs b3 zs (inr (𝒟.trans x<y y<z)) (go xs ys zs xs≤ys ys≤zs)
      ... | lt x<y | eq y≡z = merge-list≤-step≤ b1 xs b3 zs (inr (𝒟.≡-transr x<y y≡z)) (go xs ys zs xs≤ys ys≤zs)
      ... | eq x≡y | lt y<z = merge-list≤-step≤ b1 xs b3 zs (inr (𝒟.≡-transl x≡y y<z)) (go xs ys zs xs≤ys ys≤zs)
      ... | eq x≡y | eq y≡z = merge-list≤-step≤ b1 xs b3 zs (inl (x≡y ∙ y≡z)) (go xs ys zs xs≤ys ys≤zs)

  merge-list<-trans : ∀ b1 xs b2 ys b3 zs → merge-list< b1 xs b2 ys → merge-list< b2 ys b3 zs → merge-list< b1 xs b3 zs
  merge-list<-trans b1 xs b2 ys b3 zs = go xs ys zs
    where
      go≤ : ∀ xs ys zs → merge-list≤ b1 xs b2 ys → merge-list≤ b2 ys b3 zs → merge-list≤ b1 xs b3 zs
      go≤ xs ys zs = merge-list≤-trans b1 xs b2 ys b3 zs

      go : ∀ xs ys zs → merge-list< b1 xs b2 ys → merge-list< b2 ys b3 zs → merge-list< b1 xs b3 zs
      go [] [] [] (lift b1<b2) (lift b2<b3) =
        lift (𝒟.trans b1<b2 b2<b3)
      go [] [] (z ∷ zs) (lift b1<b2) ys<zs with cmp b2 z
      ... | lt b2<z = merge-list<-step< b1 [] b3 zs (𝒟.trans b1<b2 b2<z) (go≤ [] [] zs (inr b1<b2) ys<zs)
      ... | eq b2≡z = merge-list<-step< b1 [] b3 zs (𝒟.≡-transr b1<b2 b2≡z) (go≤ [] [] zs (inr b1<b2) (weaken-< b2 [] b3 zs ys<zs))
      go [] (y ∷ ys) [] xs<ys ys<zs with cmp b1 y | cmp y b3
      ... | lt b1<y | lt y<b3 = lift (𝒟.trans b1<y y<b3)
      ... | lt b1<y | eq y≡b3 = lift (𝒟.≡-transr b1<y y≡b3)
      ... | eq b1≡y | lt y<b3 = lift (𝒟.≡-transl b1≡y y<b3)
      ... | eq b1≡y | eq y≡b3 = merge-list<-trans b1 [] b2 ys b3 [] xs<ys ys<zs
      go [] (y ∷ ys) (z ∷ zs) xs<ys ys<zs with cmp b1 y | cmp y z
      ... | lt b1<y | lt y<z = merge-list<-step< b1 [] b3 zs (𝒟.trans b1<y y<z) (go≤ [] ys zs xs<ys ys<zs)
      ... | lt b1<y | eq y≡z = merge-list<-step< b1 [] b3 zs (𝒟.≡-transr b1<y y≡z) (go≤ [] ys zs xs<ys (weaken-< b2 ys b3 zs ys<zs))
      ... | eq b1≡y | lt y<z = merge-list<-step< b1 [] b3 zs (𝒟.≡-transl b1≡y y<z) (go≤ [] ys zs (weaken-< b1 [] b2 ys xs<ys) ys<zs)
      ... | eq b1≡y | eq y≡z = merge-list<-step≡ b1 [] b3 zs (b1≡y ∙ y≡z) (go [] ys zs xs<ys ys<zs)
      go (x ∷ xs) [] [] xs<ys (lift b2<b3) with cmp x b2
      ... | lt x<b2 = merge-list<-step< b1 xs b3 [] (𝒟.trans x<b2 b2<b3) (go≤ xs [] [] xs<ys (inr b2<b3))
      ... | eq x≡b2 = merge-list<-step< b1 xs b3 [] (𝒟.≡-transl x≡b2 b2<b3) (go≤ xs [] [] (weaken-< b1 xs b2 [] xs<ys) (inr b2<b3))
      go (x ∷ xs) [] (z ∷ zs) xs<ys ys<zs with cmp x b2 | cmp b2 z
      ... | lt x<b2 | lt b2<z = merge-list<-step< b1 xs b3 zs (𝒟.trans x<b2 b2<z) (go≤ xs [] zs xs<ys ys<zs) 
      ... | lt x<b2 | eq b2≡z = merge-list<-step< b1 xs b3 zs (𝒟.≡-transr x<b2 b2≡z) (go≤ xs [] zs xs<ys (weaken-< b2 [] b3 zs ys<zs))  
      ... | eq x≡b2 | lt b2<z = merge-list<-step< b1 xs b3 zs (𝒟.≡-transl x≡b2 b2<z) (go≤ xs [] zs (weaken-< b1 xs b2 [] xs<ys) ys<zs)  
      ... | eq x≡b2 | eq b2≡z = merge-list<-step≡ b1 xs b3 zs (x≡b2 ∙ b2≡z) (go xs [] zs xs<ys ys<zs)  
      go (x ∷ xs) (y ∷ ys) [] xs<ys ys<zs with cmp x y | cmp y b3
      ... | lt x<y | lt y<b3 = merge-list<-step< b1 xs b3 [] (𝒟.trans x<y y<b3) (go≤ xs ys [] xs<ys ys<zs) 
      ... | lt x<y | eq y≡b3 = merge-list<-step< b1 xs b3 [] (𝒟.≡-transr x<y y≡b3) (go≤ xs ys [] xs<ys (weaken-< b2 ys b3 [] ys<zs)) 
      ... | eq x≡y | lt y<b3 = merge-list<-step< b1 xs b3 [] (𝒟.≡-transl x≡y y<b3) (go≤ xs ys [] (weaken-< b1 xs b2 ys xs<ys) ys<zs) 
      ... | eq x≡y | eq y≡b3 = merge-list<-step≡ b1 xs b3 [] (x≡y ∙ y≡b3) (go xs ys [] xs<ys ys<zs) 
      go (x ∷ xs) (y ∷ ys) (z ∷ zs) xs<ys ys<zs with cmp x y | cmp y z
      ... | lt x<y | lt y<z = merge-list<-step< b1 xs b3 zs (𝒟.trans x<y y<z) (go≤ xs ys zs xs<ys ys<zs) 
      ... | lt x<y | eq y≡z = merge-list<-step< b1 xs b3 zs (𝒟.≡-transr x<y y≡z) (go≤ xs ys zs xs<ys (weaken-< b2 ys b3 zs ys<zs)) 
      ... | eq x≡y | lt y<z = merge-list<-step< b1 xs b3 zs (𝒟.≡-transl x≡y y<z) (go≤ xs ys zs (weaken-< b1 xs b2 ys xs<ys) ys<zs) 
      ... | eq x≡y | eq y≡z = merge-list<-step≡ b1 xs b3 zs (x≡y ∙ y≡z) (go xs ys zs xs<ys ys<zs) 

  --------------------------------------------------------------------------------
  -- Heterogenous Compositions
  --
  -- These proofs may seem redundant but converting from 'merge-list≤' to 'non-strict merge-list<' doesn't quite work,
  -- due to the behaviour around the bases. In particular, this relies on compactness, and we want to use these results
  -- when we don't have compactness yet (for instance, showing that 'compact' is strictly monotonic).

  merge-list≤-transl : ∀ b1 xs b2 ys b3 zs → merge-list≤ b1 xs b2 ys → merge-list< b2 ys b3 zs → merge-list< b1 xs b3 zs
  merge-list≤-transl b1 xs b2 ys b3 zs = go xs ys zs
    where
      step< : ∀ xs ys zs {x z}
              → (x < z)
              → merge-list≤ b1 xs b2 ys
              → merge-list≤ b2 ys b3 zs
              → tri-rec
                (merge-list≤ b1 xs b3 zs)
                (merge-list< b1 xs b3 zs)
                (Lift (o ⊔ r) ⊥)
                (cmp x z)
      step< xs ys zs x<z xs≤ys ys≤zs =
        merge-list<-step< b1 xs b3 zs x<z (merge-list≤-trans b1 xs b2 ys b3 zs xs≤ys ys≤zs)

      step≤ : ∀ xs ys zs {x z}
              → (x ≤ z)
              → merge-list≤ b1 xs b2 ys
              → merge-list< b2 ys b3 zs
              → tri-rec
                (merge-list≤ b1 xs b3 zs)
                (merge-list< b1 xs b3 zs)
                (Lift (o ⊔ r) ⊥)
                (cmp x z)
      step≤ xs ys zs (inl x≡z) xs≤ys ys<zs =
        merge-list<-step≡ b1 xs b3 zs x≡z (merge-list≤-transl b1 xs b2 ys b3 zs xs≤ys ys<zs)
      step≤ xs ys zs (inr x<z) xs≤ys ys<zs =
        merge-list<-step< b1 xs b3 zs x<z (merge-list≤-trans b1 xs b2 ys b3 zs xs≤ys (weaken-< b2 ys b3 zs ys<zs))

      go : ∀ xs ys zs → merge-list≤ b1 xs b2 ys → merge-list< b2 ys b3 zs → merge-list< b1 xs b3 zs
      go [] [] [] b1≤b2 (lift b2<b3) =
        lift (𝒟.≤-transl b1≤b2 b2<b3)
      go [] [] (z ∷ zs) b1≤b2 ys<zs with cmp b2 z
      ... | lt b2<z = step< [] [] zs (𝒟.≤-transl b1≤b2 b2<z) b1≤b2 ys<zs
      ... | eq b2≡z = step≤ [] [] zs (𝒟.≤-trans b1≤b2 (inl b2≡z)) b1≤b2 ys<zs
      go [] (y ∷ ys) [] xs≤ys ys<zs with cmp b1 y | cmp y b3
      ... | lt b1<y | lt y<b3 = lift (𝒟.trans b1<y y<b3)
      ... | lt b1<y | eq y≡b3 = lift (𝒟.≡-transr b1<y y≡b3)
      ... | eq b1≡y | lt y<b3 = lift (𝒟.≡-transl b1≡y y<b3)
      ... | eq b1≡y | eq y≡b3 = go [] ys [] xs≤ys ys<zs
      go [] (y ∷ ys) (z ∷ zs) xs≤ys ys<zs with cmp b1 y | cmp y z
      ... | lt b1<y | lt y<z = step< [] ys zs (𝒟.trans b1<y y<z) xs≤ys ys<zs
      ... | lt b1<y | eq y≡z = step< [] ys zs (𝒟.≡-transr b1<y y≡z) xs≤ys (weaken-< b2 ys b3 zs ys<zs)
      ... | eq b1≡y | lt y<z = step< [] ys zs (𝒟.≡-transl b1≡y y<z) xs≤ys ys<zs
      ... | eq b1≡y | eq y≡z = step≤ [] ys zs (inl (b1≡y ∙ y≡z)) xs≤ys ys<zs
      go (x ∷ xs) [] [] xs≤ys (lift b2<b3) with cmp x b2
      ... | lt x<b2 = step< xs [] [] (𝒟.trans x<b2 b2<b3) xs≤ys (inr b2<b3)
      ... | eq x≡b2 = step< xs [] [] (𝒟.≡-transl x≡b2 b2<b3) xs≤ys (inr b2<b3)
      go (x ∷ xs) [] (z ∷ zs) xs≤ys ys<zs with cmp x b2 | cmp b2 z
      ... | lt x<b2 | lt b2<z = step< xs [] zs (𝒟.trans x<b2 b2<z) xs≤ys ys<zs
      ... | lt x<b2 | eq b2≡z = step< xs [] zs (𝒟.≡-transr x<b2 b2≡z) xs≤ys (weaken-< b2 [] b3 zs ys<zs) 
      ... | eq x≡b2 | lt b2<z = step< xs [] zs (𝒟.≡-transl x≡b2 b2<z) xs≤ys ys<zs
      ... | eq x≡b2 | eq b2≡z = step≤ xs [] zs (inl (x≡b2 ∙ b2≡z)) xs≤ys ys<zs
      go (x ∷ xs) (y ∷ ys) [] xs≤ys ys<zs with cmp x y | cmp y b3
      ... | lt x<y | lt y<b3 = step< xs ys [] (𝒟.trans x<y y<b3) xs≤ys ys<zs
      ... | lt x<y | eq y≡b3 = step< xs ys [] (𝒟.≡-transr x<y y≡b3) xs≤ys (weaken-< b2 ys b3 [] ys<zs)
      ... | eq x≡y | lt y<b3 = step< xs ys [] (𝒟.≡-transl x≡y y<b3) xs≤ys ys<zs
      ... | eq x≡y | eq y≡b3 = step≤ xs ys [] (inl (x≡y ∙ y≡b3)) xs≤ys ys<zs
      go (x ∷ xs) (y ∷ ys) (z ∷ zs) xs≤ys ys<zs with cmp x y | cmp y z
      ... | lt x<y | lt y<z = step< xs ys zs (𝒟.trans x<y y<z) xs≤ys ys<zs
      ... | lt x<y | eq y≡z = step< xs ys zs (𝒟.≡-transr x<y y≡z) xs≤ys (weaken-< b2 ys b3 zs ys<zs)
      ... | eq x≡y | lt y<z = step< xs ys zs (𝒟.≡-transl x≡y y<z) xs≤ys ys<zs
      ... | eq x≡y | eq y≡z = step≤ xs ys zs (inl (x≡y ∙ y≡z)) xs≤ys ys<zs

  merge-list≤-transr : ∀ b1 xs b2 ys b3 zs → merge-list< b1 xs b2 ys → merge-list≤ b2 ys b3 zs → merge-list< b1 xs b3 zs
  merge-list≤-transr b1 xs b2 ys b3 zs = go xs ys zs
    where
      step< : ∀ xs ys zs {x z}
              → (x < z)
              → merge-list≤ b1 xs b2 ys
              → merge-list≤ b2 ys b3 zs
              → tri-rec
                (merge-list≤ b1 xs b3 zs)
                (merge-list< b1 xs b3 zs)
                (Lift (o ⊔ r) ⊥)
                (cmp x z)
      step< xs ys zs x<z xs≤ys ys≤zs =
        merge-list<-step< b1 xs b3 zs x<z (merge-list≤-trans b1 xs b2 ys b3 zs xs≤ys ys≤zs)

      step≤ : ∀ xs ys zs {x z}
              → (x ≤ z)
              → merge-list< b1 xs b2 ys
              → merge-list≤ b2 ys b3 zs
              → tri-rec
                (merge-list≤ b1 xs b3 zs)
                (merge-list< b1 xs b3 zs)
                (Lift (o ⊔ r) ⊥)
                (cmp x z)
      step≤ xs ys zs (inl x≡z) xs≤ys ys<zs =
        merge-list<-step≡ b1 xs b3 zs x≡z (merge-list≤-transr b1 xs b2 ys b3 zs xs≤ys ys<zs)
      step≤ xs ys zs (inr x<z) xs<ys ys≤zs =
        merge-list<-step< b1 xs b3 zs x<z (merge-list≤-trans b1 xs b2 ys b3 zs (weaken-< b1 xs b2 ys xs<ys) ys≤zs)

      go : ∀ xs ys zs → merge-list< b1 xs b2 ys → merge-list≤ b2 ys b3 zs → merge-list< b1 xs b3 zs
      go [] [] [] (lift b1<b2) b2≤b3 =
        lift (𝒟.≤-transr b1<b2 b2≤b3)
      go [] [] (z ∷ zs) (lift b1<b2) ys<zs with cmp b2 z
      ... | lt b2<z = step< [] [] zs (𝒟.trans b1<b2 b2<z) (inr b1<b2) ys<zs
      ... | eq b2≡z = step≤ [] [] zs (inr (𝒟.≡-transr b1<b2 b2≡z)) (lift b1<b2) ys<zs
      go [] (y ∷ ys) [] xs≤ys ys<zs with cmp b1 y | cmp y b3
      ... | lt b1<y | lt y<b3 = lift (𝒟.trans b1<y y<b3)
      ... | lt b1<y | eq y≡b3 = lift (𝒟.≡-transr b1<y y≡b3)
      ... | eq b1≡y | lt y<b3 = lift (𝒟.≡-transl b1≡y y<b3)
      ... | eq b1≡y | eq y≡b3 = go [] ys [] xs≤ys ys<zs
      go [] (y ∷ ys) (z ∷ zs) xs≤ys ys<zs with cmp b1 y | cmp y z
      ... | lt b1<y | lt y<z = step< [] ys zs (𝒟.trans b1<y y<z) xs≤ys ys<zs
      ... | lt b1<y | eq y≡z = step< [] ys zs (𝒟.≡-transr b1<y y≡z) xs≤ys ys<zs
      ... | eq b1≡y | lt y<z = step< [] ys zs (𝒟.≡-transl b1≡y y<z) (weaken-< b1 [] b2 ys xs≤ys) ys<zs
      ... | eq b1≡y | eq y≡z = step≤ [] ys zs (inl (b1≡y ∙ y≡z)) xs≤ys ys<zs
      go (x ∷ xs) [] [] xs<ys b2≤b3 with cmp x b2
      ... | lt x<b2 = step< xs [] [] (𝒟.≤-transr x<b2 b2≤b3) xs<ys b2≤b3
      ... | eq x≡b2 = step≤ xs [] [] (𝒟.≤-trans (inl x≡b2) b2≤b3) xs<ys b2≤b3
      go (x ∷ xs) [] (z ∷ zs) xs≤ys ys<zs with cmp x b2 | cmp b2 z
      ... | lt x<b2 | lt b2<z = step< xs [] zs (𝒟.trans x<b2 b2<z) xs≤ys ys<zs
      ... | lt x<b2 | eq b2≡z = step< xs [] zs (𝒟.≡-transr x<b2 b2≡z) xs≤ys ys<zs
      ... | eq x≡b2 | lt b2<z = step< xs [] zs (𝒟.≡-transl x≡b2 b2<z) (weaken-< b1 xs b2 [] xs≤ys) ys<zs
      ... | eq x≡b2 | eq b2≡z = step≤ xs [] zs (inl (x≡b2 ∙ b2≡z)) xs≤ys ys<zs
      go (x ∷ xs) (y ∷ ys) [] xs≤ys ys<zs with cmp x y | cmp y b3
      ... | lt x<y | lt y<b3 = step< xs ys [] (𝒟.trans x<y y<b3) xs≤ys ys<zs
      ... | lt x<y | eq y≡b3 = step< xs ys [] (𝒟.≡-transr x<y y≡b3) xs≤ys ys<zs
      ... | eq x≡y | lt y<b3 = step< xs ys [] (𝒟.≡-transl x≡y y<b3) (weaken-< b1 xs b2 ys xs≤ys) ys<zs
      ... | eq x≡y | eq y≡b3 = step≤ xs ys [] (inl (x≡y ∙ y≡b3)) xs≤ys ys<zs
      go (x ∷ xs) (y ∷ ys) (z ∷ zs) xs≤ys ys<zs with cmp x y | cmp y z
      ... | lt x<y | lt y<z = step< xs ys zs (𝒟.trans x<y y<z) xs≤ys ys<zs
      ... | lt x<y | eq y≡z = step< xs ys zs (𝒟.≡-transr x<y y≡z) xs≤ys ys<zs
      ... | eq x≡y | lt y<z = step< xs ys zs (𝒟.≡-transl x≡y y<z) (weaken-< b1 xs b2 ys xs≤ys) ys<zs
      ... | eq x≡y | eq y≡z = step≤ xs ys zs (inl (x≡y ∙ y≡z)) xs≤ys ys<zs

  _merge<_ : SupportList → SupportList → Type (o ⊔ r)
  xs merge< ys = merge-list< (xs .base) (list xs) (ys .base) (list ys)

  _merge≤_ : SupportList → SupportList → Type (o ⊔ r)
  xs merge≤ ys = merge-list≤ (xs .base) (list xs) (ys .base) (list ys)

  merge-is-strict-order : is-strict-order _merge<_
  merge-is-strict-order .is-strict-order.irrefl {xs} =
    merge-list<-irrefl (xs .base) (list xs)
  merge-is-strict-order .is-strict-order.trans {xs} {ys} {zs} =
    merge-list<-trans (xs .base) (list xs) (ys .base) (list ys) (zs .base) (list zs)
  merge-is-strict-order .is-strict-order.has-prop {xs} {ys} =
    merge-list<-is-prop (xs .base) (list xs) (ys .base) (list ys)

  --------------------------------------------------------------------------------
  -- Converting between non-strict and the nice ≤

  non-strict→merge≤ : ∀ xs ys → non-strict _merge<_ xs ys → xs merge≤ ys
  non-strict→merge≤ xs ys (inl xs≡ys) = subst (xs merge≤_) xs≡ys (merge-list≤-refl (xs .base) (list xs))
  non-strict→merge≤ xs ys (inr xs<ys) = weaken-< (xs .base) (list xs) (ys .base) (list ys) xs<ys

  merge≤→non-strict : ∀ xs ys → xs merge≤ ys → non-strict _merge<_ xs ys
  merge≤→non-strict xs ys xs≤ys =
    -- This subst is required due to issues with with-abstraction.
    -- In order to get the merge-list≤ to compute, we need to induct
    -- on lists. Trying to with-abstract and induct on 'list xs' and 'list ys'
    -- causes termination issues; therefore, we need to factor things out into
    -- a helper function. However, this causes the goal to be off by a bwd-fwd,
    -- requiring the following big subst.
    -- Again, Ouch!
    let xs′-compact = subst (is-compact (xs .base)) (sym $ bwd-fwd (xs .elts)) (xs .compacted)
        ys′-compact = subst (is-compact (ys .base)) (sym $ bwd-fwd (ys .elts)) (ys .compacted)
    in subst₂ (λ ϕ ψ → ϕ ≡ ψ ⊎ merge-list< (xs .base) (list xs) (ys .base) (list ys))
       (support-list-path refl (bwd-fwd (xs .elts)))
       (support-list-path refl (bwd-fwd (ys .elts))) $
       go (xs .base) (list xs) (ys .base) (list ys) xs′-compact ys′-compact xs≤ys
    where
      go : ∀ b1 xs b2 ys
           → (xs-compact : is-compact b1 (bwd xs))
           → (ys-compact : is-compact b2 (bwd ys))
           → merge-list≤ b1 xs b2 ys
           → support-list b1 (bwd xs) xs-compact ≡ support-list b2 (bwd ys) ys-compact ⊎ merge-list< b1 xs b2 ys
      go b1 [] b2 [] xs-compact ys-compact (inl b1≡b2) = inl $ support-list-path b1≡b2 refl
      go b1 [] b2 [] xs-compact ys-compact (inr b1<b2) = inr (lift b1<b2)
      go b1 [] b2 (y ∷ ys) xs-compact ys-compact xs≤ys with cmp b1 y
      ... | lt b1<y = inr xs≤ys
      ... | eq b1≡y =
        -- This is done to avoid yet another helper function.
        go b1 [] b2 ys xs-compact (is-compact-tail y ys b2 ys-compact) xs≤ys
        |> ⊎-mapl $ λ p →
          let ys≡[] : ys ≡ []
              ys≡[] = bwd-inj $ ap elts (sym p)
              
              b1≡b2 : b1 ≡ b2
              b1≡b2 = ap base p

              ¬y≡b2 : y ≡ b2 → ⊥
              ¬y≡b2 y≡b2 = base-isnt-compact-∷ ys≡[] y≡b2 ys-compact
          in absurd $ ¬y≡b2 $ (sym b1≡y) ∙ b1≡b2
      go b1 (x ∷ xs) b2 [] xs-compact ys-compact xs≤ys with cmp x b2
      ... | lt x<b2 = inr xs≤ys
      ... | eq x≡b2 =
        go b1 xs b2 [] (is-compact-tail x xs b1 xs-compact) ys-compact xs≤ys
        |> ⊎-mapl $ λ p →
          let xs≡[] : xs ≡ []
              xs≡[] = bwd-inj $ ap elts p
              
              b1≡b2 : b1 ≡ b2
              b1≡b2 = ap base p

              ¬x≡b1 : x ≡ b1 → ⊥
              ¬x≡b1 x≡b1 = base-isnt-compact-∷ xs≡[] x≡b1 xs-compact
          in absurd $ ¬x≡b1 $ x≡b2 ∙ sym b1≡b2
      go b1 (x ∷ xs) b2 (y ∷ ys) xs-compact ys-compact xs≤ys with cmp x y
      ... | lt x<y = inr xs≤ys
      ... | eq x≡y =
        go b1 xs b2 ys (is-compact-tail x xs b1 xs-compact) (is-compact-tail y ys b2 ys-compact) xs≤ys
        |> ⊎-mapl $ λ p →
          let xs≡ys : xs ≡ ys
              xs≡ys = bwd-inj $ ap elts p

              b1≡b2 : b1 ≡ b2
              b1≡b2 = ap base p
          in support-list-path b1≡b2 (ap bwd (ap₂ _∷_ x≡y xs≡ys))

  --------------------------------------------------------------------------------
  -- Compaction + Orderings

  compact-≤ : ∀ b xs → merge-list≤ b (fwd xs) b (fwd (compact b xs))
  compact-≤ b [] =
    inl refl
  compact-≤ b (xs #r x) with x ≡? b
  ... | yes x≡b =
    merge-list≤-trans
      b (xs ⊗▷ (x ∷ []))
      b (fwd xs)
      b (fwd (compact b xs))
      (merge-list≤-⊗▷-vanish b xs (x ∷ []) (vanish-step b x [] x≡b tt))
      (compact-≤ b xs)
  ... | no ¬x≡b =
    merge-list≤-refl b (fwd (xs #r x))

  compact-≥ : ∀ b xs → merge-list≤ b (fwd (compact b xs)) b (fwd xs)
  compact-≥ b [] =
    inl refl
  compact-≥ b (xs #r x) with x ≡? b
  ... | yes x≡b =
    merge-list≤-trans
      b (fwd (compact b xs))
      b (fwd xs)
      b (xs ⊗▷ (x ∷ []))
      (compact-≥ b xs)
      (merge-list≥-⊗▷-vanish b xs (x ∷ []) (vanish-step b x [] x≡b tt))
  ... | no ¬x≡b =
    merge-list≤-refl b (fwd (xs #r x))

  compact-mono-≤ : ∀ b1 xs b2 ys → merge-list≤ b1 xs b2 ys → merge-list≤ b1 (fwd (compact b1 (bwd xs))) b2 (fwd (compact b2 (bwd ys)))
  compact-mono-≤ b1 xs b2 ys xs≤ys =
    merge-list≤-trans
      b1 (fwd (compact b1 (bwd xs)))
      b1 (fwd (bwd xs))
      b2 (fwd (compact b2 (bwd ys)))
      (compact-≥ b1 (bwd xs)) $
    merge-list≤-trans
      b1 (fwd (bwd xs))
      b2 (fwd (bwd ys))
      b2 (fwd (compact b2 (bwd ys)))
      (subst₂ (λ ϕ ψ → merge-list≤ b1 ϕ b2 ψ) (sym $ fwd-bwd xs) (sym $ fwd-bwd ys) xs≤ys)
      (compact-≤ b2 (bwd ys))

  compact-mono-< : ∀ b1 xs b2 ys → merge-list< b1 xs b2 ys → merge-list< b1 (fwd (compact b1 (bwd xs))) b2 (fwd (compact b2 (bwd ys)))
  compact-mono-< b1 xs b2 ys xs<ys =
    merge-list≤-transl
      b1 (fwd (compact b1 (bwd xs)))
      b1 (fwd (bwd xs))
      b2 (fwd (compact b2 (bwd ys)))
      (compact-≥ b1 (bwd xs)) $
    merge-list≤-transr
      b1 (fwd (bwd xs))
      b2 (fwd (bwd ys))
      b2 (fwd (compact b2 (bwd ys)))
      (subst₂ (λ ϕ ψ → merge-list< b1 ϕ b2 ψ) (sym $ fwd-bwd xs) (sym $ fwd-bwd ys) xs<ys)
      (compact-≤ b2 (bwd ys))

  --------------------------------------------------------------------------------
  -- Left-Invariance

  merge-list≤-left-invariant : ∀ b1 xs b2 ys b3 zs → merge-list≤ b2 ys b3 zs → merge-list≤ (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs)
  merge-list≤-left-invariant b1 xs b2 ys b3 zs = go xs ys zs
    where
      -- We are going to be making a /lot/ of common recursive calls, so let's factor those
      -- out before doing the monster case bash.
      step≤ : ∀ xs ys zs {x y}
              → (x ≤ y)
              → merge-list≤ b2 ys b3 zs
              → tri-rec
                (merge-list≤ (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs))
                (merge-list≤ (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs))
                (Lift (o ⊔ r) ⊥)
                (cmp x y)
      step≤ xs ys zs x≤y xs≤ys =
        merge-list≤-step≤
          (b1 ⊗ b2) (merge-list b1 xs b2 ys)
          (b1 ⊗ b3) (merge-list b1 xs b3 zs)
          x≤y
          (merge-list≤-left-invariant b1 xs b2 ys b3 zs xs≤ys)

      go : ∀ xs ys zs → merge-list≤ b2 ys b3 zs → merge-list≤ (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs)
      go [] [] [] b2≤b3 =
        𝒟.left-invariant-≤ b2≤b3
      go [] [] (z ∷ zs) ys<zs with cmp b2 z
      ... | lt b2<z = step≤ [] [] zs (inr $ 𝒟.left-invariant b2<z) ys<zs
      ... | eq b2≡z = step≤ [] [] zs (inl $ ap (b1 ⊗_) b2≡z) ys<zs
      go [] (y ∷ ys) [] ys<zs with cmp y b3
      ... | lt y<b3 = step≤ [] ys [] (inr $ 𝒟.left-invariant y<b3) ys<zs
      ... | eq y≡b3 = step≤ [] ys [] (inl $ ap (b1 ⊗_) y≡b3) ys<zs
      go [] (y ∷ ys) (z ∷ zs) ys<zs with cmp y z
      ... | lt y<z = step≤ [] ys zs (inr $ 𝒟.left-invariant y<z) ys<zs
      ... | eq y≡z = step≤ [] ys zs (inl $ ap (b1 ⊗_) y≡z) ys<zs
      go (x ∷ xs) [] [] b2<b3 =
        step≤ xs [] [] (𝒟.left-invariant-≤ b2<b3) b2<b3
      go (x ∷ xs) [] (z ∷ zs) ys<zs with cmp b2 z
      ... | lt b2<z = step≤ xs [] zs (inr $ 𝒟.left-invariant b2<z) ys<zs
      ... | eq b2≡z = step≤ xs [] zs (inl $ ap (x ⊗_) b2≡z) ys<zs
      go (x ∷ xs) (y ∷ ys) [] ys<zs with cmp y b3
      ... | lt y<b3 = step≤ xs ys [] (inr $ 𝒟.left-invariant y<b3) ys<zs
      ... | eq y≡b3 = step≤ xs ys [] (inl $ ap (x ⊗_) y≡b3) ys<zs
      go (x ∷ xs) (y ∷ ys) (z ∷ zs) ys<zs with cmp y z
      ... | lt y<z = step≤ xs ys zs (inr $ 𝒟.left-invariant y<z) ys<zs
      ... | eq y≡z = step≤ xs ys zs (inl $ ap (x ⊗_) y≡z) ys<zs

  merge-list<-left-invariant : ∀ b1 xs b2 ys b3 zs → merge-list< b2 ys b3 zs → merge-list< (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs)
  merge-list<-left-invariant b1 xs b2 ys b3 zs = go xs ys zs
    where
      -- same idea as above: factor out the shape of the recursive calls.
      step< : ∀ xs ys zs {x y}
              → (x < y)
              → merge-list≤ b2 ys b3 zs
              → tri-rec
                (merge-list≤ (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs))
                (merge-list< (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs))
                (Lift (o ⊔ r) ⊥)
                (cmp x y)
      step< xs ys zs x<y ys≤zs =
        merge-list<-step<
          (b1 ⊗ b2) (merge-list b1 xs b2 ys)
          (b1 ⊗ b3) (merge-list b1 xs b3 zs)
          x<y
          (merge-list≤-left-invariant b1 xs b2 ys b3 zs ys≤zs)

      step≡ : ∀ xs ys zs {x y}
              → (x ≡ y)
              → merge-list< b2 ys b3 zs
              → tri-rec
                (merge-list≤ (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs))
                (merge-list< (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs))
                (Lift (o ⊔ r) ⊥)
                (cmp x y)
      step≡ xs ys zs x≡y ys<zs =
        merge-list<-step≡
          (b1 ⊗ b2) (merge-list b1 xs b2 ys)
          (b1 ⊗ b3) (merge-list b1 xs b3 zs)
          x≡y
          (merge-list<-left-invariant b1 xs b2 ys b3 zs ys<zs)

      go : ∀ xs ys zs → merge-list< b2 ys b3 zs → merge-list< (b1 ⊗ b2) (merge-list b1 xs b2 ys) (b1 ⊗ b3) (merge-list b1 xs b3 zs)
      go [] [] [] (lift b2<b3) =
        lift (𝒟.left-invariant b2<b3)
      go [] [] (z ∷ zs) ys<zs with cmp b2 z
      ... | lt b2<z = step< [] [] zs (𝒟.left-invariant b2<z) ys<zs
      ... | eq b2≡z = step≡ [] [] zs (ap (b1 ⊗_) b2≡z) ys<zs
      go [] (y ∷ ys) [] ys<zs with cmp y b3
      ... | lt y<b3 = step< [] ys [] (𝒟.left-invariant y<b3) ys<zs
      ... | eq y≡b3 = step≡ [] ys [] (ap (b1 ⊗_) y≡b3) ys<zs
      go [] (y ∷ ys) (z ∷ zs) ys<zs with cmp y z
      ... | lt y<z = step< [] ys zs (𝒟.left-invariant y<z) ys<zs
      ... | eq y≡z = step≡ [] ys zs (ap (b1 ⊗_) y≡z) ys<zs
      go (x ∷ xs) [] [] (lift b2<b3) =
        step< xs [] [] (𝒟.left-invariant b2<b3) (inr b2<b3)
      go (x ∷ xs) [] (z ∷ zs) ys<zs with cmp b2 z
      ... | lt b2<z = step< xs [] zs (𝒟.left-invariant b2<z) ys<zs
      ... | eq b2≡z = step≡ xs [] zs (ap (x ⊗_) b2≡z) ys<zs
      go (x ∷ xs) (y ∷ ys) [] ys<zs with cmp y b3
      ... | lt y<b3 = step< xs ys [] (𝒟.left-invariant y<b3) ys<zs
      ... | eq y≡b3 = step≡ xs ys [] (ap (x ⊗_) y≡b3) ys<zs
      go (x ∷ xs) (y ∷ ys) (z ∷ zs) ys<zs with cmp y z
      ... | lt y<z = step< xs ys zs (𝒟.left-invariant y<z) ys<zs
      ... | eq y≡z = step≡ xs ys zs (ap (x ⊗_) y≡z) ys<zs

  merge-left-invariant : ∀ xs ys zs → ys merge< zs → (merge xs ys) merge< (merge xs zs)
  merge-left-invariant xs ys zs ys<zs =
    compact-mono-<
      (xs .base ⊗ ys .base) (merge-list (xs .base) (list xs) (ys .base) (list ys))
      (xs .base ⊗ zs .base) (merge-list (xs .base) (list xs) (zs .base) (list zs))
      (merge-list<-left-invariant (xs .base) (list xs) (ys .base) (list ys) (zs .base) (list zs) ys<zs)

  merge-is-displacement-algebra : is-displacement-algebra _merge<_ empty merge
  merge-is-displacement-algebra .is-displacement-algebra.has-monoid = merge-is-monoid
  merge-is-displacement-algebra .is-displacement-algebra.has-strict-order = merge-is-strict-order
  merge-is-displacement-algebra .is-displacement-algebra.left-invariant {xs} {ys} {zs} = merge-left-invariant xs ys zs

  --------------------------------------------------------------------------------
  -- Indexing

  index : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → Nat → ⌞ 𝒟 ⌟
  index b [] n = b
  index b (x ∷ xs) zero = x
  index b (x ∷ xs) (suc n) = index b xs n

  index-vanishes : ∀ b xs n → vanishes b xs → index b xs n ≡ b
  index-vanishes b [] n vanishes = refl
  index-vanishes b (x ∷ xs) zero vanishes with x ≡? b
  ... | yes x≡b = x≡b
  index-vanishes b (x ∷ xs) (suc n) vanishes with x ≡? b
  ... | yes _ = index-vanishes b xs n vanishes

  index-compact : ∀ b xs n → index b (fwd (compact b (bwd xs))) n ≡ index b xs n
  index-compact b [] n = refl
  index-compact b (x ∷ xs) zero with x ≡? b
  ... | yes x≡b with inspect (compact b (bwd xs))
  ... | [] , p =
    index b (fwd (compact b (([] #r x) ◁⊗ xs))) 0 ≡⟨ ap (λ ϕ → index b (fwd ϕ) 0) (compact-◁⊗ ([] #r x) xs [] p) ⟩
    index b (fwd (compact b ([] #r x))) 0         ≡⟨ ap (λ ϕ → index b (fwd ϕ) 0) (compact-step [] x≡b) ⟩
    b                                             ≡˘⟨ x≡b ⟩
    x                                             ∎
  ... | cs #r c , p =
    index b (fwd (compact b (([] #r x) ◁⊗ xs))) 0         ≡⟨ ap (λ ϕ → index b (fwd (compact b ϕ)) 0) (◁⊗-bwd ([] #r x) xs) ⟩
    index b (fwd (compact b (([] #r x) ++r bwd xs))) 0    ≡⟨ ap (λ ϕ → index b (fwd ϕ) 0) (compact-++r ([] #r x) (bwd xs) (cs #r c) (p ∙ sym cs#r-compact)) ⟩
    index b (fwd (compact b (([] #r x) ++r (cs #r c)))) 0 ≡⟨ ap (λ ϕ → index b (fwd ϕ) 0) (compact-done (([] #r x) ++r cs) c≠base) ⟩
    index b (fwd (([] #r x) ++r (cs #r c))) 0             ≡⟨ ap (λ ϕ → index b ϕ 0) (fwd-++r ([] #r x) (cs #r c)) ⟩
    x ∎
    where
      c≠base : c ≡ b → ⊥
      c≠base = compact-last b (bwd xs) cs c p

      cs#r-compact : compact b (cs #r c) ≡ cs #r c
      cs#r-compact = compact-done cs c≠base
  index-compact b (x ∷ xs) zero | no ¬x≡b =
    index b (fwd (compact b (([] #r x) ◁⊗ xs))) 0      ≡⟨ ap (λ ϕ → index b (fwd ϕ) 0) (compact-◁⊗-¬base [] xs ¬x≡b) ⟩
    index b (fwd (([] #r x) ++r compact b (bwd xs))) 0 ≡⟨ ap (λ ϕ → index b ϕ 0) (fwd-++r ([] #r x) (compact b (bwd xs))) ⟩
    x ∎
  index-compact b (x ∷ xs) (suc n) with x ≡? b
  ... | yes x≡b with inspect (compact b (bwd xs))
  ... | [] , p =
    index b (fwd (compact b (([] #r x) ◁⊗ xs))) (suc n) ≡⟨ ap (λ ϕ → index b (fwd ϕ) (suc n)) (compact-◁⊗ ([] #r x) xs [] p) ⟩
    index b (fwd (compact b ([] #r x))) (suc n)         ≡⟨ ap (λ ϕ → index b (fwd ϕ) (suc n)) (compact-step [] x≡b) ⟩
    b                                                   ≡˘⟨ index-vanishes b xs n (vanishes-bwd b xs p) ⟩
    index b xs n ∎
  ... | cs #r c , p =
    index b (fwd (compact b (([] #r x) ◁⊗ xs))) (suc n)         ≡⟨ ap (λ ϕ → index b (fwd (compact b ϕ)) (suc n)) (◁⊗-bwd ([] #r x) xs) ⟩
    index b (fwd (compact b (([] #r x) ++r bwd xs))) (suc n)    ≡⟨ ap (λ ϕ → index b (fwd ϕ) (suc n)) (compact-++r ([] #r x) (bwd xs) (cs #r c) (p ∙ sym cs#r-compact)) ⟩
    index b (fwd (compact b (([] #r x) ++r (cs #r c)))) (suc n) ≡⟨ ap (λ ϕ → index b (fwd ϕ) (suc n)) (compact-done (([] #r x) ++r cs) c≠base) ⟩
    index b (fwd ((([] #r x) ++r cs) #r c)) (suc n)             ≡⟨ ap (λ ϕ → index b ϕ (suc n)) (fwd-++r ([] #r x) (cs #r c)) ⟩     
    index b (fwd (cs #r c)) n                                   ≡˘⟨ ap (λ ϕ → index b (fwd ϕ) n) p ⟩
    index b (fwd (compact b (bwd xs))) n                        ≡⟨ index-compact b xs n ⟩
    index b xs n ∎
    where
      c≠base : c ≡ b → ⊥
      c≠base = compact-last b (bwd xs) cs c p

      cs#r-compact : compact b (cs #r c) ≡ cs #r c
      cs#r-compact = compact-done cs c≠base
  index-compact b (x ∷ xs) (suc n) | no ¬x≡b =
    index b (fwd (compact b (([] #r x) ◁⊗ xs))) (suc n)      ≡⟨ ap (λ ϕ → index b (fwd ϕ) (suc n)) (compact-◁⊗-¬base [] xs ¬x≡b) ⟩
    index b (fwd (([] #r x) ++r compact b (bwd xs))) (suc n) ≡⟨ ap (λ ϕ → index b ϕ (suc n)) (fwd-++r ([] #r x) (compact b (bwd xs))) ⟩
    index b (fwd (compact b (bwd xs))) n                     ≡⟨ index-compact b xs n ⟩
    index b xs n ∎

  index-mono : ∀ b1 xs b2 ys → merge-list≤ b1 xs b2 ys → ∀ n → (index b1 xs n) ≤ (index b2 ys n)
  index-mono b1 [] b2 [] xs≤ys n = xs≤ys
  index-mono b1 [] b2 (y ∷ ys) xs≤ys zero with cmp b1 y
  ... | lt b1<y = inr b1<y
  ... | eq b1≡y = inl b1≡y
  index-mono b1 [] b2 (y ∷ ys) xs≤ys (suc n) with cmp b1 y
  ... | lt b1<y = index-mono b1 [] b2 ys xs≤ys n
  ... | eq b1≡y = index-mono b1 [] b2 ys xs≤ys n
  index-mono b1 (x ∷ xs) b2 [] xs≤ys zero with cmp x b2
  ... | lt x<b2 = inr x<b2
  ... | eq x≡b2 = inl x≡b2
  index-mono b1 (x ∷ xs) b2 [] xs≤ys (suc n) with cmp x b2
  ... | lt x<b2 = index-mono b1 xs b2 [] xs≤ys n
  ... | eq x≡b2 = index-mono b1 xs b2 [] xs≤ys n
  index-mono b1 (x ∷ xs) b2 (y ∷ ys) xs≤ys zero with cmp x y
  ... | lt x<y = inr x<y
  ... | eq x≡y = inl x≡y
  index-mono b1 (x ∷ xs) b2 (y ∷ ys) xs≤ys (suc n) with cmp x y
  ... | lt x<y = index-mono b1 xs b2 ys xs≤ys n
  ... | eq x≡y = index-mono b1 xs b2 ys xs≤ys n

  index-strictly-mono : ∀ b1 xs b2 ys → merge-list< b1 xs b2 ys → (index b1 xs) inf< (index b2 ys)
  index-strictly-mono b1 xs b2 ys = go xs ys
    where
      go : ∀ xs ys → merge-list< b1 xs b2 ys → (index b1 xs) inf< (index b2 ys)
      go [] [] (lift b1<b2) =
        inf-< (λ _ → inr b1<b2) (inc (0 , b1<b2))
      go [] (y ∷ ys) xs<ys with cmp b1 y
      ... | lt b1<y =
        inf-< (λ { zero → inr b1<y ; (suc n) → index-mono b1 [] b2 ys xs<ys n }) (inc (0 , b1<y))
      ... | eq b1≡y =
        inf-< (λ { zero → inl b1≡y; (suc n) →  []<∞ys .≤-everywhere n }) (∥-∥-map (λ p → (suc (fst p)) , (snd p)) ([]<∞ys .<-somewhere))
        where
          []<∞ys = go [] ys xs<ys
      go (x ∷ xs) [] xs<ys with cmp x b2
      ... | lt x<b2 =
        inf-< (λ { zero → inr x<b2 ; (suc n) → index-mono b1 xs b2 [] xs<ys n }) (inc (0 , x<b2))
      ... | eq x≡b2 =
        inf-< (λ { zero → inl x≡b2; (suc n) →  xs<∞[] .≤-everywhere n }) (∥-∥-map (λ p → (suc (fst p)) , (snd p)) (xs<∞[] .<-somewhere))
        where
          xs<∞[] = go xs [] xs<ys
      go (x ∷ xs) (y ∷ ys) xs<ys with cmp x y
      ... | lt x<y =
        inf-< (λ { zero → inr x<y ; (suc n) → index-mono b1 xs b2 ys xs<ys n }) (inc (0 , x<y))
      ... | eq x≡y =
        inf-< (λ { zero → inl x≡y; (suc n) →  xs<∞ys .≤-everywhere n }) (∥-∥-map (λ p → (suc (fst p)) , (snd p)) (xs<∞ys .<-somewhere))
        where
          xs<∞ys = go xs ys xs<ys

--------------------------------------------------------------------------------
-- Bundled Instances

module _ {o r} (𝒟 : DisplacementAlgebra o r) (cmp : ∀ x y → Tri (DisplacementAlgebra._<_ 𝒟) x y) where
  open NearlyConst 𝒟 cmp

  NearlyConstant : DisplacementAlgebra o (o ⊔ r)
  ⌞ NearlyConstant ⌟ = SupportList
  NearlyConstant .structure .DisplacementAlgebra-on._<_ = _merge<_
  NearlyConstant .structure .DisplacementAlgebra-on.ε = empty
  NearlyConstant .structure .DisplacementAlgebra-on._⊗_ = merge
  NearlyConstant .structure .DisplacementAlgebra-on.has-displacement-algebra = merge-is-displacement-algebra
  ⌞ NearlyConstant ⌟-set = SupportList-is-set


--------------------------------------------------------------------------------
-- Subalgebra Structure

module _ {o r} {𝒟 : DisplacementAlgebra o r} (cmp : ∀ x y → Tri (DisplacementAlgebra._<_ 𝒟) x y) where
  private
    module 𝒟 = DisplacementAlgebra 𝒟
    open 𝒟 using (ε; _⊗_; _<_; _≤_)
    open NearlyConst 𝒟 cmp
    open Inf 𝒟
    open SupportList

  NearlyConstant⊆InfProd : is-displacement-subalgebra (NearlyConstant 𝒟 cmp) (InfProd 𝒟)
  NearlyConstant⊆InfProd = subalgebra
    where

      into : SupportList → Nat → ⌞ 𝒟 ⌟
      into xs n = index (xs .base) (list xs) n

      into-preserves-⊗ : ∀ xs ys n → into (merge xs ys) n ≡ (into xs ⊗∞ into ys) n
      into-preserves-⊗  xs ys n =
        index (xs .base ⊗ ys .base) (fwd (compact (xs .base ⊗ ys .base) (bwd (merge-list (xs .base) (list xs) (ys .base) (list ys))))) n
          ≡⟨ index-compact (xs .base ⊗ ys .base) (merge-list (xs .base) (list xs) (ys .base) (list ys)) n ⟩
        index (xs .base ⊗ ys .base) (merge-list (xs .base) (list xs) (ys .base) (list ys)) n
          ≡⟨ go (xs .base) (list xs) (ys .base) (list ys) n ⟩
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

      index≡→base≡ : ∀ b1 xs b2 ys → (∀ n → index b1 xs n ≡ index b2 ys n) → b1 ≡ b2
      index≡→base≡ b1 [] b2 [] p = p 0
      index≡→base≡ b1 [] b2 (y ∷ ys) p = index≡→base≡ b1 [] b2 ys λ n → p (suc n)
      index≡→base≡ b1 (x ∷ xs) b2 [] p = index≡→base≡ b1 xs b2 [] λ n → p (suc n)
      index≡→base≡ b1 (x ∷ xs) b2 (y ∷ ys) p = index≡→base≡ b1 xs b2 ys λ n → p (suc n)

      all-base→¬compact : ∀ b x xs → (∀ n → index b (x ∷ xs) n ≡ b) → is-compact b (bwd (x ∷ xs)) → ⊥
      all-base→¬compact b x [] p xs-compact with x ≡? b
      ... | no x≠base = x≠base (p 0)
      all-base→¬compact b x (y ∷ xs) p xs-compact =
        all-base→¬compact b y xs (λ n → p (suc n)) (is-compact-tail x (y ∷ xs) b xs-compact)

      into-inj : ∀ xs ys → (∀ n → into xs n ≡ into ys n) → xs ≡ ys
      into-inj xs ys p =
        -- Same situation as merge≤-non-strict.
        let xs′-compact = subst (is-compact (xs .base)) (sym $ bwd-fwd (xs .elts)) (xs .compacted)
            ys′-compact = subst (is-compact (ys .base)) (sym $ bwd-fwd (ys .elts)) (ys .compacted)
        in subst₂ (_≡_)
             (support-list-path refl (bwd-fwd (xs .elts)))
             (support-list-path refl (bwd-fwd (ys .elts)))
             (go (xs .base) (list xs) (ys .base) (list ys) xs′-compact ys′-compact p)
        where
          go : ∀ b1 xs b2 ys
               → (xs-compact : is-compact b1 (bwd xs))
               → (ys-compact : is-compact b2 (bwd ys))
               → (∀ n → index b1 xs n ≡ index b2 ys n)
               → support-list b1 (bwd xs) xs-compact ≡ support-list b2 (bwd ys) ys-compact
          go b1 [] b2 [] xs-compact ys-compact p = support-list-path (p 0) refl
          go b1 [] b2 (y ∷ ys) xs-compact ys-compact p =
            absurd $ all-base→¬compact b2 y ys (λ n → sym (p n) ∙ (index≡→base≡ b1 [] b2 (y ∷ ys) p)) ys-compact
          go b1 (x ∷ xs) b2 [] xs-compact ys-compact p =
            absurd $ all-base→¬compact b1 x xs (λ n → p n ∙ sym (index≡→base≡ b1 (x ∷ xs) b2 [] p)) xs-compact
          go b1 (x ∷ xs) b2 (y ∷ ys) xs-compact ys-compact p =
            support-list-path (ap base xs≡ys) (ap bwd (ap₂ _∷_ (p 0) ((over {x = xs} {y = ys} fwd-bwd (ap list xs≡ys)))))
            where
              xs≡ys =
                go b1 xs b2 ys
                  (is-compact-tail x xs b1 xs-compact)
                  (is-compact-tail y ys b2 ys-compact)
                  (λ n → p (suc n))

      subalgebra : is-displacement-subalgebra (NearlyConstant 𝒟 cmp) (InfProd 𝒟)
      subalgebra .is-displacement-subalgebra.into ._⟨$⟩_ = into
      subalgebra .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-ε = refl
      subalgebra .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.pres-⊗ xs ys = funext (into-preserves-⊗ xs ys)
      subalgebra .is-displacement-subalgebra.into .homo .is-displacement-algebra-homomorphism.strictly-mono {xs} {ys} = index-strictly-mono (xs .base) (list xs) (ys .base) (list ys)
      subalgebra .is-displacement-subalgebra.inj {xs} {ys} p = into-inj xs ys (happly p)

--------------------------------------------------------------------------------
-- Ordered Monoid

module _ {o r} {𝒟 : DisplacementAlgebra o r} (𝒟-ordered-monoid : has-ordered-monoid 𝒟) (cmp : ∀ x y → Tri (DisplacementAlgebra._<_ 𝒟) x y) where

  private
    module 𝒟 = DisplacementAlgebra 𝒟
    open 𝒟 using (ε; _⊗_; _<_; _≤_)
    open NearlyConst 𝒟 cmp
    open Inf 𝒟
    open is-ordered-monoid 𝒟-ordered-monoid
    open SupportList

    merge-list≤-right-invariant : ∀ b1 xs b2 ys b3 zs
                                  → merge-list≤ b1 xs b2 ys
                                  → merge-list≤ (b1 ⊗ b3) (merge-list b1 xs b3 zs) (b2 ⊗ b3) (merge-list b2 ys b3 zs)
    merge-list≤-right-invariant b1 xs b2 ys b3 zs xs≤ys = go xs ys zs xs≤ys
      where
        step≤ : ∀ xs ys zs {x y z}
                → tri-rec
                    (merge-list≤ b1 xs b2 ys)
                    (merge-list≤ b1 xs b2 ys)
                    (Lift (o ⊔ r) ⊥)
                    (cmp x y)
                → tri-rec
                    (merge-list≤ (b1 ⊗ b3) (merge-list b1 xs b3 zs) (b2 ⊗ b3) (merge-list b2 ys b3 zs))
                    (merge-list≤ (b1 ⊗ b3) (merge-list b1 xs b3 zs) (b2 ⊗ b3) (merge-list b2 ys b3 zs))
                    (Lift (o ⊔ r) ⊥)
                    (cmp (x ⊗ z) (y ⊗ z))
        step≤ xs ys zs {x = x} {y = y} {z = z} xs≤ys with cmp x y
        ... | lt x<y =
          merge-list≤-step≤ (b1 ⊗ b3) (merge-list b1 xs b3 zs) (b2 ⊗ b3) (merge-list b2 ys b3 zs) (right-invariant (inr x<y)) $
          merge-list≤-right-invariant b1 xs b2 ys b3 zs xs≤ys
        ... | eq x≡y =
          merge-list≤-step≤ (b1 ⊗ b3) (merge-list b1 xs b3 zs) (b2 ⊗ b3) (merge-list b2 ys b3 zs) (right-invariant (inl x≡y)) $
          merge-list≤-right-invariant b1 xs b2 ys b3 zs xs≤ys

        go : ∀ xs ys zs
             → merge-list≤ b1 xs b2 ys
             → merge-list≤ (b1 ⊗ b3) (merge-list b1 xs b3 zs) (b2 ⊗ b3) (merge-list b2 ys b3 zs)
        go [] [] [] xs≤ys =
          right-invariant xs≤ys
        go [] [] (z ∷ zs) xs≤ys =
          step≤ [] [] zs (merge-list≤-step≤ b1 [] b2 [] xs≤ys xs≤ys)
        go [] (y ∷ ys) [] xs≤ys =
          step≤ [] ys [] xs≤ys
        go [] (y ∷ ys) (z ∷ zs) xs≤ys =
          step≤ [] ys zs xs≤ys
        go (x ∷ xs) [] [] xs≤ys =
          step≤ xs [] [] xs≤ys
        go (x ∷ xs) [] (z ∷ zs) xs≤ys =
          step≤ xs [] zs xs≤ys
        go (x ∷ xs) (y ∷ ys) [] xs≤ys =
          step≤ xs ys [] xs≤ys
        go (x ∷ xs) (y ∷ ys) (z ∷ zs) xs≤ys =
          step≤ xs ys zs xs≤ys

    nearly-constant-has-ordered-monoid : has-ordered-monoid (NearlyConstant 𝒟 cmp)
    nearly-constant-has-ordered-monoid =
      right-invariant→has-ordered-monoid (NearlyConstant 𝒟 cmp) λ {xs} {ys} {zs} xs≤ys →
        merge≤→non-strict (merge xs zs) (merge ys zs) $
          merge-list≤-trans
            (xs .base ⊗ zs .base) (fwd $ compact (xs .base ⊗ zs .base) $ bwd $ merge-list (xs .base) (list xs) (zs .base) (list zs))
            (xs .base ⊗ zs .base) (fwd (bwd (merge-list (xs .base) (list xs) (zs .base) (list zs))))
            (ys .base ⊗ zs .base) (fwd $ compact (ys .base ⊗ zs .base) $ bwd $ merge-list (ys .base) (list ys) (zs .base) (list zs))
            (compact-≥ (xs .base ⊗ zs .base) (bwd $ merge-list (xs .base) (list xs) (zs .base) (list zs))) $
          merge-list≤-trans
            (xs .base ⊗ zs .base) (fwd (bwd (merge-list (xs .base) (list xs) (zs .base) (list zs))))
            (ys .base ⊗ zs .base) (fwd (bwd (merge-list (ys .base) (list ys) (zs .base) (list zs))))
            (ys .base ⊗ zs .base) (fwd $ compact (ys .base ⊗ zs .base) $ bwd $ merge-list (ys .base) (list ys) (zs .base) (list zs))
            (subst₂ (λ ϕ ψ → merge-list≤ (xs .base ⊗ zs .base) ϕ (ys .base ⊗ zs .base) ψ)
              (sym $ fwd-bwd (merge-list (xs .base) (list xs) (zs .base) (list zs)))
              (sym $ fwd-bwd (merge-list (ys .base) (list ys) (zs .base) (list zs)))
              (merge-list≤-right-invariant (xs .base) (list xs) (ys .base) (list ys) (zs .base) (list zs) (non-strict→merge≤ xs ys xs≤ys)))
            (compact-≤ (ys .base ⊗ zs .base) (bwd $ merge-list (ys .base) (list ys) (zs .base) (list zs)))

--------------------------------------------------------------------------------
-- Joins

module _ {o r} {𝒟 : DisplacementAlgebra o r} (𝒟-joins : has-joins 𝒟) (cmp : ∀ x y → Tri (DisplacementAlgebra._<_ 𝒟) x y) where
  private
    module 𝒟 = DisplacementAlgebra 𝒟
    open 𝒟 using (ε; _⊗_; _<_; _≤_)
    open NearlyConst 𝒟 cmp
    open Inf 𝒟
    open has-joins 𝒟-joins
    open SupportList

  join-list : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟
  join-list = merge-with join

  join-support : SupportList → SupportList → SupportList
  join-support xs ys .base = join (xs .base) (ys .base)
  join-support xs ys .elts = compact (join (xs .base) (ys .base)) (bwd (join-list (xs .base) (list xs) (ys .base) (list ys)))
  join-support xs ys .compacted = compact-is-compact (join (xs .base) (ys .base)) (bwd (join-list (xs .base) (list xs) (ys .base) (list ys)))

  join-list-joinl : ∀ b1 xs b2 ys → merge-list≤ b1 xs (join b1 b2) (join-list b1 xs b2 ys)
  join-list-joinl b1 [] b2 [] =
    joinl
  join-list-joinl b1 [] b2 (y ∷ ys) =
    merge-list≤-step≤ b1 [] (join b1 b2) (join-list b1 [] b2 ys) joinl (join-list-joinl b1 [] b2 ys)
  join-list-joinl b1 (x ∷ xs) b2 [] =
    merge-list≤-step≤ b1 xs (join b1 b2) (join-list b1 xs b2 []) joinl (join-list-joinl b1 xs b2 [])
  join-list-joinl b1 (x ∷ xs) b2 (y ∷ ys) =
    merge-list≤-step≤ b1 xs (join b1 b2) (join-list b1 xs b2 ys) joinl (join-list-joinl b1 xs b2 ys)

  join-list-joinr : ∀ b1 xs b2 ys → merge-list≤ b2 ys (join b1 b2) (join-list b1 xs b2 ys)
  join-list-joinr b1 [] b2 [] =
    joinr
  join-list-joinr b1 [] b2 (y ∷ ys) =
    merge-list≤-step≤ b2 ys (join b1 b2) (join-list b1 [] b2 ys) joinr (join-list-joinr b1 [] b2 ys)
  join-list-joinr b1 (x ∷ xs) b2 [] =
    merge-list≤-step≤ b2 [] (join b1 b2) (join-list b1 xs b2 []) joinr (join-list-joinr b1 xs b2 [])
  join-list-joinr b1 (x ∷ xs) b2 (y ∷ ys) =
    merge-list≤-step≤ b2 ys (join b1 b2) (join-list b1 xs b2 ys) joinr (join-list-joinr b1 xs b2 ys)

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
        (xs .base) (list xs)
        (join (xs .base) (ys .base)) (fwd $ bwd $ join-list (xs .base) (list xs) (ys .base) (list ys))
        (join (xs .base) (ys .base)) (fwd $ compact (join (xs .base) (ys .base)) $ bwd $ join-list (xs .base) (list xs) (ys .base) (list ys))
        (subst (λ ϕ → merge-list≤ (xs .base) (list xs) (join (xs .base) (ys .base)) ϕ)
          (sym $ fwd-bwd $ join-list (xs .base) (list xs) (ys .base) (list ys))
          (join-list-joinl (xs .base) (list xs) (ys .base) (list ys)))
        (compact-≤ (join (xs .base) (ys .base)) (bwd $ join-list (xs .base) (list xs) (ys .base) (list ys)))
  nearly-constant-has-joins .has-joins.joinr {xs} {ys} =
    merge≤→non-strict ys (join-support xs ys) $
      merge-list≤-trans
        (ys .base) (list ys)
        (join (xs .base) (ys .base)) (fwd $ bwd $ join-list (xs .base) (list xs) (ys .base) (list ys))
        (join (xs .base) (ys .base)) (fwd $ compact (join (xs .base) (ys .base)) $ bwd $ join-list (xs .base) (list xs) (ys .base) (list ys))
        (subst (λ ϕ → merge-list≤ (ys .base) (list ys) (join (xs .base) (ys .base)) ϕ)
          (sym $ fwd-bwd $ join-list (xs .base) (list xs) (ys .base) (list ys))
          (join-list-joinr (xs .base) (list xs) (ys .base) (list ys)))
        (compact-≤ (join (xs .base) (ys .base)) (bwd $ join-list (xs .base) (list xs) (ys .base) (list ys)))
  nearly-constant-has-joins .has-joins.universal {xs} {ys} {zs} xs≤zs ys≤zs =
    merge≤→non-strict (join-support xs ys) zs $
      merge-list≤-trans
        (join (xs .base) (ys .base)) (fwd $ compact (join (xs .base) (ys .base)) $ bwd (join-list (xs .base) (list xs) (ys .base) (list ys)))
        (join (xs .base) (ys .base)) (fwd $ bwd $ join-list (xs .base) (list xs) (ys .base) (list ys))
        (zs .base) (list zs)
        (compact-≥ (join (xs .base) (ys .base)) (bwd $ join-list (xs .base) (list xs) (ys .base) (list ys)))
        (subst (λ ϕ → merge-list≤ (join (xs .base) (ys .base)) ϕ (zs .base) (list zs))
          (sym $ fwd-bwd ( join-list (xs .base) (list xs) (ys .base) (list ys)))
          (join-list-universal (xs .base) (list xs) (ys .base) (list ys) (zs .base) (list zs)
            (non-strict→merge≤ xs zs xs≤zs)
            (non-strict→merge≤ ys zs ys≤zs)))

module _ {o r} {𝒟 : DisplacementAlgebra o r} (𝒟-bottom : has-bottom 𝒟) (cmp : ∀ x y → Tri (DisplacementAlgebra._<_ 𝒟) x y) (b : ⌞ 𝒟 ⌟) where
  private
    module 𝒟 = DisplacementAlgebra 𝒟
    open 𝒟 using (ε; _⊗_; _<_; _≤_)
    open NearlyConst 𝒟 cmp
    open Inf 𝒟
    open SupportList
    open has-bottom 𝒟-bottom

  bot-list : SupportList
  bot-list = support-list bot [] tt

  bot-list-is-bottom : ∀ b xs → merge-list≤ bot [] b xs
  bot-list-is-bottom b [] = is-bottom b
  bot-list-is-bottom b (x ∷ xs) = merge-list≤-step≤ bot [] b xs (is-bottom x) (bot-list-is-bottom b xs)

  nearly-constant-has-bottom : has-bottom (NearlyConstant 𝒟 cmp)
  nearly-constant-has-bottom .has-bottom.bot = bot-list
  nearly-constant-has-bottom .has-bottom.is-bottom xs =
    merge≤→non-strict bot-list xs $ bot-list-is-bottom (xs .base) (list xs)
