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

module NearlyConst {o r} (𝒟 : DisplacementAlgebra o r) (_≡?_ : Discrete ⌞ 𝒟 ⌟) where

  private
    module 𝒟 = DisplacementAlgebra 𝒟
    open 𝒟 using (ε; _⊗_; _<_; _≤_)

    instance
      HLevel-< : ∀ {x y} {n} → H-Level (x < y) (suc n)
      HLevel-< = prop-instance 𝒟.<-is-prop

      HLevel-≤ : ∀ {x y} {n} → H-Level (x ≤ y) (suc n)
      HLevel-≤ = prop-instance 𝒟.≤-is-prop

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

  compact-vanish-++r : ∀ {base} xs ys → compact base ys ≡ [] → compact base (xs ++r ys) ≡ compact base xs
  compact-vanish-++r {base = base} xs [] ys-vanish = refl
  compact-vanish-++r {base = base} xs (ys #r y) ys-vanish with y ≡? base
  ... | yes _ = compact-vanish-++r xs ys ys-vanish
  ... | no _ = absurd $ #r≠[] ys-vanish

  compact-++r : ∀ {base} xs ys zs → compact base ys ≡ compact base zs → compact base (xs ++r ys) ≡ compact base (xs ++r zs)
  compact-++r {base = base} xs [] [] p =
    refl
  compact-++r {base = base} xs [] (zs #r z) p =
    sym (compact-vanish-++r xs (zs #r z) (sym p))
  compact-++r {base = base} xs (ys #r y) [] p =
    compact-vanish-++r xs (ys #r y) p
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

  --------------------------------------------------------------------------------
  -- Merging Lists
  -- 
  -- We start by defining how to merge two lists without performing
  -- compaction.

  merge-list : ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟
  merge-list b1 [] b2 [] = []
  merge-list b1 [] b2 (y ∷ ys) = (b1 ⊗ y) ∷ merge-list b1 [] b2 ys
  merge-list b1 (x ∷ xs) b2 [] = (x ⊗ b2) ∷ merge-list b1 xs b2 []
  merge-list b1 (x ∷ xs) b2 (y ∷ ys) = (x ⊗ y) ∷ merge-list b1 xs b2 ys

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

  merge-is-magma : is-magma merge
  merge-is-magma .has-is-set = SupportList-is-set

  merge-is-semigroup : is-semigroup merge
  merge-is-semigroup .has-is-magma = merge-is-magma
  merge-is-semigroup .associative {xs} {ys} {zs} = merge-assoc xs ys zs

  merge-is-monoid : is-monoid empty merge
  merge-is-monoid .has-is-semigroup = merge-is-semigroup
  merge-is-monoid .idl {xs} = merge-idl xs
  merge-is-monoid .idr {ys} = merge-idr ys
