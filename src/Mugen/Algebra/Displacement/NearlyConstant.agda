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

module NearlyConst {o r} (𝒟 : DisplacementAlgebra o r) (_≡?_ : Discrete ⌞ 𝒟 ⌟) (cmp : ∀ x y → Tri (DisplacementAlgebra._<_ 𝒟) x y) where

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

  compact-◁⊗ : ∀ {base} xs ys zs → compact base (bwd ys) ≡ compact base (bwd zs) → compact base (xs ◁⊗ ys) ≡ compact base (xs ◁⊗ zs)
  compact-◁⊗ {base = base} xs ys zs p =
    compact base (xs ◁⊗ ys)      ≡⟨ ap (compact base) (◁⊗-bwd xs ys) ⟩
    compact base (xs ++r bwd ys) ≡⟨ compact-++r xs (bwd ys) (bwd zs) p ⟩
    compact base (xs ++r bwd zs) ≡˘⟨ ap (compact base) (◁⊗-bwd xs zs) ⟩
    compact base (xs ◁⊗ zs) ∎

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
        xs′ = support-list (xs .base) (bwd (list xs)) xs′-compact
        ys′ = support-list (ys .base) (bwd (list ys)) ys′-compact
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
  -- Notational Tricks
  --
  -- We define a strict-ordering structure for _merge<_ purely to
  -- be able to use equational reasoning for the later proofs.
  -- This is marked private, as we will expose it as part of
  -- the displacement algebra structure later.

  private
    MergeOrd : StrictOrder o (o ⊔ r)
    ⌞ MergeOrd ⌟ = SupportList
    MergeOrd .structure .StrictOrder-on._<_ = _merge<_
    MergeOrd .structure .StrictOrder-on.has-is-strict-order = merge-is-strict-order
    ⌞ MergeOrd ⌟-set = SupportList-is-set

 
  open StrictOrder-Reasoning MergeOrd

