module Mugen.Algebra.Displacement.DenseFiniteSupport where

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
open import Mugen.Data.Nat hiding (_<_)

module DenseFinSupport {o r} (𝒟 : DisplacementAlgebra o r) (ε? : ∀ x → Dec (x ≡ DisplacementAlgebra.ε 𝒟)) where
  private
    module 𝒟 = DisplacementAlgebra 𝒟
    open 𝒟 using (ε; _⊗_)

    --------------------------------------------------------------------------------
    -- Densely Finitely Supported Functions
    --
    -- There are 2 possible representations for a function with finite support:
    -- a dense representation that consists of a list of values, which contains
    -- ε values to pad the list out, and a sparse representation that where
    -- each non-ε value value is associated with the number of ε values that precede it.
    --
    -- To further complicate matters, both of these representations have a flaw:
    -- Multiple lists can denote the same function. For instance, consider [1] and
    -- [1, ε, ε]. This causes a problem when we try and show that the finitely supported
    -- functions are a sub-displacement algebra of the infinite product; injectivity fails!
    -- To rememdy this, we have 2 options: assign canonical representatives for each equivalence
    -- class, or take a quotient. Both options are fiddly, but we chose the canonical representative
    -- option here.
    --
    -- * Implementation Notes
    --
    -- We very explicitly do /not/ use with abstraction in the definition of 'is-compact'
    -- and 'compact'.
    -- The reason is that Agda will often get confused and not reduce goals,
    -- even though we have done the required matches that should allow
    -- the goals to be unblocked.
    --
    -- The situation is made worse by the fact that Agda does not allow us
    -- to use propositional evidence to unblock stuck with-abstracted goals.
    -- IE: if we have a goal of the form 'blah | ε? x' and we can construct
    -- a propositional equality 'ε? x ≡ yes ...', then we still can't unblock
    -- the goal.
    --
    -- Therefore, we use explicit 'case' eliminators for 'Dec', and 
    -- then define helpers that allow us to use propositional evidence
    -- to get propositional equalities that describe the expected computational
    -- behaviour.
    --
    -- We also make the choice to use snoc-lists here, as our canonical forms
    -- will have no _trailing_ ε elements. We could accomplish this with a left-fold,
    -- but the induction becomes much more tedious. However, the /merging/ of lists
    -- operates on cons-lists, as this is the more natural choice.

    -- We say a support list is compact if it has not trailing ε's.
    -- This characterizes the canonical representatives.
    is-compact : Bwd ⌞ 𝒟 ⌟ → Type
    is-compact [] = ⊤
    is-compact (xs #r x) = case _ (λ _ → ⊥) (λ _ → ⊤) (ε? x)

    is-compact-case : ∀ {x} → Dec (x ≡ ε) → Type
    is-compact-case p = case _ (λ _ → ⊥) (λ _ → ⊤) p

    -- Propositional computation helpers for 'is-compact'
    ¬ε→is-compact : ∀ xs {x} → (x ≡ ε → ⊥) → is-compact (xs #r x)
    ¬ε→is-compact xs {x = x} ¬ε =
      case (λ p → is-compact-case p)
        (λ ε! → ¬ε ε!)
        (λ _ → tt)
        (ε? x)

    ε→isn't-compact : ∀ xs {x} → x ≡ ε → is-compact (xs #r x) → ⊥
    ε→isn't-compact xs {x = x} ε! is-compact = subst is-compact-case eq is-compact
      where
        eq : ε? x ≡ yes ε! 
        eq = case (λ p → p ≡ yes ε!)
          (λ ε!′ → ap yes (⌞ 𝒟 ⌟-set x ε ε!′ ε!))
          (λ ¬ε → absurd (¬ε ε!))
          (ε? x)

    is-compact-is-prop : ∀ xs → is-prop (is-compact xs)
    is-compact-is-prop [] = hlevel 1
    is-compact-is-prop (xs #r x) =
      case (λ p → is-prop (is-compact-case p))
        (λ _ → hlevel 1)
        (λ _ → hlevel 1)
        (ε? x)

    -- Remove all trailing ε elements.
    compact : Bwd ⌞ 𝒟 ⌟ → Bwd ⌞ 𝒟 ⌟
    compact [] = []
    compact (xs #r x) =
      case _
        (λ _ → compact xs)
        (λ _ → xs #r x)
        (ε? x)

    compact-case : ∀ xs {x} → Dec (x ≡ ε) → Bwd ⌞ 𝒟 ⌟
    compact-case xs {x} p =
      case _
        (λ _ → compact xs)
        (λ _ → xs #r x)
        p

    -- Propositional computation helpers for 'compact'
    compact-step : ∀ xs {x} → (x ≡ ε) → compact (xs #r x) ≡ compact xs
    compact-step xs {x = x} ε! =
      case (λ p → compact-case xs p ≡ compact xs)
        (λ _ → refl)
        (λ ¬ε → absurd $ ¬ε ε!)
        (ε? x)

    compact-done : ∀ xs {x} → (x ≡ ε → ⊥) → compact (xs #r x) ≡ (xs #r x)
    compact-done xs {x} ¬ε =
      case (λ p → compact-case xs p ≡ (xs #r x))
        (λ ε! → absurd $ ¬ε ε!)
        (λ _ → refl)
        (ε? x)

    -- If a list has no trailing 'ε' elements, then compacting it does nothing.
    compact-compacted : ∀ xs → is-compact xs → compact xs ≡ xs
    compact-compacted [] is-compact = refl
    compact-compacted (xs #r x) is-compact =
      case (λ v → compact (xs #r x) ≡ (xs #r x))
        (λ ε! → absurd $ ε→isn't-compact xs ε! is-compact)
        (λ ¬ε → compact-done xs ¬ε)
        (ε? x)

    -- compacting a list removes all trailing ε elements.
    compact-is-compact : ∀ xs → is-compact (compact xs)
    compact-is-compact [] = tt
    compact-is-compact (xs #r x) with ε? x
    ... | yes _ = compact-is-compact xs
    ... | no ¬ε = ¬ε→is-compact xs ¬ε

    compact-vanish-++r : ∀ xs ys → compact ys ≡ [] → compact (xs ++r ys) ≡ compact xs
    compact-vanish-++r xs [] ys-vanish = refl
    compact-vanish-++r xs (ys #r y) ys-vanish with ε? y
    ... | yes _ = compact-vanish-++r xs ys ys-vanish
    ... | no _  = absurd $ #r≠[] ys-vanish

    compact-++r : ∀ xs ys zs → compact ys ≡ compact zs → compact (xs ++r ys) ≡ compact (xs ++r zs)
    compact-++r xs [] [] p = refl
    compact-++r xs [] (zs #r z) p = sym (compact-vanish-++r xs (zs #r z) (sym p))
    compact-++r xs (ys #r y) [] p = compact-vanish-++r xs (ys #r y) p
    compact-++r xs (ys #r y) (zs #r z) =
      -- Cannot be done using with-abstraction /or/ a helper function because the termination
      -- checker gets confused.
      -- Ouch.
      case (λ p → compact-case ys p ≡ compact (zs #r z) → compact-case (xs ++r ys) p ≡ compact ((xs ++r zs) #r z))
        (λ y-ε! → case (λ p → compact ys ≡ compact-case zs p → compact (xs ++r ys) ≡ compact-case (xs ++r zs) p)
          (λ z-ε! p → compact-++r xs ys zs p)
          (λ z-¬ε p →
            compact (xs ++r ys)        ≡⟨ compact-++r xs ys (zs #r z) (p ∙ sym (compact-done zs z-¬ε)) ⟩
            compact (xs ++r (zs #r z)) ≡⟨ compact-done (xs ++r zs) z-¬ε ⟩
            (xs ++r zs) #r z ∎)
          (ε? z))
        (λ y-¬ε → case (λ p → ys #r y ≡ compact-case zs p → (xs ++r ys) #r y ≡ compact-case (xs ++r zs) p)
          (λ z-ε! p →
            xs ++r (ys #r y)           ≡˘⟨ compact-done (xs ++r ys) y-¬ε ⟩
            compact (xs ++r (ys #r y)) ≡⟨ compact-++r xs (ys #r y) zs (compact-done ys y-¬ε ∙ p) ⟩
            compact (xs ++r zs) ∎)
          (λ z-¬ε p → ap (xs ++r_) p)
          (ε? z))
        (ε? y)

    -- Merge two lists together (without compaction.)
    merge-list : List ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟ → List ⌞ 𝒟 ⌟
    merge-list [] ys = ys
    merge-list (x ∷ xs) [] = x ∷ xs
    merge-list (x ∷ xs) (y ∷ ys) = (x ⊗ y) ∷ merge-list xs ys

    merge-list-idr : ∀ xs → merge-list xs [] ≡ xs
    merge-list-idr [] = refl
    merge-list-idr (x ∷ xs) = refl

    merge-list-assoc : ∀ xs ys zs → merge-list xs (merge-list ys zs) ≡ merge-list (merge-list xs ys) zs
    merge-list-assoc [] ys zs = refl
    merge-list-assoc (x ∷ xs) [] zs = refl
    merge-list-assoc (x ∷ xs) (y ∷ ys) [] = refl
    merge-list-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = ap₂ _∷_ 𝒟.associative (merge-list-assoc xs ys zs)

    merge-list-∷rεl : ∀ xs ys → compact (bwd (merge-list (xs ∷r ε) ys)) ≡ compact (bwd (merge-list xs ys))
    merge-list-∷rεl [] [] = compact-step [] refl
    merge-list-∷rεl [] (y ∷ ys) =
      compact (bwd ((ε ⊗ y) ∷ ys)) ≡⟨ ap (λ ϕ → compact (bwd (ϕ ∷ ys))) 𝒟.idl ⟩
      compact (bwd (y ∷ ys))       ∎
    merge-list-∷rεl (x ∷ xs) [] =
      compact (bwd (merge-list ((x ∷ xs) ∷r ε) [])) ≡⟨ ap (λ ϕ → compact (bwd ϕ)) (merge-list-idr ((x ∷ xs) ∷r ε)) ⟩
      compact (bwd ((x ∷ xs) ∷r ε))                 ≡⟨ ap compact (bwd-++ (x ∷ xs) (ε ∷ [])) ⟩
      compact (bwd (x ∷ xs) ++r ([] #r ε))          ≡⟨ compact-++r (bwd (x ∷ xs)) ([] #r ε) [] (compact-step [] refl) ⟩
      compact (bwd (x ∷ xs))                        ≡˘⟨ ap (λ ϕ → compact (bwd ϕ)) (merge-list-idr (x ∷ xs)) ⟩
      compact (bwd (merge-list (x ∷ xs) [])) ∎
    merge-list-∷rεl (x ∷ xs) (y ∷ ys) =
      compact (bwd ((x ⊗ y) ∷ merge-list (xs ∷r ε) ys))           ≡⟨ ap compact (bwd-++ ((x ⊗ y) ∷ []) (merge-list (xs ∷r ε) ys)) ⟩
      compact (([] #r (x ⊗ y)) ++r bwd (merge-list (xs ∷r ε) ys)) ≡⟨ compact-++r ([] #r (x ⊗ y)) (bwd (merge-list (xs ∷r ε) ys)) (bwd (merge-list xs ys)) (merge-list-∷rεl xs ys) ⟩
      compact (([] #r (x ⊗ y)) ++r bwd (merge-list xs ys))        ≡˘⟨ ap compact (bwd-++ ((x ⊗ y) ∷ []) (merge-list xs ys)) ⟩
      compact (bwd ((x ⊗ y) ∷ merge-list xs ys))                  ∎

    merge-list-∷rεr : ∀ xs ys → compact (bwd (merge-list xs (ys ∷r ε))) ≡ compact (bwd (merge-list xs ys))
    merge-list-∷rεr [] [] = compact-step [] refl
    merge-list-∷rεr [] (y ∷ ys) =
      compact (bwd ((y ∷ ys) ∷r ε))        ≡⟨ ap compact (bwd-++ (y ∷ ys) (ε ∷ [])) ⟩
      compact (bwd (y ∷ ys) ++r ([] #r ε)) ≡⟨ compact-++r (bwd (y ∷ ys)) ([] #r ε) [] (compact-step [] refl) ⟩
      compact (bwd (y ∷ ys)) ∎
    merge-list-∷rεr (x ∷ xs) [] =
      compact (bwd ((x ⊗ ε) ∷ merge-list xs [])) ≡⟨ ap (λ ϕ → compact (bwd ((x ⊗ ε) ∷ ϕ))) (merge-list-idr xs) ⟩
      compact (bwd ((x ⊗ ε) ∷ xs))               ≡⟨ ap (λ ϕ → compact (bwd (ϕ ∷ xs))) 𝒟.idr ⟩
      compact (bwd (merge-list (x ∷ xs) []))     ∎
    merge-list-∷rεr (x ∷ xs) (y ∷ ys) =
      compact (bwd ((x ⊗ y) ∷ merge-list xs (ys ∷r ε)))           ≡⟨ ap compact (bwd-++ (((x ⊗ y) ∷ [])) (merge-list xs (ys ∷r ε))) ⟩
      compact (([] #r (x ⊗ y)) ++r bwd (merge-list xs (ys ∷r ε))) ≡⟨ compact-++r ([] #r (x ⊗ y)) (bwd (merge-list xs (ys ∷r ε))) (bwd (merge-list xs ys)) (merge-list-∷rεr xs ys) ⟩
      compact (([] #r (x ⊗ y)) ++r bwd (merge-list xs ys))        ≡˘⟨ ap compact (bwd-++ ((x ⊗ y) ∷ []) (merge-list xs ys)) ⟩
      compact (bwd ((x ⊗ y) ∷ merge-list xs ys)) ∎

    merge-list-#εl : ∀ xs ys → compact (bwd (merge-list (fwd (xs #r ε)) ys)) ≡ compact (bwd (merge-list (fwd xs) ys))
    merge-list-#εl xs ys =
      compact (bwd (merge-list (fwd (xs #r ε)) ys)) ≡⟨ ap (λ ϕ → compact (bwd (merge-list ϕ ys))) (fwd-++r xs ([] #r ε)) ⟩
      compact (bwd (merge-list (fwd xs ∷r ε) ys))   ≡⟨ merge-list-∷rεl (fwd xs) ys ⟩
      compact (bwd (merge-list (fwd xs) ys)) ∎

    merge-list-#εr : ∀ xs ys → compact (bwd (merge-list xs (fwd (ys #r ε)))) ≡ compact (bwd (merge-list xs (fwd ys)))
    merge-list-#εr xs ys =
      compact (bwd (merge-list xs (fwd (ys #r ε)))) ≡⟨ ap (λ ϕ → compact (bwd (merge-list xs ϕ))) (fwd-++r ys ([] #r ε)) ⟩
      compact (bwd (merge-list xs (fwd ys ∷r ε)))   ≡⟨ merge-list-∷rεr xs (fwd ys) ⟩
      compact (bwd (merge-list xs (fwd ys))) ∎

    compact-mergel : ∀ xs ys → compact (bwd (merge-list (fwd (compact xs)) (fwd ys))) ≡ compact (bwd (merge-list (fwd xs) (fwd ys)))
    compact-mergel [] ys = refl
    compact-mergel (xs #r x) ys with ε? x
    ... | yes ε! =
      compact (bwd (merge-list (fwd (compact xs)) (fwd ys))) ≡⟨ compact-mergel xs ys ⟩
      compact (bwd (merge-list (fwd xs) (fwd ys)))           ≡˘⟨ merge-list-#εl xs (fwd ys) ⟩
      compact (bwd (merge-list (fwd (xs #r ε)) (fwd ys)))    ≡˘⟨ ap (λ ϕ → compact (bwd (merge-list (fwd (xs #r ϕ)) (fwd ys)))) ε! ⟩
      compact (bwd (merge-list (fwd (xs #r x)) (fwd ys)))    ∎
    ... | no ¬ε = refl

    compact-merger : ∀ xs ys → compact (bwd (merge-list (fwd xs) (fwd (compact ys)))) ≡ compact (bwd (merge-list (fwd xs) (fwd ys)))
    compact-merger xs [] = refl
    compact-merger xs (ys #r y) with ε? y
    ... | yes ε! =
      compact (bwd (merge-list (fwd xs) (fwd (compact ys)))) ≡⟨ compact-merger xs ys ⟩
      compact (bwd (merge-list (fwd xs) (fwd ys)))           ≡˘⟨ merge-list-#εr (fwd xs) ys ⟩
      compact (bwd (merge-list (fwd xs) (fwd (ys #r ε))))    ≡˘⟨ ap (λ ϕ → compact (bwd (merge-list (fwd xs) (fwd (ys #r ϕ))))) ε! ⟩
      compact (bwd (merge-list (fwd xs) (fwd (ys #r y))))    ∎
    ... | no ¬ε = refl

    -- We define support lists as compact lists. These are the canonical
    -- representatives of the aforementioned equivalence classes
    record SupportList : Type o where
      field
        support : Bwd ⌞ 𝒟 ⌟
        canonical : is-compact support 

    open SupportList

    -- Paths between support lists are defined purely by list equality.
    support-list-path : ∀ {xs ys : SupportList} → xs .support ≡ ys .support → xs ≡ ys
    support-list-path p i .support = p i
    support-list-path {xs = xs} {ys = ys} p i .canonical =
      is-prop→pathp (λ i → is-compact-is-prop (p i))
        (xs .canonical)
        (ys .canonical)
        i

    empty : SupportList
    empty .support = []
    empty .canonical = tt

    -- Merge two support lists.
    merge : SupportList → SupportList → SupportList
    merge xs ys .support = compact $ bwd $ merge-list (fwd $ xs .support) (fwd $ ys .support)
    merge xs ys .canonical = compact-is-compact $ bwd $ merge-list (fwd $ xs .support) (fwd $ ys .support)

    compact-support : ∀ xs → compact (xs .support) ≡ xs .support
    compact-support xs = compact-compacted (xs .support) (xs .canonical)

    merge-idl : ∀ xs → merge empty xs ≡ xs
    merge-idl xs = support-list-path $
      merge empty xs .support           ≡⟨⟩
      compact (bwd (fwd (xs .support))) ≡⟨ ap compact (bwd-fwd (xs .support)) ⟩
      compact (xs .support)             ≡⟨ compact-support xs ⟩
      xs .support                       ∎

    merge-idr : ∀ xs → merge xs empty ≡ xs
    merge-idr xs = support-list-path $
      merge xs empty .support                           ≡⟨⟩
      compact (bwd (merge-list (fwd $ xs .support) [])) ≡⟨ ap (λ ϕ → compact (bwd ϕ)) (merge-list-idr (fwd $ xs .support)) ⟩
      compact (bwd (fwd (xs .support)))                 ≡⟨ ap compact (bwd-fwd (xs .support)) ⟩
      compact (xs .support)                             ≡⟨ compact-support xs ⟩
      xs .support                                       ∎

    merge-assoc : ∀ xs ys zs → merge xs (merge ys zs) ≡ merge (merge xs ys) zs
    merge-assoc xs ys zs = support-list-path $
      merge xs (merge ys zs) .support
        ≡⟨⟩
      compact (bwd (merge-list (fwd (xs .support)) (fwd (compact (bwd (merge-list (fwd (ys .support)) (fwd (zs .support))))))))
        ≡⟨ compact-merger (xs .support) (bwd (merge-list (fwd (ys .support)) (fwd (zs .support)))) ⟩
      compact (bwd (merge-list (fwd (xs .support)) (fwd (bwd (merge-list (fwd (ys .support)) (fwd (zs .support)))))))
        ≡⟨ ap (λ ϕ →  compact (bwd (merge-list (fwd (xs .support)) ϕ))) (fwd-bwd (merge-list (fwd (ys .support)) (fwd (zs .support)))) ⟩
      compact (bwd (merge-list (fwd (xs .support)) (merge-list (fwd (ys .support)) (fwd (zs .support)))))
        ≡⟨ ap (λ ϕ → compact (bwd ϕ)) (merge-list-assoc (fwd (xs .support)) (fwd (ys .support)) (fwd (zs .support))) ⟩
      compact (bwd (merge-list (merge-list (fwd (xs .support)) (fwd (ys .support))) (fwd (zs .support))))
        ≡˘⟨ ap (λ ϕ → compact (bwd (merge-list ϕ (fwd (zs .support))))) (fwd-bwd (merge-list (fwd (xs .support)) (fwd (ys .support)))) ⟩
      compact (bwd (merge-list (fwd (bwd (merge-list (fwd (xs .support)) (fwd (ys .support))))) (fwd (zs .support))))
        ≡˘⟨ compact-mergel (bwd (merge-list (fwd (xs .support)) (fwd (ys .support)))) (zs .support) ⟩
      compact (bwd (merge-list (fwd (compact (bwd (merge-list (fwd (xs .support)) (fwd (ys .support)))))) (fwd (zs .support))))
        ≡⟨⟩
      merge (merge xs ys) zs .support ∎
