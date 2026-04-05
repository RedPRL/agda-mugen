module Mugen.Order.Instances.LexicalSum where

open import Mugen.Prelude
open import Mugen.Order.Lattice
open import Order.Instances.LexicalSum public

import Mugen.Order.Reasoning as Reasoning

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- Joins and Bottoms for Lexicographic Products
-- Section 3.3.4

module _ {A : Poset o r} {B : ⌞ A ⌟ → Poset o' r'} where
  private
    module A = Reasoning A
    module B (x :  ⌞ A ⌟) = Reasoning (B x)

    substᵢ-B : ∀ {x y : ⌞ A ⌟} (p : x ≡ᵢ y) → ⌞ B x ⌟ → ⌞ B y ⌟
    substᵢ-B p x' = substᵢ (λ x → ⌞ B x ⌟) p x'

    substᵢ-B-path
      : ∀ {x y : ⌞ A ⌟}
      → (p q : x ≡ᵢ y) (x' : ⌞ B x ⌟)
      → substᵢ-B p x' ≡ substᵢ-B q x'
    substᵢ-B-path p q x' =
      ap (λ r → substᵢ-B r x') (is-set→is-setᵢ (Poset.Ob-is-set A) _ _ p q)

    substᵢ-B-∙
      : ∀ {x y z1 : ⌞ A ⌟} (p : x ≡ᵢ y) (q : y ≡ᵢ z1) (x' : ⌞ B x ⌟)
      → substᵢ-B (p ∙ᵢ q) x' ≡ substᵢ-B q (substᵢ-B p x')
    substᵢ-B-∙ reflᵢ q x' = refl

  --------------------------------------------------------------------------------
  -- Joins

  -- If the following conditions are true, then 'Lexical-sum A B' has joins:
  -- (1) Both A and all instances of B have joins.
  -- (2) All instances of B have a bottom.
  -- (3) It's decidable in A whether an element is equal to its join with another element.
  lex-has-joins
    : (A-joins : has-joins A) (let module A-joins = has-joins A-joins)
    → (∀ x y → Dec (x ≡ᵢ A-joins.join x y) × Dec (y ≡ᵢ A-joins.join x y))
    → (∀ x → has-joins (B x))
    → (∀ x → has-bottom (B x))
    → has-joins (Lexical-sum A B)

  lex-has-joins A-joins _≡ᵢ∨₁?_ B-joins B-bottom = joins
    where
      module A-joins = has-joins A-joins
      module B-joins (x : ⌞ A ⌟) = has-joins (B-joins x)
      module B-bottom (x : ⌞ A ⌟) = has-bottom (B-bottom x)

      substᵢ-B-join
        : ∀ {x y : ⌞ A ⌟} (p : x ≡ᵢ y) (x' y' : ⌞ B x ⌟)
        → substᵢ-B p (B-joins.join x x' y') ≡ B-joins.join y (substᵢ-B p x') (substᵢ-B p y')
      substᵢ-B-join reflᵢ x y = refl

      substᵢ-B-bot
        : ∀ {x y : ⌞ A ⌟} (p : x ≡ᵢ y)
        → substᵢ-B p (B-bottom.bot x) ≡ B-bottom.bot y
      substᵢ-B-bot reflᵢ = refl

      joins : has-joins (Lexical-sum A B)
      joins .has-joins.join (x , x') (y , y') with x ≡ᵢ∨₁? y
      ... | yes x=ᵢx∨y , yes y=ᵢx∨y = A-joins.join x y , B-joins.join _ (substᵢ-B x=ᵢx∨y x') (substᵢ-B y=ᵢx∨y y')
      ... | yes x=ᵢx∨y , no  _      = A-joins.join x y , substᵢ-B x=ᵢx∨y x'
      ... | no  _      , yes y=ᵢx∨y = A-joins.join x y , substᵢ-B y=ᵢx∨y y'
      ... | no  _      , no  _      = A-joins.join x y , B-bottom.bot (A-joins.join x y)
      joins .has-joins.joinl {x , _} {y , _} with x ≡ᵢ∨₁? y
      ... | yes x=ᵢx∨y , yes _ =
        A-joins.joinl , λ p →
        B.=+≤→≤ (A-joins.join x y)
          (substᵢ-B-path p x=ᵢx∨y _)
          (B-joins.joinl (A-joins.join x y))
      ... | yes x=ᵢx∨y , no  _ =
        A-joins.joinl , λ p →
        B.=→≤ (A-joins.join x y)
          (substᵢ-B-path p x=ᵢx∨y _)
      ... | no  x≠ᵢx∨y , yes _ = A-joins.joinl , λ p → absurd (x≠ᵢx∨y p)
      ... | no  x≠ᵢx∨y , no  _ = A-joins.joinl , λ p → absurd (x≠ᵢx∨y p)
      joins .has-joins.joinr {x , _} {y , _} with x ≡ᵢ∨₁? y
      ... | yes _ , yes y=ᵢx∨y =
        A-joins.joinr , λ p →
        B.=+≤→≤ (A-joins.join x y)
          (substᵢ-B-path p y=ᵢx∨y _)
          (B-joins.joinr (A-joins.join x y))
      ... | yes _ , no  y≠ᵢx∨y = A-joins.joinr , λ p → absurd (y≠ᵢx∨y p)
      ... | no  _ , yes y=ᵢx∨y =
        A-joins.joinr , λ p →
        B.=→≤ (A-joins.join x y)
          (substᵢ-B-path p y=ᵢx∨y _)
      ... | no  _ , no  y≠ᵢx∨y = A-joins.joinr , λ p → absurd (y≠ᵢx∨y p)
      joins .has-joins.universal {x , x'} {y , y'} {_ , z2} x≤z y≤z with x ≡ᵢ∨₁? y
      ... | yes x=ᵢx∨y , yes y=ᵢx∨y =
        A-joins.universal (x≤z .fst) (y≤z .fst) , λ x∨y=ᵢz1 →
        B.=+≤→≤ _
          (substᵢ-B-join x∨y=ᵢz1 (substᵢ-B x=ᵢx∨y x') (substᵢ-B y=ᵢx∨y y'))
          (B-joins.universal _
            (B.=+≤→≤ _
              (sym (substᵢ-B-∙ x=ᵢx∨y x∨y=ᵢz1 x'))
              (x≤z .snd (x=ᵢx∨y ∙ᵢ x∨y=ᵢz1)))
            (B.=+≤→≤ _
              (sym (substᵢ-B-∙ y=ᵢx∨y x∨y=ᵢz1 y'))
              (y≤z .snd (y=ᵢx∨y ∙ᵢ x∨y=ᵢz1))))
      ... | yes x=ᵢx∨y , no  y≠ᵢx∨y =
        A-joins.universal (x≤z .fst) (y≤z .fst) , λ x∨y=ᵢz1 →
        B.=+≤→≤ _
          (sym (substᵢ-B-∙ x=ᵢx∨y x∨y=ᵢz1 x'))
          (x≤z .snd (x=ᵢx∨y ∙ᵢ x∨y=ᵢz1))
      ... | no  x≠ᵢx∨y , yes y=ᵢx∨y =
        A-joins.universal (x≤z .fst) (y≤z .fst) , λ x∨y=ᵢz1 →
        B.=+≤→≤ _
          (sym (substᵢ-B-∙ y=ᵢx∨y x∨y=ᵢz1 y'))
          (y≤z .snd (y=ᵢx∨y ∙ᵢ x∨y=ᵢz1))
      ... | no  x≠ᵢx∨y , no  y≠ᵢx∨y =
        A-joins.universal (x≤z .fst) (y≤z .fst) , λ x∨y=ᵢz1 →
        B.=+≤→≤ _
          (substᵢ-B-bot x∨y=ᵢz1)
          (B-bottom.is-bottom _)

  --------------------------------------------------------------------------------
  -- Bottoms

  lex-has-bottom : has-bottom A → (∀ x → has-bottom (B x)) → has-bottom (Lexical-sum A B)
  lex-has-bottom A-bottom B-bottom = bottom
    where
      module A-bottom = has-bottom (A-bottom)
      module B-bottom (x : ⌞ A ⌟) = has-bottom (B-bottom x)

      substᵢ-B-bot
        : ∀ {x y : ⌞ A ⌟} (p : x ≡ᵢ y)
        → substᵢ-B p (B-bottom.bot x) ≡ B-bottom.bot y
      substᵢ-B-bot reflᵢ = refl

      bottom : has-bottom (Lexical-sum A B)
      bottom .has-bottom.bot = A-bottom.bot , B-bottom.bot A-bottom.bot
      bottom .has-bottom.is-bottom = A-bottom.is-bottom , λ _ →
        B.=+≤→≤ _ (substᵢ-B-bot _) (B-bottom.is-bottom _)
