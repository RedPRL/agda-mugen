open import Mugen.Prelude
open import Mugen.Data.List

import Mugen.Order.Reasoning as Reasoning

--------------------------------------------------------------------------------
-- Lexicographical order on lists

module Mugen.Order.Instances.LexicalList {o r} (A : Poset o r) where
  private
    module A = Reasoning A

  data _≤_ : List ⌞ A ⌟ → List ⌞ A ⌟ → Type (o ⊔ r) where
    []≤ : ∀ {ys} → [] ≤ ys
    _∷≤_ : ∀ {x xs y ys} → x A.≤ y → (x ≡ y → xs ≤ ys) → (x ∷ xs) ≤ (y ∷ ys)

  private
    abstract
      ≤-refl : ∀ (xs : List ⌞ A ⌟) → xs ≤ xs
      ≤-refl [] = []≤
      ≤-refl (x ∷ xs) = A.≤-refl ∷≤ λ _ → ≤-refl xs

      ≤-trans : ∀ (xs ys zs : List ⌞ A ⌟) → xs ≤ ys → ys ≤ zs → xs ≤ zs
      ≤-trans [] ys zs nil≤ _ = []≤
      ≤-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (x≤y ∷≤ xs≤ys) (y≤z ∷≤ ys≤zs) =
        A.≤-trans x≤y y≤z ∷≤ λ x=z →
        ≤-trans xs ys zs (xs≤ys (A.≤-antisym'-l x≤y y≤z x=z)) (ys≤zs (A.≤-antisym'-r x≤y y≤z x=z))

      ≤-antisym : ∀ (xs ys : List ⌞ A ⌟) → xs ≤ ys → ys ≤ xs → xs ≡ ys
      ≤-antisym [] [] []≤ []≤ = refl
      ≤-antisym [] (y ∷ ys) nil≤ ()
      ≤-antisym (x ∷ xs) [] ()
      ≤-antisym (x ∷ xs) (y ∷ ys) (x≤y ∷≤ xs≤ys) (y≤x ∷≤ ys≤xs) =
        let x=y = A.≤-antisym x≤y y≤x in ap₂ _∷_ x=y $ ≤-antisym xs ys (xs≤ys x=y) (ys≤xs (sym x=y))

      ≤-thin : ∀ (xs ys : List ⌞ A ⌟) → is-prop (xs ≤ ys)
      ≤-thin [] ys []≤ []≤ = refl
      ≤-thin (x ∷ xs) [] ()
      ≤-thin (x ∷ xs) (y ∷ ys) (x≤y ∷≤ xs≤ys) (x≤y' ∷≤ xs≤ys') = ap₂ _∷≤_ (A.≤-thin x≤y x≤y') $
        funext λ p → ≤-thin xs ys (xs≤ys p) (xs≤ys' p)

  --------------------------------------------------------------------------------
  -- Poset Bundle

  poset : Poset o (o ⊔ r)
  poset .Poset.Ob = List ⌞ A ⌟
  poset .Poset._≤_ = _≤_
  poset .Poset.≤-thin = ≤-thin _ _
  poset .Poset.≤-refl = ≤-refl _
  poset .Poset.≤-trans = ≤-trans _ _ _
  poset .Poset.≤-antisym = ≤-antisym _ _
