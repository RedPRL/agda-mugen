module Mugen.Algebra.Displacement.Action where

open import Mugen.Prelude
open import Mugen.Algebra.Displacement

import Mugen.Order.Reasoning as Reasoning

--------------------------------------------------------------------------------
-- Right Displacement Actions

record Right-displacement-action
  {o r o' r'} (A : Poset o r) {B : Poset o' r'} (Y : Displacement-on B)
  : Type (o ⊔ r ⊔ o' ⊔ r')
  where
  private
    module A = Reasoning A
    module B = Reasoning B
    module Y = Displacement-on Y
  field
    _⋆_ : ⌞ A ⌟ → ⌞ B.Ob ⌟ → ⌞ A ⌟
    identity : ∀ {a} → a ⋆ Y.ε ≡ a
    compatible : ∀ {a x y} → a ⋆ (x Y.⊗ y) ≡ (a ⋆ x) ⋆ y
    strict-invariant : ∀ {a x y} → x B.≤ y → (a ⋆ x) A.≤[ x ≡ y ] (a ⋆ y)

  abstract
    invariant : ∀ {a x y} → x B.≤ y → (a ⋆ x) A.≤ (a ⋆ y)
    invariant {a} {x} {y} x≤y = strict-invariant {a} {x} {y} x≤y .fst

    injectiver-on-related : ∀ {a} {x} {y} → x B.≤ y → (a ⋆ x) ≡ (a ⋆ y) → x ≡ y
    injectiver-on-related {a} {x} {y} x≤y = strict-invariant {a} {x} {y} x≤y .snd

module _ where
  open Right-displacement-action

  opaque
    Right-displacement-action-path
      : ∀ {o r o' r'}
      → {A : Poset o r} {B : Poset o' r'} {Y : Displacement-on B}
      → (α β : Right-displacement-action A Y)
      → (∀ {a b} → (α ._⋆_ a b) ≡ (β ._⋆_ a b))
      → α ≡ β
    Right-displacement-action-path α β p i ._⋆_ a b = p {a} {b} i
    Right-displacement-action-path {A = A} {Y = Y} α β p i .identity {a} =
      is-prop→pathp
        (λ i → Poset.Ob-is-set A (p {a} {Y .Displacement-on.ε} i) _)
        (α .identity {a}) (β .identity {a}) i
    Right-displacement-action-path {A = A} {Y = Y} α β p i .compatible {a} {x} {y} =
      is-prop→pathp
        (λ i → Poset.Ob-is-set A
          (p {a} {Y .Displacement-on._⊗_ x y} i)
          (p {p {a} {x} i} {y} i))
        (α .compatible {a} {x} {y}) (β .compatible {a} {x} {y}) i
    Right-displacement-action-path {A = A} {B = B} α β p i .strict-invariant {a} {x} {y} q =
      is-prop→pathp
        (λ i → Reasoning.≤[]-is-hlevel A {x = p {a} {x} i} {y = p {a} {y} i} 0 (Poset.Ob-is-set B _ _))
        (α .strict-invariant {a} {x} {y} q) (β .strict-invariant {a} {x} {y} q) i

instance
  Right-actionlike-displacement-action
    : ∀ {o r o' r'}
    → Right-actionlike (λ A (B : Σ _ Displacement-on) → Right-displacement-action {o} {r} {o'} {r'} A (B .snd))
  Right-actionlike.⟦ Right-actionlike-displacement-action ⟧ʳ =
    Right-displacement-action._⋆_
  Right-actionlike-displacement-action .Right-actionlike.extʳ =
    Right-displacement-action-path _ _
