
module Mugen.Order.LeftInvariantRightCentered where

open import Mugen.Prelude
open import Mugen.Order.StrictOrder

module _ {o r} (A B : Strict-order o r) (b : ⌞ B ⌟) where
  private
    module A = Strict-order A
    module B = Strict-order B

  data _⋉_[_][_<_] (x y : ⌞ A ⌟ × ⌞ B ⌟) : Type (o ⊔ r) where
    biased : fst x ≡ fst y → snd x B.< snd y → _⋉_[_][_<_] x y
    centred : fst x A.< fst y → snd x B.≤ b → b B.≤ snd y → _⋉_[_][_<_] x y

module _ {o r} {A B : Strict-order o r} {b : ⌞ B ⌟} where
  private
    module A = Strict-order A
    module B = Strict-order B

  ⋉-elim
    : ∀ {ℓ}
    → {x y : ⌞ A ⌟ × ⌞ B ⌟}
    → {P : A ⋉ B [ b ][ x < y ] → Type ℓ}
    → ((a1≡a2 : fst x ≡ fst y) → (b1<b2 : snd x B.< snd y) → P (biased a1≡a2 b1<b2))
    → ((a1<a2 : fst x A.< fst y) → (b1≤b : snd x B.≤ b) → (b≤b2 : b B.≤ snd y) → P (centred a1<a2 b1≤b b≤b2))
    → (pf : A ⋉ B [ b ][ x < y ]) → P pf
  ⋉-elim pbiased pcentered (biased a1≡a2 b1<b2) = pbiased a1≡a2 b1<b2
  ⋉-elim pbiased pcentered (centred a1<a2 b1≤b b≤b2) = pcentered a1<a2 b1≤b b≤b2

  ⋉-elim₂
    : ∀ {ℓ}
    → {w x y z : ⌞ A ⌟ × ⌞ B ⌟}
    {P : A ⋉ B [ b ][ w < x ] → A ⋉ B [ b ][ y < z ] → Type ℓ}
    → (∀ (a1≡a2 : fst w ≡ fst x) → (b1<b2 : snd w B.< snd x)
       → (a3≡a4 : fst y ≡ fst z) → (b3<b4 : snd y B.< snd z)
       → P (biased a1≡a2 b1<b2) (biased a3≡a4 b3<b4))
    → (∀ (a1≡a2 : fst w ≡ fst x) → (b1<b2 : snd w B.< snd x)
       → (a3<a4 : fst y A.< fst z) → (b3≤b : snd y B.≤ b) → (b≤b4 : b B.≤ snd z)
       → P (biased a1≡a2 b1<b2) (centred a3<a4 b3≤b b≤b4))
    → (∀ (a1<a2 : fst w A.< fst x) → (b1≤b : snd w B.≤ b) → (b≤b2 : b B.≤ snd x)
       → (a3≡a4 : fst y ≡ fst z) → (b3<b4 : snd y B.< snd z)
       → P (centred a1<a2 b1≤b b≤b2) (biased a3≡a4 b3<b4))
    → (∀ (a1<a2 : fst w A.< fst x) → (b1≤b : snd w B.≤ b) → (b≤b2 : b B.≤ snd x)
       → (a3<a4 : fst y A.< fst z) → (b3≤b : snd y B.≤ b) → (b≤b4 : b B.≤ snd z)
       → P (centred a1<a2 b1≤b b≤b2) (centred a3<a4 b3≤b b≤b4))
    → ∀ p q → P p q
  ⋉-elim₂ {P = P} pbb pbc pcb pcc p q = go p q
    where
      go : ∀ p q → P p q
      go (biased a1≡a2 b1<b2) (biased a3≡a4 b3<b4) = pbb a1≡a2 b1<b2 a3≡a4 b3<b4
      go (biased a1≡a2 b1<b2) (centred a3<a4 b3≤b b≤b4) = pbc a1≡a2 b1<b2 a3<a4 b3≤b b≤b4
      go (centred a1<a2 b1≤b b≤b2) (biased a3≡a4 b3<b4) = pcb a1<a2 b1≤b b≤b2 a3≡a4 b3<b4
      go (centred a1<a2 b1≤b b≤b2) (centred a3<a4 b3≤b b≤b4) = pcc a1<a2 b1≤b b≤b2 a3<a4 b3≤b b≤b4

  ⋉-irrefl : ∀ (x : ⌞ A ⌟ × ⌞ B ⌟) → A ⋉ B [ b ][ x < x ] → ⊥
  ⋉-irrefl (a , b1) = ⋉-elim (λ a1≡a2 b1<b1 → B.<-irrefl b1<b1)
                             (λ a<a b1≤b b≤b2 → A.<-irrefl a<a)

  ⋉-trans : ∀ (x y z : ⌞ A ⌟ × ⌞ B ⌟) → A ⋉ B [ b ][ x < y ] → A ⋉ B [ b ][ y < z ] → A ⋉ B [ b ][ x < z ]
  ⋉-trans x y z x<y y<z =
    ⋉-elim₂ (λ a1≡a2 b1<b2 a2≡a3 b2<b3 → biased (a1≡a2 ∙ a2≡a3) (B.<-trans b1<b2 b2<b3))
            (λ a1≡a2 b1<b2 a2<a3 b2≤b b≤b3 → centred (A.≡+<→< a1≡a2 a2<a3) (B.≤-trans (B.<→≤ b1<b2) b2≤b) b≤b3)
            (λ a1<a2 b1≤b b≤b2 a2≡a3 b2<b3 → centred (A.<+≡→< a1<a2 a2≡a3) b1≤b (B.≤-trans b≤b2 (B.<→≤ b2<b3)))
            (λ a1<a2 b1≤b b≤b2 a2<a3 b2≤b b≤b3 → centred (A.<-trans a1<a2 a2<a3) b1≤b b≤b3)
            x<y y<z

  ⋉-thin : ∀ (x y : ⌞ A ⌟ × ⌞ B ⌟) → is-prop (A ⋉ B [ b ][ x < y ])
  ⋉-thin x y (biased _ _) (biased _ _) = ap₂ biased (A.has-is-set _ _ _ _) (B.<-thin _ _)
  ⋉-thin x y (biased a1≡a2 _) (centred a1<a2 _ _) = absurd (A.<→≠ a1<a2 a1≡a2)
  ⋉-thin x y (centred a1<a2 _ _) (biased a1≡a2 _) = absurd (A.<→≠ a1<a2 a1≡a2)
  ⋉-thin x y (centred a1<a2 ≤b b≤) (centred a1<a2′ ≤b′ b≤′) i =
    centred (A.<-thin a1<a2 a1<a2′ i) (B.≤-thin ≤b ≤b′ i) (B.≤-thin b≤ b≤′ i)


_⋉_[_] : ∀ {o} → (A B : Strict-order o o) → ⌞ B ⌟ → Strict-order o o
A ⋉ B [ b ] = to-strict-order order where
  module A = Strict-order A
  module B = Strict-order B

  order : make-strict-order _ (⌞ A ⌟ × ⌞ B ⌟)
  order .make-strict-order._<_ = A ⋉ B [ b ][_<_]
  order .make-strict-order.<-irrefl {x} = ⋉-irrefl x
  order .make-strict-order.<-trans {x} {y} {z} = ⋉-trans x y z
  order .make-strict-order.<-thin = ⋉-thin _ _
  order .make-strict-order.has-is-set = ×-is-hlevel 2 A.has-is-set B.has-is-set
