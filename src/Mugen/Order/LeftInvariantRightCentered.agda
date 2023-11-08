
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
    trunc : ∀ (p q : _⋉_[_][_<_] x y) → p ≡ q

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
    → (∀ pf → is-prop (P pf))
    → (pf : A ⋉ B [ b ][ x < y ]) → P pf
  ⋉-elim pbiased pcentered pprop (biased a1≡a2 b1<b2) = pbiased a1≡a2 b1<b2
  ⋉-elim pbiased pcentered pprop (centred a1<a2 b1≤b b≤b2) = pcentered a1<a2 b1≤b b≤b2
  ⋉-elim pbiased pcentered pprop (trunc p q i) =
    is-prop→pathp (λ j → pprop (trunc p q j))
      (⋉-elim pbiased pcentered pprop p)
      (⋉-elim pbiased pcentered pprop q)
      i

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
    → (∀ p q → is-prop (P p q))
    → ∀ p q → P p q
  ⋉-elim₂ {P = P} pbb pbc pcb pcc pprop p q = go p q
    where
      go : ∀ p q → P p q
      go (biased a1≡a2 b1<b2) (biased a3≡a4 b3<b4) = pbb a1≡a2 b1<b2 a3≡a4 b3<b4
      go (biased a1≡a2 b1<b2) (centred a3<a4 b3≤b b≤b4) = pbc a1≡a2 b1<b2 a3<a4 b3≤b b≤b4
      go (biased a1≡a2 b1<b2) (trunc p q i) =
        is-prop→pathp (λ j → pprop (biased a1≡a2 b1<b2) (trunc p q j))
                      (go (biased a1≡a2 b1<b2) p)
                      (go (biased a1≡a2 b1<b2) q)
                      i
      go (centred a1<a2 b1≤b b≤b2) (biased a3≡a4 b3<b4) = pcb a1<a2 b1≤b b≤b2 a3≡a4 b3<b4
      go (centred a1<a2 b1≤b b≤b2) (centred a3<a4 b3≤b b≤b4) = pcc a1<a2 b1≤b b≤b2 a3<a4 b3≤b b≤b4
      go (centred a1<a2 b1≤b b≤b2) (trunc p q i) =
        is-prop→pathp (λ j → pprop (centred a1<a2 b1≤b b≤b2) (trunc p q j))
          (go (centred a1<a2 b1≤b b≤b2) p)
          (go (centred a1<a2 b1≤b b≤b2) q)
          i
      go (trunc p q i) r =
        is-prop→pathp (λ j → pprop (trunc p q j) r)
          (go p r)
          (go q r)
          i

  ⋉-irrefl : ∀ (x : ⌞ A ⌟ × ⌞ B ⌟) → A ⋉ B [ b ][ x < x ] → ⊥
  ⋉-irrefl (a , b1) = ⋉-elim (λ a1≡a2 b1<b1 → B.<-irrefl b1<b1)
                             (λ a<a b1≤b b≤b2 → A.<-irrefl a<a)
                             (λ _ → hlevel 1)

  ⋉-trans : ∀ (x y z : ⌞ A ⌟ × ⌞ B ⌟) → A ⋉ B [ b ][ x < y ] → A ⋉ B [ b ][ y < z ] → A ⋉ B [ b ][ x < z ]
  ⋉-trans x y z x<y y<z =
    ⋉-elim₂ (λ a1≡a2 b1<b2 a2≡a3 b2<b3 → biased (a1≡a2 ∙ a2≡a3) (B.<-trans b1<b2 b2<b3))
            (λ a1≡a2 b1<b2 a2<a3 b2≤b b≤b3 → centred (A.≡-transl a1≡a2 a2<a3) (B.≤-trans (B.<→≤ b1<b2) b2≤b) b≤b3)
            (λ a1<a2 b1≤b b≤b2 a2≡a3 b2<b3 → centred (A.≡-transr a1<a2 a2≡a3) b1≤b (B.≤-trans b≤b2 (B.<→≤ b2<b3)))
            (λ a1<a2 b1≤b b≤b2 a2<a3 b2≤b b≤b3 → centred (A.<-trans a1<a2 a2<a3) b1≤b b≤b3)
            (λ _ _ → trunc) x<y y<z


_⋉_[_] : ∀ {o} → (A B : Strict-order o o) → ⌞ B ⌟ → Strict-order o o
A ⋉ B [ b ] = to-strict-order order where
  module A = Strict-order A
  module B = Strict-order B

  order : make-strict-order _ (⌞ A ⌟ × ⌞ B ⌟)
  order .make-strict-order._<_ = A ⋉ B [ b ][_<_]
  order .make-strict-order.<-irrefl {x} = ⋉-irrefl x
  order .make-strict-order.<-trans {x} {y} {z} = ⋉-trans x y z
  order .make-strict-order.<-thin = trunc
  order .make-strict-order.has-is-set = ×-is-hlevel 2 A.has-is-set B.has-is-set 
