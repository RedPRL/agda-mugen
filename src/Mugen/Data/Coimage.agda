module Mugen.Data.Coimage where

open import Mugen.Prelude

private variable
  ℓ ℓ′ : Level
  A B : Type ℓ
  f : A → B

data Coim {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} (f : A → B) : Type (ℓ ⊔ ℓ′) where
  inc  : A → Coim f
  glue : ∀ x y → f x ≡ f y → inc x ≡ inc y
  squash : is-set (Coim f)

--------------------------------------------------------------------------------
-- Eliminators

Coim-elim-prop : ∀ {ℓ} {f : A → B} {C : Coim f → Type ℓ}
                 → (∀ x → is-prop (C x))
                 → (∀ x → C (inc x))
                 → ∀ x → C x
Coim-elim-prop cprop cinc (inc x) = cinc x
Coim-elim-prop cprop cinc (glue x y p i) =
  is-prop→pathp (λ i → cprop (glue x y p i)) (cinc x) (cinc y) i
Coim-elim-prop cprop cinc (squash x y p q i j) =
  is-prop→squarep (λ i j → cprop (squash x y p q i j))
    (λ i → map x) (λ i → map (p i)) (λ i → map (q i)) (λ i → map y) i j
    where
      map = Coim-elim-prop cprop cinc

Coim-elim-prop₂ : ∀ {ℓ} {f g : A → B} {C : Coim f → Coim g → Type ℓ}
                  → (∀ x y → is-prop (C x y))
                  → (∀ x y → C (inc x) (inc y))
                  → ∀ x y → C x y
Coim-elim-prop₂ cprop cinc =
  Coim-elim-prop (λ x → Π-is-hlevel 1 λ y → cprop x y)
    (λ x → Coim-elim-prop (cprop (inc x)) (cinc x))

Coim-elim-prop₃ : ∀ {ℓ} {f : A → B} {C : Coim f → Coim f → Coim f → Type ℓ}
                  → (∀ x y z → is-prop (C x y z))
                  → (∀ x y z → C (inc x) (inc y) (inc z))
                  → ∀ x y z → C x y z
Coim-elim-prop₃ cprop cinc =
  Coim-elim-prop₂ (λ x y → Π-is-hlevel 1 λ z → cprop x y z)
    (λ x y → Coim-elim-prop (cprop (inc x) (inc y)) (cinc x y))

--------------------------------------------------------------------------------
-- Recursors

Coim-rec : ∀ {ℓ} {C : Type ℓ} {f : A → B}
         → is-set C
         → (h : A → C)
         → (∀ x y → f x ≡ f y → h x ≡ h y)
         → Coim f → C
Coim-rec cset h h-pres (inc x) = h x
Coim-rec cset h h-pres (glue x y q i) = h-pres x y q i
Coim-rec cset h h-pres (squash x y p q i j) =
  cset (g x) (g y) (λ i → g (p i)) (λ i → g (q i)) i j
  where g = Coim-rec cset h h-pres


Coim-rec₂ : ∀ {ℓ} {C : Type ℓ} {f : A → B}
            → is-set C
            → (h : A → A → C)
            → (∀ w x y z → f w ≡ f x → f y ≡ f z → h w y ≡ h x z)
            → Coim f → Coim f → C
Coim-rec₂ cset h h-pres (inc x) (inc y) = h x y
Coim-rec₂ cset h h-pres (inc x) (glue y z p i) =
  h-pres x x y z refl p i
Coim-rec₂ cset h h-pres (inc x) (squash y z p q i j) =
  cset (Coim-rec₂ cset h h-pres (inc x) y)
    (Coim-rec₂ cset h h-pres (inc x) z)
    (λ j → Coim-rec₂ cset h h-pres (inc x) (p j))
    (λ j → Coim-rec₂ cset h h-pres (inc x) (q j))
    i j
Coim-rec₂ cset h h-pres (glue w x p i) (inc y) =
  h-pres w x y y p refl i
Coim-rec₂ cset h h-pres (glue w x p i) (glue y z q j) =
   is-set→squarep (λ i j → cset)
     (λ j → h-pres w x y y p refl j)
     (λ j → h-pres w w y z refl q j)
     (λ j → h-pres x x y z refl q j)
     (λ j → h-pres w x z z p refl j)
     i j
Coim-rec₂ cset h h-pres (glue w x p i) (squash y z q r j k) =
  is-hlevel-suc 2 cset
    (map (glue w x p i) y)
    (map (glue w x p i) z)
    (λ j → map (glue w x p i) (q j))
    (λ j → map (glue w x p i) (r j))
    (λ i j → exp i j)
    (λ i j → exp i j)
    i j k
  where
    map = Coim-rec₂ cset h h-pres
    exp = cset
      (map (glue w x p i) y)
      (map (glue w x p i) z)
      (λ j → map (glue w x p i) (q j))
      (λ j → map (glue w x p i) (r j))

Coim-rec₂ cset h h-pres (squash w x p q i j) z =
  cset (map w z) (map x z) (λ j → map (p j) z) (λ j → map (q j) z) i j
  where
    map = Coim-rec₂ cset h h-pres
