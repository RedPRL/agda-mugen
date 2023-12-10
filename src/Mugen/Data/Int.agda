module Mugen.Data.Int where

open import Data.Nat

open import Mugen.Prelude

open import Data.Int.Inductive public

--------------------------------------------------------------------------------
-- General Facts

pattern 0ℤ = pos zero

-_ : Nat → Int
- zero = pos zero
- suc x = negsuc x

abs : Int → Nat
abs (pos n) = n
abs (negsuc n) = suc n

pos≠negsuc : ∀ {m n} → pos m ≡ negsuc n → ⊥
pos≠negsuc p = subst distinguish p tt where
  distinguish : Int → Type
  distinguish (pos _) = ⊤
  distinguish (negsuc _) = ⊥

negsuc≠pos : ∀ {m n} → negsuc m ≡ pos n → ⊥
negsuc≠pos = pos≠negsuc ⊙ sym

Int-is-set : is-set Int
Int-is-set = Discrete→is-set Discrete-Int

instance
  H-Level-Int : ∀ {n} → H-Level Int (2 + n)
  H-Level-Int = basic-instance 2 Int-is-set

--------------------------------------------------------------------------------
-- Algebra

infixr 5 _+ℤ_
_+ℤ_ : Int → Int → Int
pos zero +ℤ y = y
pos (suc x) +ℤ y = suc-int (pos x +ℤ y)
negsuc zero +ℤ y = pred-int y
negsuc (suc x) +ℤ y = pred-int (negsuc x +ℤ y)

maxℤ : Int → Int → Int
maxℤ (pos x) (pos y) = pos (max x y)
maxℤ (pos x) (negsuc _) = pos x
maxℤ (negsuc _) (pos y) = pos y
maxℤ (negsuc x) (negsuc y) = negsuc (min x y)

-- Properties

abstract
  +ℤ-idl : ∀ x → 0ℤ +ℤ x ≡ x
  +ℤ-idl x = refl

  +ℤ-idr : ∀ x → x +ℤ 0ℤ ≡ x
  +ℤ-idr (pos zero) = refl
  +ℤ-idr (pos (suc n)) = ap suc-int $ +ℤ-idr (pos n)
  +ℤ-idr (negsuc zero) = refl
  +ℤ-idr (negsuc (suc n)) = ap pred-int $ +ℤ-idr (negsuc n)

  +ℤ-succl : ∀ x y → suc-int x +ℤ y ≡ suc-int (x +ℤ y)
  +ℤ-succl (pos x) y = refl
  +ℤ-succl (negsuc zero) y = sym $ suc-pred y
  +ℤ-succl (negsuc (suc x)) y = sym $ suc-pred (negsuc x +ℤ y)

  +ℤ-succr : ∀ x y → x +ℤ suc-int y ≡ suc-int (x +ℤ y)
  +ℤ-succr (pos zero) y = refl
  +ℤ-succr (pos (suc x)) y = ap suc-int $ +ℤ-succr (pos x) y
  +ℤ-succr (negsuc zero) y = pred-suc y ∙ sym (suc-pred y)
  +ℤ-succr (negsuc (suc x)) y =
    ap pred-int (+ℤ-succr (negsuc x) y) ∙ pred-suc (negsuc x +ℤ y) ∙ sym (suc-pred (negsuc x +ℤ y))

  +ℤ-predl : ∀ x y → pred-int x +ℤ y ≡ pred-int (x +ℤ y)
  +ℤ-predl (pos zero) y = refl
  +ℤ-predl (pos (suc x)) y = sym $ pred-suc (pos x +ℤ y)
  +ℤ-predl (negsuc zero) y = refl
  +ℤ-predl (negsuc (suc _)) y = refl

  +ℤ-predr : ∀ x y → x +ℤ pred-int y ≡ pred-int (x +ℤ y)
  +ℤ-predr (pos zero) y = refl
  +ℤ-predr (pos (suc x)) y =
    ap suc-int (+ℤ-predr (pos x) y) ∙ suc-pred (pos x +ℤ y) ∙ sym (pred-suc (pos x +ℤ y))
  +ℤ-predr (negsuc zero) y = refl
  +ℤ-predr (negsuc (suc x)) y =
    ap pred-int (+ℤ-predr (negsuc x) y)

  +ℤ-associative : ∀ x y z → x +ℤ (y +ℤ z) ≡ (x +ℤ y) +ℤ z
  +ℤ-associative (pos zero) y z = refl
  +ℤ-associative (pos (suc x)) y z =
    suc-int (pos x +ℤ (y +ℤ z)) ≡⟨ ap suc-int (+ℤ-associative (pos x) y z) ⟩
    suc-int ((pos x +ℤ y) +ℤ z) ≡˘⟨ +ℤ-succl (pos x +ℤ y) z ⟩
    (suc-int (pos x +ℤ y) +ℤ z) ∎
  +ℤ-associative (negsuc zero) y z = sym $ +ℤ-predl y z
  +ℤ-associative (negsuc (suc x)) y z =
    pred-int (negsuc x +ℤ (y +ℤ z)) ≡⟨ ap pred-int (+ℤ-associative (negsuc x) y z) ⟩
    pred-int ((negsuc x +ℤ y) +ℤ z) ≡˘⟨ +ℤ-predl (negsuc x +ℤ y) z ⟩
    (pred-int (negsuc x +ℤ y) +ℤ z) ∎

  +ℤ-negate : ∀ x y → - (x + y) ≡ (- x) +ℤ (- y)
  +ℤ-negate zero y = refl
  +ℤ-negate (suc zero) zero = refl
  +ℤ-negate (suc zero) (suc y) = refl
  +ℤ-negate (suc (suc x)) y = ap pred-int $ +ℤ-negate (suc x) y

  +ℤ-pos : ∀ x y → pos (x + y) ≡ pos x +ℤ pos y
  +ℤ-pos zero y = refl
  +ℤ-pos (suc x) y = ap suc-int $ +ℤ-pos x y

  negate-injective : ∀ x y → (- x) ≡ (- y) → x ≡ y
  negate-injective zero zero p = refl
  negate-injective zero (suc y) p = absurd (pos≠negsuc p)
  negate-injective (suc x) zero p = absurd (pos≠negsuc (sym p))
  negate-injective (suc x) (suc y) p = ap suc (negsuc-injective p)

  suc-int-injective : ∀ x y → suc-int x ≡ suc-int y → x ≡ y
  suc-int-injective (pos _) (pos _) p = ap pred-int p
  suc-int-injective (pos _) (negsuc zero) p = ap pred-int p
  suc-int-injective (pos _) (negsuc (suc _)) p = ap pred-int p
  suc-int-injective (negsuc zero) (pos _) p = ap pred-int p
  suc-int-injective (negsuc zero) (negsuc zero) p = ap pred-int p
  suc-int-injective (negsuc zero) (negsuc (suc _)) p = ap pred-int p
  suc-int-injective (negsuc (suc _)) (pos _) p = ap pred-int p
  suc-int-injective (negsuc (suc _)) (negsuc zero) p = ap pred-int p
  suc-int-injective (negsuc (suc _)) (negsuc (suc _)) p = ap pred-int p

  pred-int-injective : ∀ x y → pred-int x ≡ pred-int y → x ≡ y
  pred-int-injective (pos zero) (pos zero) p = ap suc-int p
  pred-int-injective (pos zero) (pos (suc _)) p = ap suc-int p
  pred-int-injective (pos zero) (negsuc _) p = ap suc-int p
  pred-int-injective (pos (suc _)) (pos zero) p = ap suc-int p
  pred-int-injective (pos (suc _)) (pos (suc _)) p = ap suc-int p
  pred-int-injective (pos (suc _)) (negsuc _) p = ap suc-int p
  pred-int-injective (negsuc _) (pos zero) p = ap suc-int p
  pred-int-injective (negsuc _) (pos (suc _)) p = ap suc-int p
  pred-int-injective (negsuc _) (negsuc _) p = ap suc-int p

  +ℤ-injectiver : ∀ k x y → k +ℤ x ≡ k +ℤ y → x ≡ y
  +ℤ-injectiver (pos zero) x y p = p
  +ℤ-injectiver (pos (suc k)) x y p =
    +ℤ-injectiver (pos k) x y $ suc-int-injective (pos k +ℤ x) (pos k +ℤ y) p
  +ℤ-injectiver (negsuc zero) x y p = pred-int-injective x y p
  +ℤ-injectiver (negsuc (suc k)) x y p =
    +ℤ-injectiver (negsuc k) x y $ pred-int-injective (negsuc k +ℤ x) (negsuc k +ℤ y) p

--------------------------------------------------------------------------------
-- Order

_≤ℤ_ : Int → Int → Type
pos x ≤ℤ pos y = x ≤ y
pos x ≤ℤ negsuc y = ⊥
negsuc x ≤ℤ pos y = ⊤
negsuc x ≤ℤ negsuc y = y ≤ x

abstract
  ≤ℤ-refl : ∀ x → x ≤ℤ x
  ≤ℤ-refl (pos x) = ≤-refl
  ≤ℤ-refl (negsuc x) = ≤-refl

  ≤ℤ-trans : ∀ x y z → x ≤ℤ y → y ≤ℤ z → x ≤ℤ z
  ≤ℤ-trans (pos x) (pos y) (pos z) x≤y y≤z = ≤-trans x≤y y≤z
  ≤ℤ-trans (negsuc x) (pos y) (pos z) x≤y y≤z = tt
  ≤ℤ-trans (negsuc x) (negsuc y) (pos z) x≤y y≤z = tt
  ≤ℤ-trans (negsuc x) (negsuc y) (negsuc z) x≤y y≤z = ≤-trans y≤z x≤y

  ≤ℤ-antisym : ∀ x y → x ≤ℤ y → y ≤ℤ x → x ≡ y
  ≤ℤ-antisym (pos x) (pos y) x≤y y≤z = ap pos $ ≤-antisym x≤y y≤z
  ≤ℤ-antisym (negsuc x) (negsuc y) x≤y y≤z = ap negsuc $ ≤-antisym y≤z x≤y

  ≤ℤ-is-prop : ∀ x y → is-prop (x ≤ℤ y)
  ≤ℤ-is-prop (pos x) (pos y) = ≤-is-prop
  ≤ℤ-is-prop (pos x) (negsuc y) = hlevel 1
  ≤ℤ-is-prop (negsuc x) (pos y) = hlevel 1
  ≤ℤ-is-prop (negsuc x) (negsuc y) = ≤-is-prop

  suc-int-invariant : ∀ x y → x ≤ℤ y → suc-int x ≤ℤ suc-int y
  suc-int-invariant (pos x) (pos y) x≤y = s≤s x≤y
  suc-int-invariant (pos x) (negsuc y) ()
  suc-int-invariant (negsuc zero) (pos y) _ = 0≤x
  suc-int-invariant (negsuc zero) (negsuc zero) _ = 0≤x
  suc-int-invariant (negsuc zero) (negsuc (suc _)) ()
  suc-int-invariant (negsuc (suc x)) (pos y) _ = tt
  suc-int-invariant (negsuc (suc x)) (negsuc zero) _ = tt
  suc-int-invariant (negsuc (suc x)) (negsuc (suc y)) (s≤s x≥y) = x≥y

  pred-int-invariant : ∀ x y → x ≤ℤ y → pred-int x ≤ℤ pred-int y
  pred-int-invariant (pos zero) (pos zero) _ = 0≤x
  pred-int-invariant (pos zero) (pos (suc _)) _ = tt
  pred-int-invariant (pos x) (negsuc y) ()
  pred-int-invariant (pos (suc x)) (pos zero) ()
  pred-int-invariant (pos (suc x)) (pos (suc y)) (s≤s x≥y) = x≥y
  pred-int-invariant (negsuc x) (pos zero) _ = 0≤x
  pred-int-invariant (negsuc x) (pos (suc y)) _ = tt
  pred-int-invariant (negsuc x) (negsuc y) x≤y = s≤s x≤y

  +ℤ-left-invariant : ∀ x y z → y ≤ℤ z → (x +ℤ y) ≤ℤ (x +ℤ z)
  +ℤ-left-invariant (pos zero) y z y≤z = y≤z
  +ℤ-left-invariant (pos (suc x)) y z y≤z =
    suc-int-invariant _ _ $ +ℤ-left-invariant (pos x) y z y≤z
  +ℤ-left-invariant (negsuc zero) y z y≤z =
    pred-int-invariant _ _ y≤z
  +ℤ-left-invariant (negsuc (suc x)) y z y≤z =
    pred-int-invariant _ _ $ +ℤ-left-invariant (negsuc x) y z y≤z

  +ℤ-right-invariant : ∀ x y z → x ≤ℤ y → (x +ℤ z) ≤ℤ (y +ℤ z)
  +ℤ-right-invariant x y (pos zero) x≤y =
    coe1→0 (λ i → +ℤ-idr x i ≤ℤ +ℤ-idr y i) x≤y
  +ℤ-right-invariant x y (pos (suc z)) x≤y =
    coe1→0 (λ i → +ℤ-succr x (pos z) i ≤ℤ +ℤ-succr y (pos z) i) $
    suc-int-invariant _ _ $ +ℤ-right-invariant x y (pos z) x≤y
  +ℤ-right-invariant x y (negsuc zero) x≤y =
    coe1→0 (λ i → +ℤ-predr x 0ℤ i ≤ℤ +ℤ-predr y 0ℤ i) $
    pred-int-invariant _ _ $ coe1→0 (λ i → +ℤ-idr x i ≤ℤ +ℤ-idr y i) x≤y
  +ℤ-right-invariant x y (negsuc (suc z)) x≤y =
    coe1→0 (λ i → +ℤ-predr x (negsuc z) i ≤ℤ +ℤ-predr y (negsuc z) i) $
    pred-int-invariant _ _ $ +ℤ-right-invariant x y (negsuc z) x≤y

  maxℤ-≤l : ∀ x y → x ≤ℤ maxℤ x y
  maxℤ-≤l (pos x) (pos y) = max-≤l x y
  maxℤ-≤l (pos x) (negsuc y) = ≤-refl
  maxℤ-≤l (negsuc x) (pos y) = tt
  maxℤ-≤l (negsuc x) (negsuc y) = min-≤l x y

  maxℤ-≤r : ∀ x y → y ≤ℤ maxℤ x y
  maxℤ-≤r (pos x) (pos y) = max-≤r x y
  maxℤ-≤r (pos x) (negsuc y) = tt
  maxℤ-≤r (negsuc x) (pos y) = ≤-refl
  maxℤ-≤r (negsuc x) (negsuc y) = min-≤r x y

  maxℤ-is-lub : ∀ x y z → x ≤ℤ z → y ≤ℤ z → maxℤ x y ≤ℤ z
  maxℤ-is-lub (pos x) (pos y) (pos z) x≤z y≤z = max-is-lub x y z x≤z y≤z
  maxℤ-is-lub (pos x) (negsuc y) (pos z) x≤z y≤z = x≤z
  maxℤ-is-lub (negsuc x) (pos y) (pos z) x≤z y≤z = y≤z
  maxℤ-is-lub (negsuc x) (negsuc y) (pos z) x≤z y≤z = tt
  maxℤ-is-lub (negsuc x) (negsuc y) (negsuc z) x≤z y≤z = min-is-glb x y z x≤z y≤z

  negate-anti-mono : ∀ x y → x ≤ y → (- y) ≤ℤ (- x)
  negate-anti-mono zero zero _ = 0≤x
  negate-anti-mono zero (suc y) x≤y = tt
  negate-anti-mono (suc x) (suc y) (s≤s x≤y) = x≤y
  
  negate-anti-full : ∀ x y → (- y) ≤ℤ (- x) → x ≤ y
  negate-anti-full zero _ _ = 0≤x
  negate-anti-full (suc x) zero ()
  negate-anti-full (suc x) (suc y) x≤y = (s≤s x≤y)
  
  negate-min : ∀ x y → - (min x y) ≡ maxℤ (- x) (- y)
  negate-min zero zero = refl
  negate-min zero (suc y) = refl
  negate-min (suc x) zero = refl
  negate-min (suc x) (suc y) = refl
