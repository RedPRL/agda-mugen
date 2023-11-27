module Mugen.Data.Int where

open import Mugen.Prelude
open import Mugen.Order.Poset
open import Mugen.Data.Nat

data Int : Type where
  pos    : (n : Nat) → Int
  negsuc : (n : Nat) → Int

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

pos-inj : ∀ {m n} → pos m ≡ pos n → m ≡ n
pos-inj = ap abs

negsuc-inj : ∀ {m n} → negsuc m ≡ negsuc n → m ≡ n
negsuc-inj p = suc-inj (ap abs p)

Discrete-Int : Discrete Int
Discrete-Int (pos m) (pos n) = dec-map (ap pos) pos-inj (Discrete-Nat m n)
Discrete-Int (pos m) (negsuc n) = no pos≠negsuc
Discrete-Int (negsuc m) (pos n) = no (λ p → pos≠negsuc (sym p))
Discrete-Int (negsuc m) (negsuc n) = dec-map (ap negsuc) negsuc-inj (Discrete-Nat m n)

Int-is-set : is-set Int
Int-is-set = Discrete→is-set Discrete-Int

instance
  H-Level-Int : ∀ {n} → H-Level Int (2 + n)
  H-Level-Int = basic-instance 2 Int-is-set

--------------------------------------------------------------------------------
-- Algebra

succℤ : Int → Int
succℤ (pos n) = pos (suc n)
succℤ (negsuc zero) = 0ℤ
succℤ (negsuc (suc n)) = negsuc n

predℤ : Int → Int
predℤ 0ℤ = negsuc zero
predℤ (pos (suc n)) = pos n
predℤ (negsuc n) = negsuc (suc n)

infixr 5 _+ℤ_
_+ℤ_ : Int → Int → Int
pos zero +ℤ y = y
pos (suc x) +ℤ y = succℤ (pos x +ℤ y)
negsuc zero +ℤ y = predℤ y
negsuc (suc x) +ℤ y = predℤ (negsuc x +ℤ y)

maxℤ : Int → Int → Int
maxℤ (pos x) (pos y) = pos (max x y)
maxℤ (pos x) (negsuc _) = pos x
maxℤ (negsuc _) (pos y) = pos y
maxℤ (negsuc x) (negsuc y) = negsuc (min x y)

-- Properties

succℤ-predℤ : ∀ x → x ≡ succℤ (predℤ x)
succℤ-predℤ (pos (suc _)) = refl
succℤ-predℤ (pos zero) = refl
succℤ-predℤ (negsuc _) = refl

predℤ-succℤ : ∀ x → x ≡ predℤ (succℤ x)
predℤ-succℤ (pos _) = refl
predℤ-succℤ (negsuc zero) = refl
predℤ-succℤ (negsuc (suc _)) = refl

+ℤ-idl : ∀ x → 0ℤ +ℤ x ≡ x
+ℤ-idl x = refl

+ℤ-idr : ∀ x → x +ℤ 0ℤ ≡ x
+ℤ-idr (pos zero) = refl
+ℤ-idr (pos (suc n)) = ap succℤ $ +ℤ-idr (pos n)
+ℤ-idr (negsuc zero) = refl
+ℤ-idr (negsuc (suc n)) = ap predℤ $ +ℤ-idr (negsuc n)

+ℤ-succl : ∀ x y → succℤ x +ℤ y ≡ succℤ (x +ℤ y)
+ℤ-succl (pos x) y = refl
+ℤ-succl (negsuc zero) y = succℤ-predℤ y
+ℤ-succl (negsuc (suc x)) y = succℤ-predℤ (negsuc x +ℤ y)

+ℤ-succr : ∀ x y → x +ℤ succℤ y ≡ succℤ (x +ℤ y)
+ℤ-succr (pos zero) y = refl
+ℤ-succr (pos (suc x)) y = ap succℤ $ +ℤ-succr (pos x) y
+ℤ-succr (negsuc zero) y = sym (predℤ-succℤ y) ∙ succℤ-predℤ y
+ℤ-succr (negsuc (suc x)) y =
  ap predℤ (+ℤ-succr (negsuc x) y) ∙ sym (predℤ-succℤ (negsuc x +ℤ y)) ∙ succℤ-predℤ (negsuc x +ℤ y)

+ℤ-predl : ∀ x y → predℤ x +ℤ y ≡ predℤ (x +ℤ y)
+ℤ-predl (pos zero) y = refl
+ℤ-predl (pos (suc x)) y = predℤ-succℤ (pos x +ℤ y)
+ℤ-predl (negsuc zero) y = refl
+ℤ-predl (negsuc (suc _)) y = refl

+ℤ-predr : ∀ x y → x +ℤ predℤ y ≡ predℤ (x +ℤ y)
+ℤ-predr (pos zero) y = refl
+ℤ-predr (pos (suc x)) y =
  ap succℤ (+ℤ-predr (pos x) y) ∙ sym (succℤ-predℤ (pos x +ℤ y)) ∙ predℤ-succℤ (pos x +ℤ y)
+ℤ-predr (negsuc zero) y = refl
+ℤ-predr (negsuc (suc x)) y =
  ap predℤ (+ℤ-predr (negsuc x) y)

+ℤ-associative : ∀ x y z → x +ℤ (y +ℤ z) ≡ (x +ℤ y) +ℤ z
+ℤ-associative (pos zero) y z = refl
+ℤ-associative (pos (suc x)) y z =
  succℤ (pos x +ℤ (y +ℤ z)) ≡⟨ ap succℤ (+ℤ-associative (pos x) y z) ⟩
  succℤ ((pos x +ℤ y) +ℤ z) ≡˘⟨ +ℤ-succl (pos x +ℤ y) z ⟩
  (succℤ (pos x +ℤ y) +ℤ z) ∎
+ℤ-associative (negsuc zero) y z = sym $ +ℤ-predl y z
+ℤ-associative (negsuc (suc x)) y z =
  predℤ (negsuc x +ℤ (y +ℤ z)) ≡⟨ ap predℤ (+ℤ-associative (negsuc x) y z) ⟩
  predℤ ((negsuc x +ℤ y) +ℤ z) ≡˘⟨ +ℤ-predl (negsuc x +ℤ y) z ⟩
  (predℤ (negsuc x +ℤ y) +ℤ z) ∎

+ℤ-negate : ∀ x y → - (x + y) ≡ (- x) +ℤ (- y)
+ℤ-negate zero y = refl
+ℤ-negate (suc zero) zero = refl
+ℤ-negate (suc zero) (suc y) = refl
+ℤ-negate (suc (suc x)) y = ap predℤ $ +ℤ-negate (suc x) y

+ℤ-pos : ∀ x y → pos (x + y) ≡ pos x +ℤ pos y
+ℤ-pos zero y = refl
+ℤ-pos (suc x) y = ap succℤ $ +ℤ-pos x y

negate-inj : ∀ x y → (- x) ≡ (- y) → x ≡ y
negate-inj zero zero p = refl
negate-inj zero (suc y) p = absurd (pos≠negsuc p)
negate-inj (suc x) zero p = absurd (pos≠negsuc (sym p))
negate-inj (suc x) (suc y) p = ap suc (negsuc-inj p)

succℤ-inj : ∀ x y → succℤ x ≡ succℤ y → x ≡ y
succℤ-inj (pos _) (pos _) p = ap predℤ p
succℤ-inj (pos _) (negsuc zero) p = ap predℤ p
succℤ-inj (pos _) (negsuc (suc _)) p = ap predℤ p
succℤ-inj (negsuc zero) (pos _) p = ap predℤ p
succℤ-inj (negsuc zero) (negsuc zero) p = ap predℤ p
succℤ-inj (negsuc zero) (negsuc (suc _)) p = ap predℤ p
succℤ-inj (negsuc (suc _)) (pos _) p = ap predℤ p
succℤ-inj (negsuc (suc _)) (negsuc zero) p = ap predℤ p
succℤ-inj (negsuc (suc _)) (negsuc (suc _)) p = ap predℤ p

predℤ-inj : ∀ x y → predℤ x ≡ predℤ y → x ≡ y
predℤ-inj (pos zero) (pos zero) p = ap succℤ p
predℤ-inj (pos zero) (pos (suc _)) p = ap succℤ p
predℤ-inj (pos zero) (negsuc _) p = ap succℤ p
predℤ-inj (pos (suc _)) (pos zero) p = ap succℤ p
predℤ-inj (pos (suc _)) (pos (suc _)) p = ap succℤ p
predℤ-inj (pos (suc _)) (negsuc _) p = ap succℤ p
predℤ-inj (negsuc _) (pos zero) p = ap succℤ p
predℤ-inj (negsuc _) (pos (suc _)) p = ap succℤ p
predℤ-inj (negsuc _) (negsuc _) p = ap succℤ p

+ℤ-injr : ∀ k x y → k +ℤ x ≡ k +ℤ y → x ≡ y
+ℤ-injr (pos zero) x y p = p
+ℤ-injr (pos (suc k)) x y p =
  +ℤ-injr (pos k) x y $ succℤ-inj (pos k +ℤ x) (pos k +ℤ y) p
+ℤ-injr (negsuc zero) x y p = predℤ-inj x y p
+ℤ-injr (negsuc (suc k)) x y p =
  +ℤ-injr (negsuc k) x y $ predℤ-inj (negsuc k +ℤ x) (negsuc k +ℤ y) p

--------------------------------------------------------------------------------
-- Order

_≤ℤ_ : Int → Int → Type
pos x ≤ℤ pos y = x ≤ y
pos x ≤ℤ negsuc y = ⊥
negsuc x ≤ℤ pos y = ⊤
negsuc x ≤ℤ negsuc y = y ≤ x

_<ℤ_ : Int → Int → Type
_<ℤ_ = strict _≤ℤ_

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

succℤ-invariant : ∀ x y → x ≤ℤ y → succℤ x ≤ℤ succℤ y
succℤ-invariant (pos x) (pos y) x≤y = s≤s x≤y
succℤ-invariant (pos x) (negsuc y) ()
succℤ-invariant (negsuc zero) (pos y) _ = 0≤x
succℤ-invariant (negsuc zero) (negsuc zero) _ = 0≤x
succℤ-invariant (negsuc zero) (negsuc (suc _)) ()
succℤ-invariant (negsuc (suc x)) (pos y) _ = tt
succℤ-invariant (negsuc (suc x)) (negsuc zero) _ = tt
succℤ-invariant (negsuc (suc x)) (negsuc (suc y)) (s≤s x≥y) = x≥y

predℤ-invariant : ∀ x y → x ≤ℤ y → predℤ x ≤ℤ predℤ y
predℤ-invariant (pos zero) (pos zero) _ = 0≤x
predℤ-invariant (pos zero) (pos (suc _)) _ = tt
predℤ-invariant (pos x) (negsuc y) ()
predℤ-invariant (pos (suc x)) (pos zero) ()
predℤ-invariant (pos (suc x)) (pos (suc y)) (s≤s x≥y) = x≥y
predℤ-invariant (negsuc x) (pos zero) _ = 0≤x
predℤ-invariant (negsuc x) (pos (suc y)) _ = tt
predℤ-invariant (negsuc x) (negsuc y) x≤y = s≤s x≤y

+ℤ-left-invariant : ∀ x y z → y ≤ℤ z → (x +ℤ y) ≤ℤ (x +ℤ z)
+ℤ-left-invariant (pos zero) y z y≤z = y≤z
+ℤ-left-invariant (pos (suc x)) y z y≤z =
  succℤ-invariant _ _ $ +ℤ-left-invariant (pos x) y z y≤z
+ℤ-left-invariant (negsuc zero) y z y≤z =
  predℤ-invariant _ _ y≤z
+ℤ-left-invariant (negsuc (suc x)) y z y≤z =
  predℤ-invariant _ _ $ +ℤ-left-invariant (negsuc x) y z y≤z

+ℤ-right-invariant : ∀ x y z → x ≤ℤ y → (x +ℤ z) ≤ℤ (y +ℤ z)
+ℤ-right-invariant x y (pos zero) x≤y =
  coe1→0 (λ i → +ℤ-idr x i ≤ℤ +ℤ-idr y i) x≤y
+ℤ-right-invariant x y (pos (suc z)) x≤y =
  coe1→0 (λ i → +ℤ-succr x (pos z) i ≤ℤ +ℤ-succr y (pos z) i) $
  succℤ-invariant _ _ $ +ℤ-right-invariant x y (pos z) x≤y
+ℤ-right-invariant x y (negsuc zero) x≤y =
  coe1→0 (λ i → +ℤ-predr x 0ℤ i ≤ℤ +ℤ-predr y 0ℤ i) $
  predℤ-invariant _ _ $ coe1→0 (λ i → +ℤ-idr x i ≤ℤ +ℤ-idr y i) x≤y
+ℤ-right-invariant x y (negsuc (suc z)) x≤y =
  coe1→0 (λ i → +ℤ-predr x (negsuc z) i ≤ℤ +ℤ-predr y (negsuc z) i) $
  predℤ-invariant _ _ $ +ℤ-right-invariant x y (negsuc z) x≤y

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

-------------------------------------------------------------------------------
-- Bundles

ℤ-Strict-order : Poset lzero lzero
ℤ-Strict-order = to-poset mk where
  mk : make-poset _ _
  mk .make-poset._≤_ = _≤ℤ_
  mk .make-poset.≤-refl = ≤ℤ-refl _
  mk .make-poset.≤-trans = ≤ℤ-trans _ _ _
  mk .make-poset.≤-thin = ≤ℤ-is-prop _ _
  mk .make-poset.≤-antisym = ≤ℤ-antisym _ _
