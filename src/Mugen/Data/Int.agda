module Mugen.Data.Int where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Algebra.Displacement
open import Mugen.Order.StrictOrder
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

diff : Nat → Nat → Int
diff zero zero = 0ℤ
diff zero (suc n) = negsuc n
diff (suc m) zero = pos (suc m)
diff (suc m) (suc n) = diff m n

1+ℤ : Int → Int
1+ℤ (pos n) = pos (suc n)
1+ℤ (negsuc zero) = 0ℤ
1+ℤ (negsuc (suc n)) = negsuc n

_-1ℤ : Int → Int
0ℤ -1ℤ = negsuc zero
pos (suc n) -1ℤ = pos n
negsuc n -1ℤ = negsuc (suc n)

_+ℤ_ : Int → Int → Int
pos m +ℤ pos n = pos (m + n)
pos m +ℤ negsuc n = diff m (suc n)
negsuc m +ℤ pos n = diff n (suc m)
negsuc m +ℤ negsuc n = negsuc (suc (m + n))

maxℤ : Int → Int → Int
maxℤ (pos x) (pos y) = pos (max x y)
maxℤ (pos x) (negsuc _) = pos x
maxℤ (negsuc _) (pos y) = pos y
maxℤ (negsuc x) (negsuc y) = negsuc (min x y)

+ℤ-idl : ∀ x → 0ℤ +ℤ x ≡ x
+ℤ-idl (pos n) = refl
+ℤ-idl (negsuc n) = refl

+ℤ-idr : ∀ x → x +ℤ 0ℤ ≡ x
+ℤ-idr (pos x) = ap pos (+-zeror x)
+ℤ-idr (negsuc n) = refl

diff-0ℤl : ∀ x → diff 0 x ≡ 1+ℤ (negsuc x)
diff-0ℤl zero = refl
diff-0ℤl (suc x) = refl

diff-0ℤr : ∀ x → diff x 0 ≡ pos x
diff-0ℤr zero = refl
diff-0ℤr (suc x) = refl

diff-sucl : ∀ x y → diff (suc x) y ≡ 1+ℤ (diff x y)
diff-sucl zero zero = refl
diff-sucl zero (suc y) = diff-0ℤl y
diff-sucl (suc x) zero = refl
diff-sucl (suc x) (suc y) = diff-sucl x y

diff-sucr : ∀ x y → diff x (suc y) ≡ (diff x y) -1ℤ
diff-sucr zero zero = refl
diff-sucr zero (suc y) = refl
diff-sucr (suc x) zero = diff-0ℤr x
diff-sucr (suc x) (suc y) = diff-sucr x y

+ℤ-sucl : ∀ x y → pos (suc x) +ℤ y ≡ 1+ℤ (pos x +ℤ y)
+ℤ-sucl zero (pos y) = refl
+ℤ-sucl zero (negsuc y) = diff-0ℤl y
+ℤ-sucl (suc x) (pos n) = refl
+ℤ-sucl (suc x) (negsuc y) = diff-sucl x y

+ℤ-sucr : ∀ x y → x +ℤ (pos (suc y)) ≡ 1+ℤ (x +ℤ pos y)
+ℤ-sucr (pos x) y = ap pos (+-sucr x y)
+ℤ-sucr (negsuc x) zero = diff-0ℤl x
+ℤ-sucr (negsuc x) (suc y) = diff-sucl y x

+ℤ-diff-posl : ∀ x y z → pos x +ℤ (diff y z) ≡ diff (x + y) z
+ℤ-diff-posl zero y z = +ℤ-idl (diff y z)
+ℤ-diff-posl (suc x) y z =
  pos (suc x) +ℤ diff y z ≡⟨ +ℤ-sucl x (diff y z) ⟩
  1+ℤ (pos x +ℤ diff y z) ≡⟨ ap 1+ℤ (+ℤ-diff-posl x y z) ⟩
  1+ℤ (diff (x + y) z)    ≡˘⟨ diff-sucl (x + y) z ⟩
  diff (suc (x + y)) z    ∎

+ℤ-diff-posr : ∀ x y z → diff x y +ℤ pos z ≡ diff (x + z) y
+ℤ-diff-posr zero zero z = sym (diff-0ℤr z)
+ℤ-diff-posr zero (suc y) z = refl
+ℤ-diff-posr (suc x) zero z = refl
+ℤ-diff-posr (suc x) (suc y) z = +ℤ-diff-posr x y z

+ℤ-diff-negl : ∀ x y z → negsuc x +ℤ diff y z ≡ diff y (suc (x + z))
+ℤ-diff-negl x zero zero = ap negsuc (sym $ +-zeror x)
+ℤ-diff-negl x zero (suc z) = ap negsuc (sym $ +-sucr x z)
+ℤ-diff-negl x (suc y) zero = ap (diff y) (sym $ +-zeror x)
+ℤ-diff-negl x (suc y) (suc z) =
  negsuc x +ℤ diff y z ≡⟨ +ℤ-diff-negl x y z ⟩
  diff y (suc (x + z)) ≡˘⟨ ap (diff y) (+-sucr x z) ⟩
  diff y (x + suc z) ∎

+ℤ-diff-negr : ∀ x y z → diff x y +ℤ negsuc z ≡ diff x (suc (y + z))
+ℤ-diff-negr zero zero z = refl
+ℤ-diff-negr zero (suc y) z = refl
+ℤ-diff-negr (suc x) zero z = refl
+ℤ-diff-negr (suc x) (suc y) z = +ℤ-diff-negr x y z

infixr 5 _+ℤ_

+ℤ-associative : ∀ x y z → x +ℤ (y +ℤ z) ≡ (x +ℤ y) +ℤ z
+ℤ-associative (pos x) (pos y) (pos z) =
  ap pos (+-associative x y z)
+ℤ-associative (pos x) (pos y) (negsuc z) =
  +ℤ-diff-posl x y (suc z)
+ℤ-associative (pos x) (negsuc y) (pos z) =
  pos x +ℤ diff z (suc y) ≡⟨ +ℤ-diff-posl x z (suc y) ⟩
  diff (x + z) (suc y)    ≡˘⟨ +ℤ-diff-posr x (suc y) z ⟩
  diff x (suc y) +ℤ pos z ∎
+ℤ-associative (pos x) (negsuc y) (negsuc z) =
  sym (+ℤ-diff-negr x (suc y) z)
+ℤ-associative (negsuc x) (pos y) (pos z) =
  sym (+ℤ-diff-posr y (suc x) z)
+ℤ-associative (negsuc x) (pos y) (negsuc z) =
  negsuc x +ℤ diff y (suc z) ≡⟨ +ℤ-diff-negl x y (suc z) ⟩
  diff y (suc x + suc z)     ≡⟨ ap (diff y) (+-sucr (suc x) z) ⟩
  diff y (suc (suc x) + z)   ≡˘⟨ +ℤ-diff-negr y (suc x) z ⟩
  diff y (suc x) +ℤ negsuc z ∎
+ℤ-associative (negsuc x) (negsuc y) (pos z) =
  negsuc x +ℤ diff z (suc y) ≡⟨ +ℤ-diff-negl x z (suc y) ⟩
  diff z (suc x + suc y)     ≡⟨ ap (diff z) (+-sucr (suc x) y) ⟩
  diff z (suc (suc x) + y)   ∎
+ℤ-associative (negsuc x) (negsuc y) (negsuc z) =
  negsuc (suc (x + suc (y + z)))   ≡⟨ ap negsuc (+-sucr (suc x) (y + z)) ⟩
  negsuc (suc (suc (x + (y + z)))) ≡⟨ ap negsuc (+-associative (suc (suc x)) y z) ⟩
  negsuc (suc (suc (x + y + z)))   ∎

+ℤ-negate : ∀ x y → - (x + y) ≡ (- x) +ℤ (- y)
+ℤ-negate zero zero = refl
+ℤ-negate zero (suc y) = refl
+ℤ-negate (suc x) zero = ap negsuc (+-zeror x)
+ℤ-negate (suc x) (suc y) = ap negsuc (+-sucr  x y)

negate-inj : ∀ x y → (- x) ≡ (- y) → x ≡ y
negate-inj zero zero p = refl
negate-inj zero (suc y) p = absurd (pos≠negsuc p)
negate-inj (suc x) zero p = absurd (pos≠negsuc (sym p))
negate-inj (suc x) (suc y) p = ap suc (negsuc-inj p)

--------------------------------------------------------------------------------
-- Order

_<ℤ_ : Int → Int → Type
pos x <ℤ pos y = x < y
pos x <ℤ negsuc y = ⊥
negsuc x <ℤ pos y = ⊤
negsuc x <ℤ negsuc y = y < x

_≤ℤ_ : Int → Int → Type
pos x ≤ℤ pos y = x ≤ y
pos x ≤ℤ negsuc y = ⊥
negsuc x ≤ℤ pos y = ⊤
negsuc x ≤ℤ negsuc y = y ≤ x


<ℤ-irrefl : ∀ x → x <ℤ x → ⊥
<ℤ-irrefl (pos x) = <-irrefl refl
<ℤ-irrefl (negsuc x) = <-irrefl refl

<ℤ-trans : ∀ x y z → x <ℤ y → y <ℤ z → x <ℤ z
<ℤ-trans (pos x) (pos y) (pos z) x<y y<z = <-trans x y z x<y y<z
<ℤ-trans (negsuc x) (pos y) (pos z) x<y y<z = tt
<ℤ-trans (negsuc x) (negsuc y) (pos z) x<y y<z = tt
<ℤ-trans (negsuc x) (negsuc y) (negsuc z) x<y y<z = <-trans z y x y<z x<y

≤ℤ-refl : ∀ x → x ≤ℤ x
≤ℤ-refl (pos x) = ≤-refl
≤ℤ-refl (negsuc x) = ≤-refl

≤ℤ-trans : ∀ x y z → x ≤ℤ y → y ≤ℤ z → x ≤ℤ z
≤ℤ-trans (pos x) (pos y) (pos z) x≤y y≤z = ≤-trans x≤y y≤z
≤ℤ-trans (negsuc x) (pos y) (pos z) x≤y y≤z = tt
≤ℤ-trans (negsuc x) (negsuc y) (pos z) x≤y y≤z = tt
≤ℤ-trans (negsuc x) (negsuc y) (negsuc z) x≤y y≤z = ≤-trans y≤z x≤y

<ℤ-weaken : ∀ x y → x <ℤ y → x ≤ℤ y
<ℤ-weaken (pos x) (pos y) x<y = <-weaken x y x<y
<ℤ-weaken (negsuc x) (pos y) x<y = tt
<ℤ-weaken (negsuc x) (negsuc y) x<y = <-weaken y x x<y

≤ℤ-strengthen : ∀ x y → x ≤ℤ y → x ≡ y ⊎ x <ℤ y
≤ℤ-strengthen (pos x) (pos y) x≤y =
  ⊎-map (ap pos) (λ x<y → x<y) (≤-strengthen x y x≤y)
≤ℤ-strengthen (negsuc x) (pos y) x≤y =
  inr tt
≤ℤ-strengthen (negsuc x) (negsuc y) x≤y =
  ⊎-map (λ p → ap negsuc (sym p)) (λ y<x → y<x) (≤-strengthen y x x≤y)

to-≤ℤ : ∀ x y → x ≡ y ⊎ x <ℤ y → x ≤ℤ y
to-≤ℤ x y (inl x≡y) = subst (x ≤ℤ_) x≡y (≤ℤ-refl x)
to-≤ℤ x y (inr x<y) = <ℤ-weaken x y x<y

<ℤ-≤ℤ-trans : ∀ x y z → x <ℤ y → y ≤ℤ z → x <ℤ z
<ℤ-≤ℤ-trans (pos x) (pos y) (pos z) x<y y≤z = ≤-trans x<y y≤z
<ℤ-≤ℤ-trans (negsuc x) (pos y) (pos z) x<y y≤z = tt
<ℤ-≤ℤ-trans (negsuc x) (negsuc y) (pos z) x<y y≤z = tt
<ℤ-≤ℤ-trans (negsuc x) (negsuc y) (negsuc z) x<y y≤z = ≤-trans (s≤s y≤z) x<y

≤ℤ-<ℤ-trans : ∀ x y z → x ≤ℤ y → y <ℤ z → x <ℤ z
≤ℤ-<ℤ-trans (pos x) (pos y) (pos z) x≤y y<z = ≤-trans (s≤s x≤y) y<z
≤ℤ-<ℤ-trans (negsuc x) (pos y) (pos z) x≤y y<z = tt
≤ℤ-<ℤ-trans (negsuc x) (negsuc y) (pos z) x≤y y<z = tt
≤ℤ-<ℤ-trans (negsuc x) (negsuc y) (negsuc z) x≤y y<z = ≤-trans y<z x≤y

<ℤ-is-prop : ∀ x y → is-prop (x <ℤ y)
<ℤ-is-prop (pos x) (pos y) = ≤-is-prop
<ℤ-is-prop (pos x) (negsuc y) = hlevel 1
<ℤ-is-prop (negsuc x) (pos y) = hlevel 1
<ℤ-is-prop (negsuc x) (negsuc y) = ≤-is-prop

module Int-<Reasoning where
  infix  1 begin-<_
  infixr 2 step-< step-≤ step-≡
  infix  3 _<∎

  -- Used to block evaluation of _<ℤ_
  data _IsRelatedTo_ : Int → Int → Type where
    done : ∀ x → x IsRelatedTo x
    strong : ∀ x y → x <ℤ y → x IsRelatedTo y
    weak : ∀ x y → x ≤ℤ y → x IsRelatedTo y

  Strong : ∀ {x y} → x IsRelatedTo y → Type
  Strong (done _) = ⊥
  Strong (strong _ _ _) = ⊤
  Strong (weak _ _ _) = ⊥

  begin-<_ : ∀ {x y} → (x<y : x IsRelatedTo y) → {Strong x<y} → x <ℤ y
  begin-< (strong _ _ x<y) = x<y

  begin-≤_ : ∀ {x y} → (x≤y : x IsRelatedTo y) → x ≤ℤ y
  begin-≤ done x = ≤ℤ-refl x
  begin-≤ strong x y x<y = <ℤ-weaken x y x<y
  begin-≤ weak x y x≤y = x≤y

  step-< : ∀ x {y z} → y IsRelatedTo z → x <ℤ y → x IsRelatedTo z
  step-< x (done y) x<y = strong x y x<y
  step-< x (strong y z y<z) x<y = strong x z (<ℤ-trans x y z x<y y<z)
  step-< x (weak y z y≤z) x<y = strong x z (<ℤ-≤ℤ-trans x y z x<y y≤z)

  step-≤ : ∀ x {y z} → y IsRelatedTo z → x ≤ℤ y → x IsRelatedTo z
  step-≤ x (done y) x≤y = weak x y x≤y
  step-≤ x (strong y z y<z) x≤y = strong x z (≤ℤ-<ℤ-trans x y z x≤y y<z)
  step-≤ x (weak y z y≤z) x≤y = weak x z (≤ℤ-trans x y z x≤y y≤z)

  step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
  step-≡ x (done y) p = subst (x IsRelatedTo_) p (done x)
  step-≡ x (strong y z y<z) p = strong x z (subst (_<ℤ z) (sym p) y<z)
  step-≡ x (weak y z y≤z) p = weak x z (subst (_≤ℤ z) (sym p) y≤z)

  _<∎ : ∀ x → x IsRelatedTo x
  _<∎ x = done x

  syntax step-< x q p = x <⟨ p ⟩ q
  syntax step-≤ x q p = x ≤⟨ p ⟩ q
  syntax step-≡ x q p = x ≡̇⟨ p ⟩ q

open Int-<Reasoning

1+ℤ-< : ∀ x → x <ℤ 1+ℤ x
1+ℤ-< (pos x) = <-suc x
1+ℤ-< (negsuc zero) = tt
1+ℤ-< (negsuc (suc x)) = <-suc x

-1ℤ-< : ∀ x → (x -1ℤ) <ℤ x
-1ℤ-< (pos (suc x)) = <-suc x
-1ℤ-< 0ℤ = tt
-1ℤ-< (negsuc x) = <-suc x

diff-suc-< : ∀ x y → diff x (suc y) <ℤ pos x
diff-suc-< zero y = tt
diff-suc-< (suc x) zero = begin-<
  diff x 0    ≡̇⟨ diff-0ℤr x ⟩
  pos x       <⟨ <-suc x ⟩
  pos (suc x) <∎
diff-suc-< (suc x) (suc y) = begin-<
  diff x (suc y) <⟨ diff-suc-< x y ⟩
  pos x          <⟨ <-suc x ⟩
  pos (suc x)    <∎

diff-negsuc-< : ∀ x y → negsuc y <ℤ diff x y
diff-negsuc-< zero zero = tt
diff-negsuc-< zero (suc y) = <-suc y
diff-negsuc-< (suc x) zero = tt
diff-negsuc-< (suc x) (suc y) = begin-<
  negsuc (suc y) <⟨ -1ℤ-< (negsuc y) ⟩ 
  negsuc y       <⟨ diff-negsuc-< x y ⟩ 
  diff x y       <∎

diff-left-invariant : ∀ x y z → z < y → diff x y <ℤ diff x z
diff-left-invariant zero (suc y) zero z<y = tt
diff-left-invariant zero (suc y) (suc z) (s≤s z<y) = z<y
diff-left-invariant (suc x) (suc y) zero z<y = diff-suc-< (suc x) y
diff-left-invariant (suc x) (suc y) (suc z) (s≤s z<y) = diff-left-invariant x y z z<y

diff-right-invariant : ∀ x y z → x < y → diff x z <ℤ diff y z
diff-right-invariant zero (suc y) zero x<y = x<y
diff-right-invariant zero (suc y) (suc z) x<y = diff-negsuc-< y z
diff-right-invariant (suc x) (suc y) zero x<y = x<y
diff-right-invariant (suc x) (suc y) (suc z) (s≤s x<y) = diff-right-invariant x y z x<y

diff-weak-left-invariant : ∀ x y z → z ≤ y → diff x y ≤ℤ diff x z
diff-weak-left-invariant x y z z≤y with ≤-strengthen z y z≤y
... | inl z≡y = subst (_≤ℤ diff x z) (ap (diff x) z≡y) (≤ℤ-refl (diff x z))
... | inr z<y = <ℤ-weaken (diff x y) (diff x z) $ diff-left-invariant x y z z<y

+ℤ-left-invariant : ∀ x y z → y <ℤ z → (x +ℤ y) <ℤ (x +ℤ z)
+ℤ-left-invariant (pos x) (pos y) (pos z) y<z = +-<-left-invariant x y z y<z
+ℤ-left-invariant (pos x) (negsuc y) (pos z) y<z = begin-<
  diff x (suc y) <⟨ diff-suc-< x y ⟩
  pos x          ≤⟨ +-≤l x z ⟩
  pos (x + z)    <∎
+ℤ-left-invariant (pos x) (negsuc y) (negsuc z) y<z =
  diff-left-invariant x (suc y) (suc z) (s≤s y<z)
+ℤ-left-invariant (negsuc x) (pos y) (pos z) y<z =
  diff-right-invariant y z (suc x) y<z
+ℤ-left-invariant (negsuc x) (negsuc y) (pos z) y<z = begin-<
  negsuc (suc (x + y)) <⟨ diff-negsuc-< z (suc (x + y))  ⟩
  diff z (suc (x + y)) ≤⟨ diff-weak-left-invariant z (suc (x + y)) (suc x) (+-≤l (suc x) y) ⟩
  diff z (suc x) <∎
+ℤ-left-invariant (negsuc x) (negsuc y) (negsuc z) y<z =
  s≤s (+-<-left-invariant x z y y<z)

+ℤ-right-invariant : ∀ x y z → x <ℤ y → (x +ℤ z) <ℤ (y +ℤ z)
+ℤ-right-invariant (pos x) (pos y) (pos z) x<y =
  +-<-right-invariant x y z x<y
+ℤ-right-invariant (pos x) (pos y) (negsuc z) x<y =
  diff-right-invariant x y (suc z) x<y
+ℤ-right-invariant (negsuc x) (pos y) (pos z) x<y = begin-<
  diff z (suc x) <⟨ diff-suc-< z x ⟩
  pos z          ≤⟨ +-≤r y z ⟩
  pos (y + z)    <∎
+ℤ-right-invariant (negsuc x) (pos y) (negsuc z) x<y = begin-<
  negsuc (suc (x + z)) ≡̇⟨ ap negsuc (sym (+-sucr x z)) ⟩
  negsuc (x + suc z)   ≤⟨ +-≤r x (suc z) ⟩
  negsuc (suc z)       <⟨ diff-negsuc-< y (suc z) ⟩
  diff y (suc z)       <∎
+ℤ-right-invariant (negsuc x) (negsuc y) (pos z) x<y =
  diff-left-invariant z (suc x) (suc y) (s≤s x<y)
+ℤ-right-invariant (negsuc x) (negsuc y) (negsuc z) x<y =
  s≤s (+-<-right-invariant y x z x<y)

+ℤ-weak-right-invariant : ∀ x y z → non-strict _<ℤ_ x y → non-strict _<ℤ_ (x +ℤ z) (y +ℤ z)
+ℤ-weak-right-invariant x y z (inl x≡y) = inl (ap (_+ℤ z) x≡y)
+ℤ-weak-right-invariant x y z (inr x<y) = inr (+ℤ-right-invariant x y z x<y)

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

negate-anti-mono : ∀ x y → x < y → (- y) <ℤ (- x)
negate-anti-mono zero (suc y) x<y = tt
negate-anti-mono (suc x) (suc y) (s≤s x<y) = x<y

--------------------------------------------------------------------------------
-- Bundles

ℤ-Strict-order : Strict-order lzero lzero
ℤ-Strict-order = to-strict-order mk where
  mk : make-strict-order _ _ 
  mk .make-strict-order._<_ = _<ℤ_
  mk .make-strict-order.<-irrefl = <ℤ-irrefl _
  mk .make-strict-order.<-trans = <ℤ-trans _ _ _
  mk .make-strict-order.<-thin = <ℤ-is-prop _ _
  mk .make-strict-order.has-is-set = hlevel 2

ℤ-Displacement : Displacement-algebra lzero lzero
ℤ-Displacement = to-displacement-algebra mk where
  mk : make-displacement-algebra ℤ-Strict-order
  mk .make-displacement-algebra.ε = pos 0
  mk .make-displacement-algebra._⊗_ = _+ℤ_
  mk .make-displacement-algebra.idl = +ℤ-idl _
  mk .make-displacement-algebra.idr = +ℤ-idr _
  mk .make-displacement-algebra.associative {x} {y} {z} = +ℤ-associative x y z
  mk .make-displacement-algebra.left-invariant {x} {y} {z} = +ℤ-left-invariant x y z

ℤ-has-ordered-monoid : has-ordered-monoid ℤ-Displacement
ℤ-has-ordered-monoid =
  right-invariant→has-ordered-monoid ℤ-Displacement
    (+ℤ-weak-right-invariant _ _ _)
