module Mugen.Data.Int where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
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

+ℤ-associative : ∀ x y z → (x +ℤ y) +ℤ z ≡ x +ℤ (y +ℤ z)
+ℤ-associative (pos x) (pos y) (pos z) =
  ap pos (+-associative x y z)
+ℤ-associative (pos x) (pos y) (negsuc z) =
  sym (+ℤ-diff-posl x y (suc z))
+ℤ-associative (pos x) (negsuc y) (pos z) =
  diff x (suc y) +ℤ pos z ≡⟨ +ℤ-diff-posr x (suc y) z ⟩
  diff (x + z) (suc y)    ≡˘⟨ +ℤ-diff-posl x z (suc y) ⟩
  pos x +ℤ diff z (suc y) ∎
+ℤ-associative (pos x) (negsuc y) (negsuc z) =
  +ℤ-diff-negr x (suc y) z
+ℤ-associative (negsuc x) (pos y) (pos z) =
  +ℤ-diff-posr y (suc x) z
+ℤ-associative (negsuc x) (pos y) (negsuc z) =
  diff y (suc x) +ℤ negsuc z ≡⟨ +ℤ-diff-negr y (suc x) z ⟩
  diff y (suc (suc x + z)) ≡˘⟨ ap (diff y) (+-sucr (suc x) z) ⟩
  diff y (suc x + suc z) ≡˘⟨ +ℤ-diff-negl x y (suc z) ⟩
  negsuc x +ℤ diff y (suc z) ∎
+ℤ-associative (negsuc x) (negsuc y) (pos z) =
  diff z (suc (suc x) + y)   ≡˘⟨ ap (diff z) (+-sucr (suc x) y) ⟩
  diff z (suc x + suc y)     ≡⟨ sym (+ℤ-diff-negl x z (suc y)) ⟩
  negsuc x +ℤ diff z (suc y) ∎
+ℤ-associative (negsuc x) (negsuc y) (negsuc z) =
  negsuc (suc (suc x) + y + z) ≡⟨ ap negsuc (+-associative (suc (suc x)) y z) ⟩
  negsuc (suc (suc x) + (y + z)) ≡˘⟨ ap negsuc (+-sucr (suc x) (y + z)) ⟩
  negsuc (suc x + suc (y + z)) ∎


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

+ℤ-is-magma : is-magma _+ℤ_
+ℤ-is-magma .has-is-set = hlevel 2

+ℤ-is-semigroup : is-semigroup _+ℤ_
+ℤ-is-semigroup .has-is-magma = +ℤ-is-magma
+ℤ-is-semigroup .associative {x} {y} {z} = sym $ +ℤ-associative x y z

+ℤ-0ℤ-is-monoid : is-monoid 0ℤ _+ℤ_
+ℤ-0ℤ-is-monoid .has-is-semigroup = +ℤ-is-semigroup
+ℤ-0ℤ-is-monoid .idl {x} = +ℤ-idl x
+ℤ-0ℤ-is-monoid .idr {y} =  +ℤ-idr y


--------------------------------------------------------------------------------
-- Order

data _≤ℤ_ : Int → Int → Type where
  +≤+ : ∀ {x y} → x ≤ y → pos x ≤ℤ pos y
  -≤- : ∀ {x y} → y ≤ x → negsuc x ≤ℤ negsuc y
  instance
    -≤+ : ∀ {x y} → negsuc x ≤ℤ pos y

data _<ℤ_ : Int → Int → Type where
  +<+ : ∀ {x y} → x < y → pos x <ℤ pos y
  -<- : ∀ {x y} → y < x → negsuc x <ℤ negsuc y
  instance
    -<+ : ∀ {x y} → negsuc x <ℤ pos y

instance
  +≤+′ : ∀ {x y} → ⦃ x ≤ y ⦄ → pos x ≤ℤ pos y
  +≤+′ ⦃ x≤y ⦄ = +≤+ x≤y

  -≤-′ : ∀ {x y} → ⦃ y ≤ x ⦄ → negsuc x ≤ℤ negsuc y
  -≤-′ ⦃ y≤x ⦄ = -≤- y≤x

  +<+′ : ∀ {x y} → ⦃ x < y ⦄ → pos x <ℤ pos y
  +<+′ ⦃ x≤y ⦄ = +<+ x≤y

  -<-′ : ∀ {x y} → ⦃ y < x ⦄ → negsuc x <ℤ negsuc y
  -<-′ ⦃ y≤x ⦄ = -<- y≤x


<ℤ-irrefl : ∀ {x} → x <ℤ x → ⊥
<ℤ-irrefl (+<+ x<x) = <-irrefl x<x
<ℤ-irrefl (-<- x<x) = <-irrefl x<x

<ℤ-trans : ∀ {x y z} → x <ℤ y → y <ℤ z → x <ℤ z
<ℤ-trans (+<+ x<y) (+<+ y<z) = +<+ (<-trans x<y y<z)
<ℤ-trans (-<- y<x) (-<- z<y) = -<- (<-trans z<y y<x)
<ℤ-trans (-<- x<y) -<+ = -<+
<ℤ-trans -<+ (+<+ y<z) = -<+

≤ℤ-refl : ∀ {x} → x ≤ℤ x
≤ℤ-refl {x = pos n} = +≤+ ≤-refl
≤ℤ-refl {x = negsuc n} = -≤- ≤-refl

≤ℤ-trans : ∀ {x y z} → x ≤ℤ y → y ≤ℤ z → x ≤ℤ z
≤ℤ-trans (+≤+ x≤y) (+≤+ y≤z) = +≤+ (≤-trans x≤y y≤z)
≤ℤ-trans (-≤- y≤x) (-≤- z≤y) = -≤- (≤-trans z≤y y≤x)
≤ℤ-trans (-≤- x≤y) -≤+ = -≤+
≤ℤ-trans -≤+ (+≤+ y≤z) = -≤+

<ℤ-weaken : ∀ {x y} → x <ℤ y → x ≤ℤ y
<ℤ-weaken (+<+ x<y) = +≤+ (<-weaken x<y)
<ℤ-weaken (-<- y<x) = -≤- (<-weaken y<x)
<ℤ-weaken -<+ = -≤+

≤ℤ-strengthen : ∀ {x y} → x ≤ℤ y → x ≡ y ⊎ x <ℤ y
≤ℤ-strengthen (+≤+ x≤y) = ⊎-map (ap pos) +<+ (≤-strengthen x≤y)
≤ℤ-strengthen (-≤- y≤x) = ⊎-map (λ y≡x → ap negsuc (sym y≡x)) -<- (≤-strengthen y≤x)
≤ℤ-strengthen -≤+ = inr -<+

to-≤ℤ : ∀ {x y} → x ≡ y ⊎ x <ℤ y → x ≤ℤ y
to-≤ℤ (inl x≡y) = subst (_ ≤ℤ_) x≡y ≤ℤ-refl
to-≤ℤ (inr x<y) = <ℤ-weaken x<y

<ℤ-≤ℤ-trans : ∀ {x y z} → x <ℤ y → y ≤ℤ z → x <ℤ z
<ℤ-≤ℤ-trans (+<+ x<y) (+≤+ y≤z) = +<+ (≤-trans x<y y≤z)
<ℤ-≤ℤ-trans (-<- y<x) (-≤- z≤y) = -<- (≤-trans (s≤s z≤y) y<x)
<ℤ-≤ℤ-trans (-<- y<x) -≤+ = -<+
<ℤ-≤ℤ-trans -<+ (+≤+ y≤z) = -<+

≤ℤ-<ℤ-trans : ∀ {x y z} → x ≤ℤ y → y <ℤ z → x <ℤ z
≤ℤ-<ℤ-trans (+≤+ x≤y) (+<+ y<z) = +<+ (≤-trans (s≤s x≤y) y<z)
≤ℤ-<ℤ-trans (-≤- y≤x) (-<- z<y) = -<- (≤-trans z<y y≤x)
≤ℤ-<ℤ-trans (-≤- y≤x) -<+ = -<+
≤ℤ-<ℤ-trans -≤+ (+<+ y<z) = -<+

<ℤ-is-prop : ∀ {x y} → is-prop (x <ℤ y)
<ℤ-is-prop (+<+ p) (+<+ q) = ap +<+ (≤-prop p q)
<ℤ-is-prop (-<- p) (-<- q) = ap -<- (≤-prop p q)
<ℤ-is-prop -<+ -<+ = refl

<ℤ-is-strict-order : is-strict-order _<ℤ_
<ℤ-is-strict-order .is-strict-order.irrefl = <ℤ-irrefl
<ℤ-is-strict-order .is-strict-order.trans = <ℤ-trans
<ℤ-is-strict-order .is-strict-order.has-prop = <ℤ-is-prop

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
  begin-≤ done x = ≤ℤ-refl
  begin-≤ strong x y x<y = <ℤ-weaken  x<y
  begin-≤ weak x y x≤y = x≤y

  step-< : ∀ x {y z} → y IsRelatedTo z → x <ℤ y → x IsRelatedTo z
  step-< x (done y) x<y = strong x y x<y
  step-< x (strong y z y<z) x<y = strong x z (<ℤ-trans x<y y<z)
  step-< x (weak y z y≤z) x<y = strong x z (<ℤ-≤ℤ-trans x<y y≤z)

  step-≤ : ∀ x {y z} → y IsRelatedTo z → x ≤ℤ y → x IsRelatedTo z
  step-≤ x (done y) x≤y = weak x y x≤y
  step-≤ x (strong y z y<z) x≤y = strong x z (≤ℤ-<ℤ-trans x≤y y<z)
  step-≤ x (weak y z y≤z) x≤y = weak x z (≤ℤ-trans x≤y y≤z)

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

1+ℤ-< : ∀ {x} → x <ℤ 1+ℤ x
1+ℤ-< {pos x} = +<+ <-ascend
1+ℤ-< {negsuc zero} = -<+
1+ℤ-< {negsuc (suc x)} = -<- <-ascend

-1ℤ-< : ∀ {x} → (x -1ℤ) <ℤ x
-1ℤ-< {pos (suc x)} = +<+ <-ascend
-1ℤ-< {0ℤ} = -<+
-1ℤ-< {negsuc x} = -<- <-ascend

diff-suc-< : ∀ x y → diff x (suc y) <ℤ pos x
diff-suc-< zero y = -<+
diff-suc-< (suc x) zero = begin-<
  diff x 0    ≡̇⟨ diff-0ℤr x ⟩
  pos x       <⟨ +<+ <-ascend ⟩
  pos (suc x) <∎
diff-suc-< (suc x) (suc y) = begin-<
  diff x (suc y) <⟨ diff-suc-< x y ⟩
  pos x          <⟨ +<+ <-ascend ⟩
  pos (suc x)    <∎

diff-negsuc-< : ∀ x y → negsuc y <ℤ diff x y
diff-negsuc-< zero zero = -<+
diff-negsuc-< zero (suc y) = -<- <-ascend
diff-negsuc-< (suc x) zero = -<+
diff-negsuc-< (suc x) (suc y) = begin-<
  negsuc (suc y) <⟨ -1ℤ-< ⟩ 
  negsuc y       <⟨ diff-negsuc-< x y ⟩ 
  diff x y       <∎

diff-left-invariant : ∀ {y z} x → z < y → diff x y <ℤ diff x z
diff-left-invariant zero (s≤s 0≤x) = -<+
diff-left-invariant zero (s≤s (s≤s z<y)) = -<- (s≤s z<y)
diff-left-invariant (suc x) (s≤s 0≤x) = diff-suc-< _ _
diff-left-invariant (suc x) (s≤s (s≤s z<y)) = diff-left-invariant x (s≤s z<y)

diff-right-invariant : ∀ {x y} z → x < y → diff x z <ℤ diff y z
diff-right-invariant zero (s≤s 0≤x) = +<+′
diff-right-invariant zero (s≤s (s≤s x<y)) = +<+ (s≤s (s≤s x<y))
diff-right-invariant {y = suc y} (suc z) (s≤s 0≤x) = diff-negsuc-< y z
diff-right-invariant (suc z) (s≤s (s≤s x<y)) = diff-right-invariant z (s≤s x<y)

diff-weak-left-invariant : ∀ {y z} x → z ≤ y → diff x y ≤ℤ diff x z
diff-weak-left-invariant x z≤y with ≤-strengthen z≤y
... | inl z≡y = subst (_≤ℤ diff x _) (ap (diff x) z≡y) (≤ℤ-refl)
... | inr z<y = <ℤ-weaken $ diff-left-invariant x z<y

+ℤ-left-invariant : ∀ {y z} x → y <ℤ z → (x +ℤ y) <ℤ (x +ℤ z)
+ℤ-left-invariant (pos x) (+<+ y<z) = +<+ (+-<-left-invariant x y<z)
+ℤ-left-invariant (negsuc x) (+<+ y<z) = diff-right-invariant (suc x) y<z
+ℤ-left-invariant (pos x) (-<- z<y) = diff-left-invariant x (s≤s z<y)
+ℤ-left-invariant (negsuc x) (-<- z<y) = -<- (+-<-left-invariant (suc x) z<y)
+ℤ-left-invariant {y = negsuc y} {z = pos z} (pos x) -<+ = begin-<
  diff x (suc y) <⟨ diff-suc-< x y ⟩
  pos x          ≤⟨ +≤+ (+-≤l x z) ⟩
  pos (x + z)    <∎
+ℤ-left-invariant {y = negsuc y} {z = pos z} (negsuc x) -<+ = begin-<
  negsuc (suc (x + y)) <⟨ diff-negsuc-< z (suc (x + y)) ⟩
  diff z (suc (x + y)) ≤⟨ diff-weak-left-invariant z (+-≤l (suc x) y) ⟩
  diff z (suc x) <∎

+ℤ-right-invariant : ∀ {x y} z → x <ℤ y → (x +ℤ z) <ℤ (y +ℤ z)
+ℤ-right-invariant (pos z) (+<+ x<y) = +<+ (+-<-right-invariant z x<y)
+ℤ-right-invariant (negsuc z) (+<+ x<y) = diff-right-invariant (suc z) x<y
+ℤ-right-invariant (pos z) (-<- x<y) = diff-left-invariant z (s≤s x<y)
+ℤ-right-invariant (negsuc z) (-<- x<y) = -<- (+-<-right-invariant z (s≤s x<y))
+ℤ-right-invariant {x = negsuc x} {y = pos y} (pos z) -<+ = begin-<
  diff z (suc x) <⟨ diff-suc-< z x ⟩
  pos z          ≤⟨ +≤+ (+-≤r y z) ⟩
  pos (y + z)    <∎
+ℤ-right-invariant {x = negsuc x} {y = pos y} (negsuc z) -<+ = begin-<
  negsuc (suc (x + z)) ≡̇⟨ ap negsuc (sym (+-sucr x z)) ⟩
  negsuc (x + suc z)   ≤⟨ -≤- (+-≤r x (suc z)) ⟩
  negsuc (suc z)       <⟨ diff-negsuc-< y (suc z) ⟩
  diff y (suc z)       <∎

+ℤ-weak-right-invariant : ∀ {x y} z → non-strict _<ℤ_ x y → non-strict _<ℤ_ (x +ℤ z) (y +ℤ z)
+ℤ-weak-right-invariant z (inl x≡y) = inl (ap (_+ℤ z) x≡y)
+ℤ-weak-right-invariant z (inr x<y) = inr (+ℤ-right-invariant z x<y)

maxℤ-≤l : ∀ x y → x ≤ℤ maxℤ x y
maxℤ-≤l (pos x) (pos y) = +≤+ (max-≤l x y)
maxℤ-≤l (pos x) (negsuc y) = ≤ℤ-refl
maxℤ-≤l (negsuc x) (pos y) = -≤+
maxℤ-≤l (negsuc x) (negsuc y) = -≤- (min-≤l x y)

maxℤ-≤r : ∀ x y → y ≤ℤ maxℤ x y
maxℤ-≤r (pos x) (pos y) = +≤+ (max-≤r x y)
maxℤ-≤r (pos x) (negsuc y) = -≤+
maxℤ-≤r (negsuc x) (pos y) = ≤ℤ-refl
maxℤ-≤r (negsuc x) (negsuc y) = -≤- (min-≤r x y)

maxℤ-is-lub : ∀ {x y z} → x ≤ℤ z → y ≤ℤ z → maxℤ x y ≤ℤ z
maxℤ-is-lub (+≤+ x≤z) (+≤+ y≤z) = +≤+ (max-is-lub x≤z y≤z)
maxℤ-is-lub (+≤+ x≤z) -≤+ = +≤+ x≤z
maxℤ-is-lub (-≤- z≤x) (-≤- z≤y) = -≤- (min-is-glb z≤x z≤y)
maxℤ-is-lub -≤+ (+≤+ y≤z) = +≤+ y≤z
maxℤ-is-lub -≤+ -≤+ = -≤+

negate-anti-mono : ∀ {x y} → x < y → (- y) <ℤ (- x)
negate-anti-mono (s≤s 0≤x) = -<+
negate-anti-mono (s≤s (s≤s x<y)) = -<- (s≤s x<y)
