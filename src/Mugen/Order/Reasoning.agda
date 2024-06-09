open import Mugen.Prelude

module Mugen.Order.Reasoning {o r} (A : Poset o r) where

private variable
  o' r' r'' : Level

open Poset A public

abstract
  =→≤ : ∀ {x y} → x ≡ y → x ≤ y
  =→≤ x=y = subst (_ ≤_) x=y ≤-refl

  ≤+=→≤ : ∀ {x y z} → x ≤ y → y ≡ z → x ≤ z
  ≤+=→≤ x≤y y≡z = subst (_ ≤_) y≡z x≤y

  =+≤→≤ : ∀ {x y z} → x ≡ y → y ≤ z → x ≤ z
  =+≤→≤ x≡y y≤z = subst (_≤ _) (sym x≡y) y≤z

  ≤-antisym'-l : ∀ {x y z} → x ≤ y → y ≤ z → x ≡ z → x ≡ y
  ≤-antisym'-l {y = y} x≤y y≤z x=z = ≤-antisym x≤y $ subst (y ≤_) (sym x=z) y≤z

  ≤-antisym'-r : ∀ {x y z} → x ≤ y → y ≤ z → x ≡ z → y ≡ z
  ≤-antisym'-r {y = y} x≤y y≤z x=z = ≤-antisym y≤z $ subst (_≤ y) x=z x≤y

ParametrizedInequality : ∀ (x y : Ob) (K : Type r') → Type (o ⊔ r ⊔ r')
ParametrizedInequality x y K = (x ≤ y) × (x ≡ y → K)

syntax ParametrizedInequality x y K = x ≤[ K ] y

abstract
  ≤[]-is-hlevel : ∀ {x y : Ob} {K : Type r'}
    → (n : Nat) → is-hlevel K (1 + n) → is-hlevel (x ≤[ K ] y) (1 + n)
  ≤[]-is-hlevel n hb =
    ×-is-hlevel (1 + n) (is-prop→is-hlevel-suc ≤-thin) $ Π-is-hlevel (1 + n) λ _ → hb

≤[]-map : ∀ {x y} {K : Type r'} {K' : Type r''} → (K → K') → x ≤[ K ] y → x ≤[ K' ] y
≤[]-map f p = Σ-map₂ (f ⊙_) p

_<_ : Ob → Ob → Type (o ⊔ r)
x < y = x ≤[ ⊥ ] y

abstract
  ≤→≤[]-equal : ∀ {x y} → x ≤ y → x ≤[ x ≡ y ] y
  ≤→≤[]-equal x≤y = x≤y , λ p → p

  <-irrefl : ∀ {x} {K : Type r'} → x ≤[ K ] x → K
  <-irrefl x<x = x<x .snd refl

  ≤[]-trans : ∀ {x y z} {K K' : Type r'} → x ≤[ K ] y → y ≤[ K' ] z → x ≤[ K × K' ] z
  ≤[]-trans {y = y} x<y y<z .fst = ≤-trans (x<y .fst) (y<z .fst)
  ≤[]-trans {y = y} x<y y<z .snd x=z =
    x<y .snd (≤-antisym'-l (x<y .fst) (y<z .fst) x=z) ,
    y<z .snd (≤-antisym'-r (x<y .fst) (y<z .fst) x=z)

  <-trans : ∀ {x y z} {K : Type r'} → x ≤[ K ] y → y ≤[ K ] z → x ≤[ K ] z
  <-trans x<y y<z = ≤[]-map fst $ ≤[]-trans x<y y<z

  <-is-prop : ∀ {x y} → is-prop (x < y)
  <-is-prop {x} {y} = hlevel 1

  ≤[]-asym : ∀ {x y} {K K' : Type r'} → x ≤[ K ] y → y ≤[ K' ] x → K × K'
  ≤[]-asym x<y y<x = <-irrefl (≤[]-trans x<y y<x)

  <-asym : ∀ {x y} {K : Type r'} → x ≤[ K ] y → y ≤[ K ] x → K
  <-asym x<y y<x = <-irrefl (<-trans x<y y<x)

  =+<→< : ∀ {x y z} {K : Type r'} → x ≡ y → y ≤[ K ] z → x ≤[ K ] z
  =+<→< {K = K} x≡y y<z = subst (λ ϕ → ϕ ≤[ K ] _) (sym x≡y) y<z

  <+=→< : ∀ {x y z} {K : Type r'} → x ≤[ K ] y → y ≡ z → x ≤[ K ] z
  <+=→< {K = K} x<y y≡z = subst (λ ϕ → _ ≤[ K ] ϕ) y≡z x<y

  <→≱ : ∀ {x y} {K : Type r'} → x ≤[ K ] y → y ≤ x → K
  <→≱ x<y y≤x = x<y .snd $ ≤-antisym (x<y .fst) y≤x

  ≤→≯ : ∀ {x y} {K : Type r'} → x ≤ y → y ≤[ K ] x → K
  ≤→≯ x≤y y<x = y<x .snd $ ≤-antisym (y<x .fst) x≤y

  <→≠ : ∀ {x y} {K : Type r'} → x ≤[ K ] y → x ≡ y → K
  <→≠ {K = K} x<y x≡y = x<y .snd x≡y

  <→≤ : ∀ {x y} {K : Type r'} → x ≤[ K ] y → x ≤ y
  <→≤ x<y = x<y .fst

  ≤+<→< : ∀ {x y z} {K : Type r'} → x ≤ y → y ≤[ K ] z → x ≤[ K ] z
  ≤+<→< x≤y y<z .fst = ≤-trans x≤y (y<z .fst)
  ≤+<→< x≤y y<z .snd x=z = <→≱ y<z (=+≤→≤ (sym x=z) x≤y)

  <+≤→< : ∀ {x y z} {K : Type r'} → x ≤[ K ] y → y ≤ z → x ≤[ K ] z
  <+≤→< x<y y≤z .fst = ≤-trans (x<y .fst) y≤z
  <+≤→< x<y y≤z .snd x=z = <→≱ x<y (≤+=→≤ y≤z (sym x=z))

private
  data Related (K : Type r') : ⌞ A ⌟ → ⌞ A ⌟ → Type (o ⊔ r ⊔ lsuc r') where
    strict : ∀ {x y} → x ≤[ K ] y → Related K x y
    non-strict : ∀ {x y} → x ≤ y → Related K x y

  NonStrict : ∀ {x y} → Related ⊤ x y → Type
  NonStrict (strict _) = ⊥
  NonStrict (non-strict _) = ⊤

  Strict : ∀ {K : Type r'} {x y} → Related K x y → Type
  Strict (strict _) = ⊤
  Strict (non-strict _) = ⊥

begin-≤[_]_ : ∀ {x y} (K : Type r') (x<y : Related K x y) → {Strict x<y} → x ≤[ K ] y
begin-≤[ K ] (strict x<y) = x<y

begin-≤_ : ∀ {x y} (x≤y : Related ⊤ x y) → {NonStrict x≤y} → x ≤ y
begin-≤ (non-strict x≤y) = x≤y

step-< : ∀ {K : Type r'} x {y z} → x ≤[ K ] y → Related K y z → Related K x z
step-< {K = K} x x<y (non-strict y≤z) = strict (<+≤→< x<y y≤z)
step-< {K = K} x x<y (strict y<z) = strict (<-trans x<y y<z)

step-≤ : ∀ {K : Type r'} x {y z} → x ≤ y → Related K y z → Related K x z
step-≤ x x≤y (non-strict y≤z) = non-strict (≤-trans x≤y y≤z)
step-≤ x x≤y (strict y<z) = strict (≤+<→< x≤y y<z)

step-≡ : ∀ {K : Type r'} x {y z} → x ≡ y → Related K y z → Related K x z
step-≡ x x≡y (non-strict y≤z) = non-strict (=+≤→≤ x≡y y≤z)
step-≡ x x≡y (strict y<z) = strict (=+<→< x≡y y<z)

_≤∎ : ∀ {K : Type r'} x → Related K x x
_≤∎ x = non-strict ≤-refl

infix  1 begin-≤[_]_ begin-≤_
infixr 2 step-< step-≤ step-≡
infix  3 _≤∎

syntax step-< x p q = x <⟨ p ⟩ q
syntax step-≤ x p q = x ≤⟨ p ⟩ q
syntax step-≡ x p q = x ≐⟨ p ⟩ q
