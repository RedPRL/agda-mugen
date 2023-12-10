open import Mugen.Prelude

module Mugen.Order.Reasoning {o r} (A : Poset o r) where

  private variable
    o' o'' r' r'' : Level

  open Poset A public

  instance
    H-Level-Ob : ∀ {n} → H-Level Ob (2 + n)
    H-Level-Ob {n = n} = basic-instance 2 Ob-is-set

    H-Level-≤ : ∀ {x y} {n} → H-Level (x ≤ y) (1 + n)
    H-Level-≤ {n = n} = prop-instance ≤-thin

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

  LeqAndIfEqual : ∀ {r'} (x y : Ob) (B : Type r') → Type (o ⊔ r ⊔ r')
  LeqAndIfEqual x y B = (x ≤ y) × (x ≡ y → B)

  syntax LeqAndIfEqual x y B = x ≤[ B ] y

  abstract
    ≤[]-is-hlevel : ∀ {x y : Ob} {B : Type r'}
      → (n : Nat) → is-hlevel B (1 + n) → is-hlevel (x ≤[ B ] y) (1 + n)
    ≤[]-is-hlevel n hb =
      ×-is-hlevel (1 + n) (is-prop→is-hlevel-suc ≤-thin) $ Π-is-hlevel (1 + n) λ _ → hb

  instance
    H-Level-≤[] : ∀ {r'} {B : Type r'} {n k : Nat} {x y}
      → ⦃ H-Level B (1 + n) ⦄ → H-Level (x ≤[ B ] y) (1 + n + k)
    H-Level-≤[] {n = n} ⦃ hb ⦄ =
      basic-instance (1 + n) $ ≤[]-is-hlevel n (hb .H-Level.has-hlevel)

  _<_ : Ob → Ob → Type (o ⊔ r)
  x < y = x ≤[ ⊥ ] y

  abstract
    <-irrefl : ∀ {x} {B : Type r'} → x ≤[ B ] x → B
    <-irrefl x<x = x<x .snd refl

    <-trans' : ∀ {x y z} {B B' : Type r'} → x ≤[ B ] y → y ≤[ B' ] z → x ≤[ B × B' ] z
    <-trans' {y = y} x<y y<z .fst = ≤-trans (x<y .fst) (y<z .fst)
    <-trans' {y = y} x<y y<z .snd x=z =
      x<y .snd (≤-antisym'-l (x<y .fst) (y<z .fst) x=z) ,
      y<z .snd (≤-antisym'-r (x<y .fst) (y<z .fst) x=z)

    <-trans : ∀ {x y z} {B : Type r'} → x ≤[ B ] y → y ≤[ B ] z → x ≤[ B ] z
    <-trans x<y y<z = Σ-map₂ (λ p → fst ⊙ p) $ <-trans' x<y y<z

    <-is-prop : ∀ {x y} → is-prop (x < y)
    <-is-prop {x} {y} = hlevel!

    <-asym : ∀ {x y} {B : Type r'} → x ≤[ B ] y → y ≤[ B ] x → B
    <-asym x<y y<x = <-irrefl (<-trans x<y y<x)

    =+<→< : ∀ {x y z} {B : Type r'} → x ≡ y → y ≤[ B ] z → x ≤[ B ] z
    =+<→< {B = B} x≡y y<z = subst (λ ϕ → ϕ ≤[ B ] _) (sym x≡y) y<z

    <+=→< : ∀ {x y z} {B : Type r'} → x ≤[ B ] y → y ≡ z → x ≤[ B ] z
    <+=→< {B = B} x<y y≡z = subst (λ ϕ → _ ≤[ B ] ϕ) y≡z x<y

    <→≱ : ∀ {x y} {B : Type r'} → x ≤[ B ] y → y ≤ x → B
    <→≱ x<y y≤x = x<y .snd $ ≤-antisym (x<y .fst) y≤x

    ≤→≯ : ∀ {x y} {B : Type r'} → x ≤ y → y ≤[ B ] x → B
    ≤→≯ x≤y y<x = y<x .snd $ ≤-antisym (y<x .fst) x≤y

    <→≠ : ∀ {x y} {B : Type r'} → x ≤[ B ] y → x ≡ y → B
    <→≠ {B = B} x<y x≡y = x<y .snd x≡y

    <→≤ : ∀ {x y} {B : Type r'} → x ≤[ B ] y → x ≤ y
    <→≤ x<y = x<y .fst

    ≤+<→< : ∀ {x y z} {B : Type r'} → x ≤ y → y ≤[ B ] z → x ≤[ B ] z
    ≤+<→< x≤y y<z .fst = ≤-trans x≤y (y<z .fst)
    ≤+<→< x≤y y<z .snd x=z = <→≱ y<z (=+≤→≤ (sym x=z) x≤y)

    <+≤→< : ∀ {x y z} {B : Type r'} → x ≤[ B ] y → y ≤ z → x ≤[ B ] z
    <+≤→< x<y y≤z .fst = ≤-trans (x<y .fst) y≤z
    <+≤→< x<y y≤z .snd x=z = <→≱ x<y (≤+=→≤ y≤z (sym x=z))

  private
    data Related (r' : Level) : ⌞ A ⌟ → ⌞ A ⌟ → Type (o ⊔ r ⊔ lsuc r') where
      strict : ∀ {x y} (B : Type r') → x ≤[ B ] y → Related r' x y
      non-strict : ∀ {x y} → x ≤ y → Related r' x y

    Strict : ∀ {r' x y} → Related r' x y → Type
    Strict (strict _ _) = ⊤
    Strict (non-strict _) = ⊥

    Proj : ∀ {r' x y} → Related r' x y → Type r'
    Proj (strict B _) = B
    Proj (non-strict _) = Lift _ ⊤

  begin-<_ : ∀ {r' x y} → (x<y : Related r' x y) → {Strict x<y} → x ≤[ Proj x<y ] y
  begin-< (strict _ x<y) = x<y

  begin-≤[_]_ : ∀ r' {x y} → (x≤y : Related r' x y) → x ≤ y
  begin-≤[ r' ] (strict _ x<y) = x<y .fst
  begin-≤[ r' ] (non-strict x≤y) = x≤y

  step-< : ∀ {r'} {B} x {y z} → x ≤[ B ] y → Related r' y z → Related r' x z
  step-< {B = B} x x<y (non-strict y≤z) = strict B (<+≤→< x<y y≤z)
  step-< {B = B} x x<y (strict B' y<z) = strict (B × B') (<-trans' x<y y<z)

  step-≤ : ∀ {r'} x {y z} → x ≤ y → Related r' y z → Related r' x z
  step-≤ x x≤y (non-strict y≤z) = non-strict (≤-trans x≤y y≤z)
  step-≤ x x≤y (strict B y<z) = strict B (≤+<→< x≤y y<z)

  step-≡ : ∀ {r'} x {y z} → x ≡ y → Related r' y z → Related r' x z
  step-≡ x x≡y (non-strict y≤z) = non-strict (=+≤→≤ x≡y y≤z)
  step-≡ x x≡y (strict B y<z) = strict B (=+<→< x≡y y<z)

  _≤∎ : ∀ {r'} x → Related r' x x
  _≤∎ x = non-strict ≤-refl

  infix  1 begin-<_ begin-≤[_]_
  infixr 2 step-< step-≤ step-≡
  infix  3 _≤∎

  syntax step-< x p q = x <⟨ p ⟩ q
  syntax step-≤ x p q = x ≤⟨ p ⟩ q
  syntax step-≡ x p q = x ≐⟨ p ⟩ q
