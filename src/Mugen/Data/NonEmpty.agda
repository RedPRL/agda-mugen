module Mugen.Data.NonEmpty where

open import Mugen.Prelude

--------------------------------------------------------------------------------
-- Non-Empty Lists

data List⁺ {ℓ} (A : Type ℓ) : Type ℓ where
  [_] : A → List⁺ A
  _∷_ : A → List⁺ A → List⁺ A

private variable
  ℓ : Level
  A : Type ℓ

head : List⁺ A → A
head [ x ] = x
head (x ∷ xs) = x

tail : List⁺ A → List⁺ A
tail [ x ] = [ x ]
tail (x ∷ xs) = xs

[]-inj : ∀ {x y : A} → [ x ] ≡ [ y ] → x ≡ y
[]-inj p = ap head p

∷-head-inj : ∀ {x y : A} {xs ys : List⁺ A} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
∷-head-inj p = ap head p

[]≢∷ : ∀ {x y : A} {ys : List⁺ A} → [ x ] ≡ y ∷ ys → ⊥
[]≢∷ p = subst distinguish p tt
  where
    distinguish : List⁺ A → Type
    distinguish [ x ] = ⊤
    distinguish (x ∷ xs) = ⊥

module List⁺-Path {ℓ} {A : Type ℓ} where
  Code : List⁺ A → List⁺ A → Type ℓ
  Code [ x ] [ y ] = x ≡ y
  Code [ x ] (y ∷ ys) = Lift _ ⊥
  Code (x ∷ xs) [ _ ] = Lift _ ⊥
  Code (x ∷ xs) (y ∷ ys) = (x ≡ y) × Code xs ys

  encode : ∀ {xs ys : List⁺ A} → xs ≡ ys → Code xs ys
  encode {xs = [ x ]} {ys = [ y ]} xs≡ys = []-inj xs≡ys
  encode {xs = [ x ]} {ys = y ∷ ys} xs≡ys = lift ([]≢∷ xs≡ys)
  encode {xs = x ∷ xs} {ys = [ y ]} xs≡ys = lift ([]≢∷ (sym xs≡ys))
  encode {xs = x ∷ xs} {ys = y ∷ ys} xs≡ys = ∷-head-inj xs≡ys , encode {xs = xs} {ys = ys} (ap tail xs≡ys)

  decode : ∀ {xs ys : List⁺ A} → Code xs ys → xs ≡ ys
  decode {xs = [ x ]} {ys = [ y ]} p = ap [_] p
  decode {xs = x ∷ xs} {ys = y ∷ ys} (p , q) = ap₂ _∷_ p (decode q)

  encode-decode : ∀ {xs ys : List⁺ A} → (p : Code xs ys) → encode (decode p) ≡ p
  encode-decode {xs = [ x ]} {ys = [ y ]} p = refl
  encode-decode {xs = x ∷ xs} {ys = y ∷ ys} (p , q) = ap (p ,_) (encode-decode q)

  decode-encode : ∀ {xs ys : List⁺ A} → (p : xs ≡ ys) → decode (encode p) ≡ p
  decode-encode {xs = xs} {ys = ys} = J (λ y p → decode (encode p) ≡ p) de-refl where
    de-refl : ∀ {xs : List⁺ A} → decode (encode (λ i → xs)) ≡ (λ i → xs)
    de-refl {xs = [ x ]} = refl
    de-refl {xs = x ∷ xs} i j = x ∷ (de-refl {xs = xs} i j)

  Code≃Path : ∀ {xs ys : List⁺ A} →  (xs ≡ ys) ≃ Code xs ys
  Code≃Path = Iso→Equiv (encode , iso decode encode-decode decode-encode)

open List⁺-Path

List⁺-is-hlevel : (n : Nat) → is-hlevel A (2 + n) → is-hlevel (List⁺ A) (2 + n)
List⁺-is-hlevel {A = A} n ahl x y = is-hlevel≃ (suc n) Code≃Path List⁺-Code-is-hlevel where
  List⁺-Code-is-hlevel : ∀ {xs ys : List⁺ A} → is-hlevel (Code xs ys) (suc n)
  List⁺-Code-is-hlevel {xs = [ x ]} {ys = [ y ]} = ahl x y
  List⁺-Code-is-hlevel {xs = [ x ]} {ys = y ∷ ys} = is-prop→is-hlevel-suc (λ x → absurd (Lift.lower x))
  List⁺-Code-is-hlevel {xs = x ∷ xs} {ys = [ y ]} = is-prop→is-hlevel-suc (λ x → absurd (Lift.lower x))
  List⁺-Code-is-hlevel {xs = x ∷ xs} {ys = y ∷ ys} = ×-is-hlevel (suc n) (ahl x y) List⁺-Code-is-hlevel
