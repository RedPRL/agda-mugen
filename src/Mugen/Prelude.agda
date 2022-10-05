module Mugen.Prelude where

open import Cat.Prelude public
open import Data.Sum public

--------------------------------------------------------------------------------
-- The Mugen Prelude
--
-- This exports a bunch of stuff from the 1lab that we use,
-- along with some helpers for structures over set + their homomorphisms.
-- There's also some misc. junk that we need everywhere.

--------------------------------------------------------------------------------
-- Set Structures

is-set→is-hlevel+2
  : ∀ {ℓ} {A : Type ℓ} {n : Nat} → is-set A → is-hlevel A (2 + n)
is-set→is-hlevel+2 aset x y = is-prop→is-hlevel-suc (aset x y)

set-instance : ∀ {ℓ} {T : Type ℓ} → is-set T → ∀ {k} → H-Level T (2 + k)
set-instance {T = T} hl = hlevel-instance (is-set→is-hlevel+2 hl)

record SetStructure {o s} (S : Type o → Type s) : Type (lsuc o ⊔ s) where
  no-eta-equality
  field
    ⌞_⌟ : Type o
    structure : S ⌞_⌟
    ⌞_⌟-set : is-set ⌞_⌟

  instance
    ⌞_⌟-hlevel : ∀ {n} → H-Level ⌞_⌟ (2 + n)
    ⌞_⌟-hlevel = set-instance ⌞_⌟-set

open SetStructure public

map-structure : ∀ {o s s′} {S : Type o → Type s} {T : Type o → Type s′}
                  (f : ∀ {A : Type o} → S A → T A)
                  → SetStructure S → SetStructure T
⌞ map-structure f S ⌟ =  ⌞ S ⌟
map-structure f S .structure = f (structure S)
⌞ map-structure f S ⌟-set = ⌞ S ⌟-set

--------------------------------------------------------------------------------
-- Homomorphisms

record Homomorphism {o s h} {S : Type o → Type s}
                    (H : (X Y : SetStructure S) → (⌞ X ⌟ → ⌞ Y ⌟) → Type h)
                    (X Y : SetStructure S) : Type (o ⊔ h) where
  constructor homomorphism
  infixr 5 _⟨$⟩_
  field
    _⟨$⟩_ : ⌞ X ⌟ → ⌞ Y ⌟
    homo : H X Y _⟨$⟩_

private unquoteDecl homo-eqv = declare-record-iso homo-eqv (quote Homomorphism)

homomorphism-hlevel : ∀ {n} {o s h} {S : Type o → Type s} {X Y : SetStructure S} 
                      {H : (X Y : SetStructure S) → (⌞ X ⌟ → ⌞ Y ⌟) → Type h}
                      → (homo-prop : (X Y : SetStructure S) → (f : ⌞ X ⌟ → ⌞ Y ⌟) → is-prop (H X Y f))
                      → H-Level (Homomorphism H X Y) (2 + n)
homomorphism-hlevel {X = X} {Y = Y} homo-prop = set-instance $
    let open SetStructure
    in is-hlevel≃ 2 (Iso→Equiv homo-eqv e⁻¹) (Σ-is-hlevel 2 (Π-is-hlevel 2 λ _ → ⌞ Y ⌟-set) λ f → is-prop→is-set (homo-prop X Y f))

open Homomorphism public

private variable
  o s h : Level
  S : Type o → Type s
  X Y : SetStructure S
  H : (X Y : SetStructure S) → (⌞ X ⌟ → ⌞ Y ⌟) → Type h
  f g : Homomorphism H X Y
    
homomorphism-path : (homo-prop : (X Y : SetStructure S) → (f : ⌞ X ⌟ → ⌞ Y ⌟) → is-prop (H X Y f)) → {f g : Homomorphism H X Y} → (∀ x → f ⟨$⟩ x ≡ g ⟨$⟩ x) → f ≡ g 
homomorphism-path homo-prop path i ._⟨$⟩_ x =
  path x i
homomorphism-path {X = X} {Y = Y} homo-prop {f = f} {g = g} path i .homo =
  is-prop→pathp (λ i → homo-prop X Y (λ x → path x i)) (homo f) (homo g) i

--------------------------------------------------------------------------------
-- Actions

record RightAction {o o′ s s′ h} {S : Type o → Type s} {T : Type o′ → Type s′}
                   (H : (X : SetStructure S) → (Y : SetStructure T) → (⌞ X ⌟ → ⌞ Y ⌟ → ⌞ X ⌟) → Type h)
                   (X : SetStructure S) (Y : SetStructure T) : Type (o ⊔ o′ ⊔ h) where
  constructor right-action
  field
    ⟦_⟧ʳ : ⌞ X ⌟ → ⌞ Y ⌟ → ⌞ X ⌟
    is-action : H X Y ⟦_⟧ʳ

open RightAction public

--------------------------------------------------------------------------------
-- HLevels

instance
  ⊎-hlevel : ∀ {a b} {A : Type a} {B : Type b} {n}
              → ⦃ H-Level A (2 + n) ⦄ → ⦃ H-Level B (2 + n) ⦄
              → H-Level (A ⊎ B) (2 + n)
  ⊎-hlevel {n = n} = hlevel-instance $ ⊎-is-hlevel _ (hlevel (2 + n)) (hlevel (2 + n))

--------------------------------------------------------------------------------
-- Decidability

dec-map : ∀ {ℓ ℓ′} {P : Type ℓ} {Q : Type ℓ′} → (P → Q) → (Q → P) → Dec P → Dec Q
dec-map to from (yes p) = yes (to p)
dec-map to from (no ¬p) = no (λ q → ¬p (from q))

--------------------------------------------------------------------------------
-- Misc.

subst₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} (P : A → B → Type ℓ₃) {a1 a2 : A} {b1 b2 : B}
       → a1 ≡ a2 → b1 ≡ b2 → P a1 b1 → P a2 b2
subst₂ P p q x = subst (λ a → P a _) p (subst (λ b → P _ b) q x) 

record Reveal_·_is_ {a b} {A : Type a} {B : A → Type b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Type (a ⊔ b) where
  constructor evidence
  field eq : f x ≡ y

remember : ∀ {a b} {A : Type a} {B : A → Type b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
remember f x = evidence refl

infixr -1 _|>_

_|>_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} → (x : A) → ((x : A) → B x) → B x
x |> f = f x
{-# INLINE _|>_ #-}

over : ∀ {ℓ} {A : Type ℓ} {x y : A} {f : A → A} → (∀ x → f x ≡ x) → f x ≡ f y → x ≡ y
over {x = x} {y = y} p q =  sym (p x) ·· q ·· p y 
