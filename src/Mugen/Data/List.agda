module Mugen.Data.List where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

-- The version of reverse in the 1Lab is difficult to reason about,
-- due to a where-bound recursive helper. Instead, we define our own.
open import Data.List hiding (reverse) public

open import Mugen.Prelude

private variable
  ℓ : Level
  A B : Type ℓ

replicate : Nat → A → List A
replicate zero x = []
replicate (suc n) x = x ∷ (replicate n x)

module _ {ℓ} {A : Type ℓ} (aset : is-set A) where

  ++-is-magma : is-magma {A = List A} _++_
  ++-is-magma .has-is-set = ListPath.List-is-hlevel 0 aset
  
  ++-is-semigroup : is-semigroup {A = List A} _++_
  ++-is-semigroup .has-is-magma = ++-is-magma
  ++-is-semigroup .associative {x} {y} {z} = sym (++-assoc x y z)

  ++-is-monoid : is-monoid {A = List A} [] _++_
  ++-is-monoid .has-is-semigroup = ++-is-semigroup
  ++-is-monoid .idl {x} = ++-idl x
  ++-is-monoid .idr {x} = ++-idr x

--------------------------------------------------------------------------------
-- Backwards Lists

data Bwd {ℓ} (A : Type ℓ) : Type ℓ where
  [] : Bwd A
  _#r_ : Bwd A → A → Bwd A

infixl 20 _#r_

#r≠[] : ∀ {xs : Bwd A} {x : A} → xs #r x ≡ [] → ⊥
#r≠[] {A = A} p = subst discrim p tt
  where
    discrim : Bwd A → Type
    discrim [] = ⊥
    discrim (_ #r _) = ⊤

last : A → Bwd A → A
last def [] = def
last def (xs #r x) = x

init : Bwd A → Bwd A
init [] = []
init (xs #r x) = xs

#r-last-inj : ∀ {xs ys : Bwd A} {x y} → xs #r x ≡ ys #r y → x ≡ y
#r-last-inj {x = x} p = ap (last x) p

#r-init-inj : ∀ {xs ys : Bwd A} {x y} → xs #r x ≡ ys #r y → xs ≡ ys
#r-init-inj p = ap init p

-- Left action of backwards lists upon lists.
_⊗▷_ : Bwd A → List A → List A
[] ⊗▷ ys = ys
(xs #r x) ⊗▷ ys = xs ⊗▷ (x ∷ ys) 

-- Right action of lists upon backwards lists.
_◁⊗_ : Bwd A → List A → Bwd A
xs ◁⊗ [] = xs
xs ◁⊗ (y ∷ ys) = (xs #r y) ◁⊗ ys

-- Reassociate into a backwards list.
bwd : List A → Bwd A
bwd xs = [] ◁⊗ xs

-- Reassociate into a forwards list.
fwd : Bwd A → List A
fwd xs = xs ⊗▷ []


_++r_ : Bwd A → Bwd A → Bwd A
xs ++r [] = xs
xs ++r (ys #r y) = (xs ++r ys) #r y

++r-assoc : ∀ (xs ys zs : Bwd A) → xs ++r (ys ++r zs) ≡ (xs ++r ys) ++r zs
++r-assoc xs ys [] = refl
++r-assoc xs ys (zs #r z) = ap (_#r z) (++r-assoc xs ys zs)

++r-idl : ∀ (xs : Bwd A) → [] ++r xs ≡ xs
++r-idl [] = refl
++r-idl (xs #r x) = ap (_#r x) (++r-idl xs)

◁⊗-bwd : ∀ (xs : Bwd A) (ys : List A) → xs ◁⊗ ys ≡ xs ++r bwd ys
◁⊗-bwd xs [] = refl
◁⊗-bwd xs (y ∷ ys) =
  (xs #r y) ◁⊗ ys                     ≡⟨ ◁⊗-bwd (xs #r y) ys ⟩
  ((xs #r y) ++r bwd ys)              ≡˘⟨ ++r-assoc xs ([] #r y) (bwd ys) ⟩
  (xs ++r (([] #r y) ++r bwd ys))     ≡˘⟨ ap (xs ++r_) (◁⊗-bwd ([] #r y) ys) ⟩
  (xs ++r (([] #r y) ◁⊗ ys))          ≡⟨⟩
  (xs ++r bwd (y ∷ ys))               ∎

⊗▷-fwd : ∀ (xs : Bwd A) (ys : List A) → xs ⊗▷ ys ≡ fwd xs ++ ys
⊗▷-fwd [] ys = refl
⊗▷-fwd (xs #r x) ys =
  (xs ⊗▷ (x ∷ ys))         ≡⟨ ⊗▷-fwd xs (x ∷ ys) ⟩
  fwd xs ++ x ∷ ys         ≡˘⟨ ++-assoc (fwd xs) (x ∷ []) ys ⟩
  (fwd xs ++ x ∷ []) ++ ys ≡˘⟨ ap (_++ ys) (⊗▷-fwd xs (x ∷ [])) ⟩
  (xs ⊗▷ (x ∷ [])) ++ ys   ≡⟨⟩
  fwd (xs #r x) ++ ys      ∎

fwd-++r : ∀ (xs ys : Bwd A) → fwd (xs ++r ys) ≡ fwd xs ++ fwd ys
fwd-++r xs [] = sym (++-idr (fwd (xs ++r [])))
fwd-++r xs (ys #r y) =
  ((xs ++r ys) ⊗▷ (y ∷ []))    ≡⟨ ⊗▷-fwd (xs ++r ys) (y ∷ []) ⟩
  fwd (xs ++r ys) ++ y ∷ []    ≡⟨ ap (_++ y ∷ []) (fwd-++r xs ys) ⟩
  (fwd xs ++ fwd ys) ++ y ∷ [] ≡⟨ ++-assoc (fwd xs) (fwd ys) (y ∷ []) ⟩
  fwd xs ++ fwd ys ++ y ∷ []   ≡˘⟨ ap (fwd xs ++_) (⊗▷-fwd ys (y ∷ [])) ⟩
  fwd xs ++ (ys ⊗▷ (y ∷ []))   ∎

bwd-++ : ∀ (xs ys : List A) → bwd (xs ++ ys) ≡ bwd xs ++r bwd ys
bwd-++ [] ys = sym (++r-idl (bwd ([] ++ ys)))
bwd-++ (x ∷ xs) ys =
  (([] #r x) ◁⊗ (xs ++ ys))           ≡⟨ ◁⊗-bwd ([] #r x) (xs ++ ys) ⟩
  (([] #r x) ++r bwd (xs ++ ys))      ≡⟨ ap (([] #r x) ++r_) (bwd-++ xs ys) ⟩
  (([] #r x) ++r (bwd xs ++r bwd ys)) ≡⟨ ++r-assoc ([] #r x) (bwd xs) ([] ◁⊗ ys) ⟩
  ((([] #r x) ++r bwd xs) ++r bwd ys) ≡˘⟨ ap (_++r bwd ys) (◁⊗-bwd ([] #r x) xs) ⟩
  ((([] #r x) ◁⊗ xs) ++r bwd ys) ∎

fwd-bwd : ∀ (xs : List A) → fwd (bwd xs) ≡ xs
fwd-bwd [] = refl
fwd-bwd (x ∷ xs) =
  fwd (bwd (x ∷ xs))         ≡⟨⟩
  fwd (([] #r x) ◁⊗ xs)      ≡⟨ ap fwd (◁⊗-bwd ([] #r x) xs) ⟩
  fwd (([] #r x) ++r bwd xs) ≡⟨ fwd-++r ([] #r x) (bwd xs) ⟩
  x ∷ fwd (bwd xs)           ≡⟨ ap (x ∷_) (fwd-bwd xs) ⟩
  x ∷ xs ∎

bwd-fwd : ∀ (xs : Bwd A) → bwd (fwd xs) ≡ xs
bwd-fwd [] = refl
bwd-fwd (xs #r x) =
  bwd (fwd (xs #r x))    ≡⟨⟩
  bwd (xs ⊗▷ (x ∷ []))   ≡⟨ ap bwd (⊗▷-fwd xs (x ∷ [])) ⟩
  bwd (fwd xs ++ x ∷ []) ≡⟨ bwd-++ (fwd xs) (x ∷ []) ⟩
  bwd (fwd xs) #r x      ≡⟨ ap (_#r x) (bwd-fwd xs) ⟩
  xs #r x ∎

List≃Bwd : List A ≃ Bwd A
List≃Bwd = Iso→Equiv (bwd , iso fwd bwd-fwd fwd-bwd)

Bwd-is-hlevel : (n : Nat) → is-hlevel A (2 + n) → is-hlevel (Bwd A) (2 + n)
Bwd-is-hlevel n ahl = is-hlevel≃ (2 + n) List≃Bwd (List-is-hlevel n ahl)
  where open ListPath

instance
  H-Level-Bwd : ∀ {n} {k} → ⦃ H-Level A (2 + n) ⦄ → H-Level (Bwd A) (2 + n + k)
  H-Level-Bwd {n = n} ⦃ x ⦄ = 
    basic-instance (2 + n) (Bwd-is-hlevel n (H-Level.has-hlevel x))


fwd-#r : ∀ (xs : Bwd A) (x : A) → Σ[ y ∈ A ] Σ[ ys ∈ List A ] (y ∷ ys ≡ fwd (xs #r x))
fwd-#r [] x = x , [] , refl
fwd-#r (xs #r x′) x =
  let (y , ys , p) = fwd-#r xs x′
  in y , ys ∷r x , ap (_∷r x) p ∙ sym (fwd-++r (xs #r x′) ([] #r x))

bwd-∷ : ∀ (x : A) (xs : List A) → Σ[ ys ∈ Bwd A ] Σ[ y ∈ A ] (ys #r y ≡ bwd (x ∷ xs))
bwd-∷ x [] = [] , x , refl
bwd-∷ x (x′ ∷ xs) =
  let (ys , y , p) = bwd-∷ x′ xs
  in ([] #r x) ++r ys , y , ap (([] #r x) ++r_) p ∙ sym (bwd-++ (x ∷ []) (x′ ∷ xs))
