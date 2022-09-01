module Mugen.Order.StrictOrder where

open import Mugen.Prelude
open import Mugen.Order.Poset

--------------------------------------------------------------------------------
-- Strict Orders

record is-strict-order {o r} {A : Type o} (_<_ : A → A → Type r) : Type (o ⊔ r) where
  no-eta-equality
  field
    irrefl : ∀ {x} → x < x → ⊥
    trans : ∀ {x y z} → x < y → y < z → x < z
    has-prop : ∀ {x y} → is-prop (x < y)

  asym : ∀ {x y} → x < y → y < x → ⊥
  asym x<y y<x = irrefl (trans x<y y<x)

  _≤_ : A → A → Type (o ⊔ r)
  x ≤ y = x ≡ y ⊎ x < y

  instance
    <-hlevel : ∀ {x y} {n} → H-Level (x < y) (suc n)
    <-hlevel = prop-instance has-prop

  ≡-transl : ∀ {x y z} → x ≡ y → y < z → x < z
  ≡-transl x≡y y<z = subst (λ ϕ → ϕ < _) (sym x≡y) y<z

  ≡-transr : ∀ {x y z} → x < y → y ≡ z → x < z
  ≡-transr x<y y≡z = subst (λ ϕ → _ < ϕ) y≡z x<y

  ≤-transl : ∀ {x y z} → x ≤ y → y < z → x < z
  ≤-transl (inl x≡y) y<z = ≡-transl x≡y y<z
  ≤-transl (inr x<y) y<z = trans x<y y<z

  ≤-transr : ∀ {x y z} → x < y → y ≤ z → x < z
  ≤-transr x<y (inl y≡z) = ≡-transr x<y y≡z
  ≤-transr x<y (inr y<z) = trans x<y y<z

  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans (inl p) (inl q) = inl (p ∙ q)
  ≤-trans (inl p) (inr y<z) = inr (≡-transl p y<z)
  ≤-trans (inr x<y) (inl q) = inr (≡-transr x<y q)
  ≤-trans (inr x<y) (inr y<z) = inr (trans x<y y<z)

  ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
  ≤-antisym (inl x≡y) y≤x = x≡y
  ≤-antisym (inr x<y) (inl y≡x) = sym y≡x
  ≤-antisym (inr x<y) (inr y<x) = absurd (irrefl (trans x<y y<x))


  <→≤ : ∀ {x y} → x < y → x ≤ y
  <→≤ x<y = inr x<y

private unquoteDecl eqv = declare-record-iso eqv (quote is-strict-order)

instance
  is-strict-order-hlevel : ∀ {o r} {A : Type o} {_<_ : A → A → Type r} {n}
                           → H-Level (is-strict-order _<_) (suc n)
  is-strict-order-hlevel = prop-instance λ x →
     let open is-strict-order x in
     is-hlevel≃ 1 (Iso→Equiv eqv e⁻¹) (hlevel 1) x

record StrictOrder-on {o : Level} (r : Level) (A : Type o) : Type (o ⊔ lsuc r) where
  no-eta-equality
  field
    _<_ : A → A → Type r
    has-is-strict-order : is-strict-order _<_

  open is-strict-order has-is-strict-order public

StrictOrder : ∀ o r → Type (lsuc o ⊔ lsuc r)
StrictOrder o r = SetStructure (StrictOrder-on {o} r)

module StrictOrder {o r} (S : StrictOrder o r) where
  open StrictOrder-on (structure S) public

  ≤-is-prop : ∀ {x y} → is-prop (x ≤ y)
  ≤-is-prop = disjoint-⊎-is-prop (⌞ S ⌟-set _ _) has-prop λ {  (x≡y , x<y) → irrefl (≡-transr x<y (sym x≡y))  }

private variable
  o r : Level
  X Y Z : StrictOrder o r

_[_<_] : ∀ (X : StrictOrder o r) → ⌞ X ⌟ → ⌞ X ⌟ → Type r
X [ x < y ] = StrictOrder-on._<_ (structure X) x y

_[_≤_] : ∀ (X : StrictOrder o r) → ⌞ X ⌟ → ⌞ X ⌟ → Type (o ⊔ r)
X [ x ≤ y ] = StrictOrder-on._≤_ (structure X) x y

--------------------------------------------------------------------------------
-- Strictly Monotonic Maps

strictly-monotonic : ∀ (X Y : StrictOrder o r) (f : ⌞ X ⌟ → ⌞ Y ⌟) → Type (o ⊔ r) 
strictly-monotonic X Y f = ∀ {x y} → X [ x < y ] → Y [ f x < f y ]


strictly-monotonic-is-prop : ∀ (X Y : StrictOrder o r) (f : ⌞ X ⌟ → ⌞ Y ⌟) → is-prop (strictly-monotonic X Y f)
strictly-monotonic-is-prop X Y f =
  let open StrictOrder-on (structure Y)
  -- For whatever reason we need to do this to get things to compute?? Odd.
  in Π-is-hlevel′ 1 λ x → hlevel 1

StrictOrder-Hom : ∀ (X Y : StrictOrder o r) → Type (o ⊔ r)
StrictOrder-Hom = Homomorphism strictly-monotonic

instance
  strict-order-hlevel : ∀ {n} → H-Level (StrictOrder-Hom X Y) (2 + n)
  strict-order-hlevel = homomorphism-hlevel strictly-monotonic-is-prop

strictly-mono→mono : ∀ {X Y : StrictOrder o r} {x y} → (f : StrictOrder-Hom X Y) → X [ x ≤ y ] → Y [ f ⟨$⟩ x ≤ f ⟨$⟩ y ]
strictly-mono→mono {Y = Y} f (inl p) = inl (ap (f ⟨$⟩_) p)
strictly-mono→mono {Y = Y} f (inr x<y) = inr (f .homo x<y)
  where
    module Y = StrictOrder-on (structure Y)

--------------------------------------------------------------------------------
-- Constructing Strict Orders from Preorders
module _ where
  
  private variable
    A : Type o
    _≤_ : A → A → Type r
  
  strict : ∀ {A : Type o} (_≤_ : A → A → Type r) → A → A → Type r
  strict _≤_ x y = (x ≤ y) × ((y ≤ x) → ⊥)
  
  is-preorder→is-strict-order : ∀ {A : Type o} {_≤_ : A → A → Type r} → is-preorder _≤_ → is-strict-order (strict _≤_)
  is-preorder→is-strict-order {A = A} {_≤_ = _≤_} preorder = strict-order
    where
      open is-preorder preorder
  
      strict-order : is-strict-order (strict _≤_)
      strict-order .is-strict-order.irrefl (_ , x≰x) = x≰x reflexive
      strict-order .is-strict-order.trans {x} {y} {z} (x≤y , y≰x) (y≤z , z≰y) =
        transitive x≤y y≤z , λ z≤x → z≰y (transitive z≤x x≤y)
      strict-order .is-strict-order.has-prop = Σ-is-hlevel 1 propositional λ _ → hlevel 1
  
  Preorder-on→StrictOrder-on : ∀ {A : Type o} → Preorder-on r A → StrictOrder-on r A
  Preorder-on→StrictOrder-on P .StrictOrder-on._<_ = strict (Preorder-on._≤_ P)
  Preorder-on→StrictOrder-on P .StrictOrder-on.has-is-strict-order = is-preorder→is-strict-order (Preorder-on.has-is-preorder P)
  
  Preorder→StrictOrder : ∀ {o r} → Preorder o r → StrictOrder o r
  Preorder→StrictOrder = map-structure Preorder-on→StrictOrder-on
  
  --------------------------------------------------------------------------------
  -- Constructing Preorders from Strict Orders
  
  non-strict : ∀ {A : Type o} (_<_ : A → A → Type r) → A → A → Type (o ⊔ r)
  non-strict _<_ x y = x ≡ y ⊎ x < y
  
  is-strict-order→is-preorder : ∀ {A : Type o} {_<_ : A → A → Type r} → is-set A → is-strict-order _<_ → is-preorder (non-strict _<_)
  is-strict-order→is-preorder {_<_ = _<_} A-set strict-order = preorder
    where
      open is-strict-order strict-order
  
      preorder : is-preorder (non-strict _<_)
      preorder .is-preorder.reflexive = inl refl
      preorder .is-preorder.transitive = ≤-trans
      preorder .is-preorder.propositional =  disjoint-⊎-is-prop (A-set _ _) has-prop λ {  (x≡y , x<y) → irrefl (≡-transr x<y (sym x≡y))  }

  StrictOrder-on→Preorder-on : ∀ {A : Type o} → is-set A → StrictOrder-on r A → Preorder-on (o ⊔ r) A
  StrictOrder-on→Preorder-on A-set strict .Preorder-on._≤_ = non-strict (StrictOrder-on._<_ strict)
  StrictOrder-on→Preorder-on A-set strict .Preorder-on.has-is-preorder = is-strict-order→is-preorder A-set (StrictOrder-on.has-is-strict-order strict)
  
  StrictOrder→Preorder : ∀ {o r} → StrictOrder o r → Preorder o (o ⊔ r)
  ⌞ StrictOrder→Preorder S ⌟ = ⌞ S ⌟
  StrictOrder→Preorder S .structure = StrictOrder-on→Preorder-on ⌞ S ⌟-set (structure S)
  ⌞ StrictOrder→Preorder S ⌟-set = ⌞ S ⌟-set

  --------------------------------------------------------------------------------
  -- Constructing Partial Orders from Strict Orders

  is-strict-order→is-partial-order : ∀ {A : Type o} {_<_ : A → A → Type r} → is-set A → is-strict-order _<_ → is-partial-order (non-strict _<_)
  is-strict-order→is-partial-order {_<_ = _<_} A-set strict-order = partial-order
    where
      open is-strict-order strict-order
       
      partial-order : is-partial-order (non-strict _<_)
      partial-order .is-partial-order.preorder = is-strict-order→is-preorder A-set strict-order
      partial-order .is-partial-order.antisym = ≤-antisym

--------------------------------------------------------------------------------
-- Reasoning

module StrictOrder-Reasoning {o r} (A : StrictOrder o r) where
  open StrictOrder A

  infix  1 begin-<_ begin-≤_
  infixr 2 step-< step-≤ step-≡
  infix  3 _<∎

  data _IsRelatedTo_ : ⌞ A ⌟ → ⌞ A ⌟ → Type (o ⊔ r) where
    done : ∀ x → x IsRelatedTo x
    strong : ∀ x y → x < y → x IsRelatedTo y
    weak : ∀ x y → x ≤ y → x IsRelatedTo y

  Strong : ∀ {x y} → x IsRelatedTo y → Type
  Strong (done _) = ⊥
  Strong (strong _ _ _) = ⊤
  Strong (weak _ _ _) = ⊥

  begin-<_ : ∀ {x y} → (x<y : x IsRelatedTo y) → {Strong x<y} → x < y
  begin-< (strong _ _ x<y) = x<y

  begin-≤_ : ∀ {x y} → (x≤y : x IsRelatedTo y) → x ≤ y
  begin-≤ done x = inl refl
  begin-≤ strong x y x<y = inr x<y
  begin-≤ weak x y x≤y = x≤y

  step-< : ∀ x {y z} → y IsRelatedTo z → x < y → x IsRelatedTo z
  step-< x (done y) x<y = strong x y x<y
  step-< x (strong y z y<z) x<y = strong x z (trans x<y y<z)
  step-< x (weak y z y≤z) x<y = strong x z (≤-transr x<y y≤z)

  step-≤ : ∀ x {y z} → y IsRelatedTo z → x ≤ y → x IsRelatedTo z
  step-≤ x (done y) x≤y = weak x y x≤y
  step-≤ x (strong y z y<z) x≤y = strong x z (≤-transl x≤y y<z)
  step-≤ x (weak y z y≤z) x≤y = weak x z (≤-trans x≤y y≤z)

  step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
  step-≡ x (done y) p = subst (x IsRelatedTo_) p (done x)
  step-≡ x (strong y z y<z) p = strong x z (subst (_< z) (sym p) y<z)
  step-≡ x (weak y z y≤z) p = weak x z (subst (_≤ z) (sym p) y≤z)

  _<∎ : ∀ x → x IsRelatedTo x
  _<∎ x = done x

  syntax step-< x q p = x <⟨ p ⟩ q
  syntax step-≤ x q p = x ≤⟨ p ⟩ q
  syntax step-≡ x q p = x ≡̇⟨ p ⟩ q
