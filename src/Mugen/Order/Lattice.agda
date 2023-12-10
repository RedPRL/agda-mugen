module Mugen.Order.Lattice where

open import Mugen.Prelude
open import Mugen.Algebra.OrderedMonoid
import Mugen.Order.Reasoning as Reasoning
open import Mugen.Order.StrictOrder

private variable
  o o' r r' : Level

--------------------------------------------------------------------------------
-- Joins and bottoms

module _ (A : Poset o r) where

  open Reasoning A

  -- Joins
  record has-joins : Type (o ⊔ r) where
    field
      join : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟
      joinl : ∀ {x y} → x ≤ join x y
      joinr : ∀ {x y} → y ≤ join x y
      universal : ∀ {x y z} → x ≤ z → y ≤ z → join x y ≤ z

  -- Bottoms
  record has-bottom : Type (o ⊔ r) where
    field
      bot : ⌞ A ⌟
      is-bottom : ∀ {x} → bot ≤ x

--------------------------------------------------------------------------------
-- Full Subposets with Joins

record is-full-subsemilattice
  {A : Poset o r} {B : Poset o' r'}
  (A-joins : has-joins A) (B-joins : has-joins B)
  (f : Strictly-monotone A B)
  : Type (o ⊔ o' ⊔ r' ⊔ r)
  where
  private
    module A = has-joins A-joins
    module B = has-joins B-joins
  field
    has-is-full-subposet : is-full-subposet f
    pres-join : ∀ {x y : ⌞ A ⌟} → f # A.join x y ≡ B.join (f # x) (f # y)
  open is-full-subposet has-is-full-subposet public

record represents-full-subsemilattice
  {A : Poset o r} {B : Poset o' r'} (B-joins : has-joins B)
  {f : Strictly-monotone A B} (full-subposet : is-full-subposet f)
  : Type (o ⊔ o')
  where
  no-eta-equality
  private
    module B-joins = has-joins B-joins
  field
    join : ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟
    pres-join : ∀ {x y : ⌞ A ⌟} → f # (join x y) ≡ B-joins.join (f # x) (f # y)

  private
    open is-full-subposet full-subposet
    module B = Reasoning B
    module f = Strictly-monotone f

  joins : has-joins A
  joins .has-joins.join = join
  joins .has-joins.joinl {x} {y} =
    full $ B.≤+=→≤ (B-joins.joinl {f # x} {f # y}) (sym pres-join)
  joins .has-joins.joinr {x} {y} =
    full $ B.≤+=→≤ (B-joins.joinr {f # x} {f # y}) (sym pres-join)
  joins .has-joins.universal {x} {y} x≤r y≤r =
    full $ B.=+≤→≤ pres-join (B-joins.universal (f.pres-≤ x≤r) (f.pres-≤ y≤r))

  has-is-full-subsemilattice : is-full-subsemilattice joins B-joins f
  has-is-full-subsemilattice .is-full-subsemilattice.has-is-full-subposet =
    full-subposet
  has-is-full-subsemilattice .is-full-subsemilattice.pres-join =
    pres-join

--------------------------------------------------------------------------------
-- Full Subposets with Bottom

record is-full-bounded-subposet
  {A : Poset o r} {B : Poset o' r'}
  (A-bottom : has-bottom A)
  (B-bottom : has-bottom B)
  (f : Strictly-monotone A B)
  : Type (o ⊔ o' ⊔ r ⊔ r') where
  no-eta-equality
  private
    module A-bottom = has-bottom A-bottom
    module B-bottom = has-bottom B-bottom
  field
    has-is-full-subposet : is-full-subposet f
    pres-bot : f # A-bottom.bot ≡ B-bottom.bot
  open is-full-subposet has-is-full-subposet public

record represents-full-bounded-subposet
  {A : Poset o r} {B : Poset o' r'} (B-bottom : has-bottom B)
  {f : Strictly-monotone A B} (full-subposet : is-full-subposet f)
  : Type (o ⊔ o')
  where
  no-eta-equality
  private
    open is-full-subposet full-subposet
    module B = Reasoning B
    module B-bottom = has-bottom B-bottom
    module f = Strictly-monotone f

  field
    bot : ⌞ A ⌟
    pres-bot : f # bot ≡ B-bottom.bot

  bottom : has-bottom A
  bottom .has-bottom.bot = bot
  bottom .has-bottom.is-bottom {x} =
    full $ B.=+≤→≤ pres-bot B-bottom.is-bottom

  has-is-full-bounded-subposet : is-full-bounded-subposet bottom B-bottom f
  has-is-full-bounded-subposet .is-full-bounded-subposet.has-is-full-subposet = full-subposet
  has-is-full-bounded-subposet .is-full-bounded-subposet.pres-bot = pres-bot
