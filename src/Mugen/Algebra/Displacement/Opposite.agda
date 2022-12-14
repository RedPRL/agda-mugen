module Mugen.Algebra.Displacement.Opposite where

open import Mugen.Prelude

open import Mugen.Algebra.Displacement
open import Mugen.Algebra.OrderedMonoid

open import Mugen.Order.Opposite
open import Mugen.Order.StrictOrder

--------------------------------------------------------------------------------
-- The Opposite Displacement Algebra
-- Section 3.3.8
--
-- Given a displacement algebra '๐', we can define another displacement
-- algebra with the same monoid structure, but with a reverse order.

module Op {o r} (๐ : DisplacementAlgebra o r) where
  open DisplacementAlgebra-on (structure ๐)

  --------------------------------------------------------------------------------
  -- Order

  _op<_ : โ ๐ โ โ โ ๐ โ โ Type r
  x op< y = ๐ [ y < x ]แต

  _opโค_ : โ ๐ โ โ โ ๐ โ โ Type (o โ r)
  x opโค y = ๐ [ y โค x ]แต

  from-opโค : โ {x y} โ x opโค y โ non-strict _op<_ x y
  from-opโค (inl yโกx) = inl (sym yโกx)
  from-opโค (inr y<x) = inr y<x

  to-opโค : โ {x y} โ non-strict _op<_ x y  โ x opโค y
  to-opโค (inl xโกy) = inl (sym xโกy)
  to-opโค (inr y<x) = inr y<x

  op-is-displacement-algebra : is-displacement-algebra _op<_ ฮต _โ_
  op-is-displacement-algebra .is-displacement-algebra.has-monoid = has-monoid
  op-is-displacement-algebra .is-displacement-algebra.has-strict-order = op-is-strict-order (DAโSO ๐)
  op-is-displacement-algebra .is-displacement-algebra.left-invariant = left-invariant

Op : โ {o r} โ DisplacementAlgebra o r โ DisplacementAlgebra o r
Op {o = o} {r = r} ๐ = displacement
  where
    open DisplacementAlgebra ๐
    open Op ๐

    displacement : DisplacementAlgebra o r
    โ displacement โ =  โ ๐ โ
    displacement .structure .DisplacementAlgebra-on._<_ = _op<_
    displacement .structure .DisplacementAlgebra-on.ฮต = ฮต
    displacement .structure .DisplacementAlgebra-on._โ_ = _โ_
    displacement .structure .DisplacementAlgebra-on.has-displacement-algebra = op-is-displacement-algebra
    โ displacement โ-set = โ ๐ โ-set

module OpProperties {o r} {๐ : DisplacementAlgebra o r} where
  open DisplacementAlgebra ๐
  open Op ๐

  --------------------------------------------------------------------------------
  -- Ordered Monoid

  op-has-ordered-monoid : has-ordered-monoid ๐ โ has-ordered-monoid (Op ๐)
  op-has-ordered-monoid ๐-ordered-monoid = right-invariantโhas-ordered-monoid (Op ๐) ฮป yโคx โ
    from-opโค $ right-invariant (to-opโค yโคx)
    where
      open is-ordered-monoid ๐-ordered-monoid
