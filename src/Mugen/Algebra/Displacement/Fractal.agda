module Mugen.Algebra.Displacement.Fractal where

open import Algebra.Magma
open import Algebra.Monoid
open import Algebra.Semigroup

open import Mugen.Prelude
open import Mugen.Data.NonEmpty

open import Mugen.Algebra.Displacement
open import Mugen.Order.StrictOrder

--------------------------------------------------------------------------------
-- Fractal Displacements
-- Section 3.3.7

module _ {o r} (ð : DisplacementAlgebra o r) where
  private
    module ð = DisplacementAlgebra-on (structure ð)
    open ð using (Îµ; _â_)

  --------------------------------------------------------------------------------
  -- Algebra

  _âá¶ _ : Listâº â ð â â Listâº â ð â â Listâº â ð â
  [ x ] âá¶  [ y ] = [ x â y ]
  [ x ] âá¶  (y â· ys) = (x â y) â· ys
  (x â· xs) âá¶  [ y ] = (x â y) â· xs
  (x â· xs) âá¶  (y â· ys) = (x â y) â· (xs âá¶  ys)

  Îµá¶  : Listâº â ð â
  Îµá¶  = [ Îµ ]

  âá¶ -associative : (xs ys zs : Listâº â ð â) â (xs âá¶  (ys âá¶  zs)) â¡ ((xs âá¶  ys) âá¶  zs)
  âá¶ -associative [ x ] [ y ] [ z ] = ap [_] ð.associative
  âá¶ -associative [ x ] [ y ] (z â· zs) = ap (_â· zs) ð.associative
  âá¶ -associative [ x ] (y â· ys) [ z ] = ap (_â· ys) ð.associative
  âá¶ -associative [ x ] (y â· ys) (z â· zs) = ap (_â· (ys âá¶  zs)) ð.associative
  âá¶ -associative (x â· xs) [ y ] [ z ] = ap (_â· xs) ð.associative
  âá¶ -associative (x â· xs) [ y ] (z â· zs) = ap (_â· (xs âá¶  zs)) ð.associative
  âá¶ -associative (x â· xs) (y â· ys) [ z ] = ap (_â· (xs âá¶  ys)) ð.associative
  âá¶ -associative (x â· xs) (y â· ys) (z â· zs) = apâ _â·_ ð.associative (âá¶ -associative xs ys zs)

  âá¶ -idl : â (xs : Listâº â ð â) â (Îµá¶  âá¶  xs) â¡ xs
  âá¶ -idl [ x ] = ap [_] ð.idl
  âá¶ -idl (x â· xs) = ap (_â· xs) ð.idl

  âá¶ -idr : â (xs : Listâº â ð â) â (xs âá¶  Îµá¶ ) â¡ xs
  âá¶ -idr [ x ] = ap [_] ð.idr
  âá¶ -idr (x â· xs) = ap (_â· xs) ð.idr

  --------------------------------------------------------------------------------
  -- Algebra

  âá¶ -is-magma : is-magma _âá¶ _
  âá¶ -is-magma .has-is-set = Listâº-is-hlevel 0 â ð â-set

  âá¶ -is-semigroup : is-semigroup _âá¶ _
  âá¶ -is-semigroup .has-is-magma = âá¶ -is-magma
  âá¶ -is-semigroup .associative {x} {y} {z} = âá¶ -associative x y z

  âá¶ -is-monoid : is-monoid Îµá¶  _âá¶ _
  âá¶ -is-monoid .has-is-semigroup = âá¶ -is-semigroup
  âá¶ -is-monoid .idl {x} = âá¶ -idl x
  âá¶ -is-monoid .idr {x} = âá¶ -idr x

  --------------------------------------------------------------------------------
  -- Order

  data fractal[_<_] : Listâº â ð â â Listâº â ð â â Type (o â r) where
    single< : â {x y} â ð [ x < y ]áµ â fractal[ [ x ] < [ y ] ]
    head<   : â {x xs y ys} â ð [ x < y ]áµ â fractal[ x â· xs < y â· ys ]
    -- Annoying hack to work around --without-K
    tail<   : â {x xs y ys} â x â¡ y â fractal[ xs < ys ] â fractal[ x â· xs < y â· ys ]

  <á¶ -irrefl : â (xs : Listâº â ð â) â fractal[ xs < xs ] â â¥
  <á¶ -irrefl [ x ] (single< x<x) = ð.irrefl x<x
  <á¶ -irrefl (x â· xs) (head< x<x) = ð.irrefl x<x
  <á¶ -irrefl (x â· xs) (tail< p xs<xs) = <á¶ -irrefl xs xs<xs

  <á¶ -trans : â (xs ys zs : Listâº â ð â) â fractal[ xs < ys ] â fractal[ ys < zs ] â fractal[ xs < zs ]
  <á¶ -trans [ x ] [ y ] [ z ] (single< x<y) (single< y<z) = single< (ð.trans x<y y<z)
  <á¶ -trans (x â· xs) (y â· ys) (z â· zs) (head< x<y) (head< y<z) = head< (ð.trans x<y y<z)
  <á¶ -trans (x â· xs) (y â· ys) (z â· zs) (head< x<y) (tail< yâ¡z ys<zs) = head< (ð.â¡-transr x<y yâ¡z)
  <á¶ -trans (x â· xs) (y â· ys) (z â· zs) (tail< xâ¡y xs<ys) (head< y<z) = head< (ð.â¡-transl xâ¡y y<z)
  <á¶ -trans (x â· xs) (y â· ys) (z â· zs) (tail< xâ¡y xs<ys) (tail< yâ¡z ys<zs) = tail< (xâ¡y â yâ¡z) (<á¶ -trans xs ys zs xs<ys ys<zs)

  <á¶ -is-prop : â (xs ys : Listâº â ð â) â is-prop (fractal[ xs < ys ])
  <á¶ -is-prop [ x ] [ y ] (single< x<y) (single< x<y') = ap single< (ð.<-is-prop x<y x<y')
  <á¶ -is-prop (x â· xs) (y â· ys) (head< x<y) (head< x<y') = ap head< (ð.<-is-prop x<y x<y')
  <á¶ -is-prop (x â· xs) (y â· ys) (head< x<y) (tail< xâ¡y xs<ys) = absurd (ð.irrefl (ð.â¡-transl (sym xâ¡y) x<y))
  <á¶ -is-prop (x â· xs) (y â· ys) (tail< xâ¡y xs<ys) (head< x<y) = absurd (ð.irrefl (ð.â¡-transl (sym xâ¡y) x<y))
  <á¶ -is-prop (x â· xs) (y â· ys) (tail< xâ¡y xs<ys) (tail< xâ¡y' xs<ys') = apâ tail< (â ð â-set x y xâ¡y xâ¡y') (<á¶ -is-prop xs ys xs<ys xs<ys')

  <á¶ -is-strict-order : is-strict-order fractal[_<_]
  <á¶ -is-strict-order .is-strict-order.irrefl {x} = <á¶ -irrefl x
  <á¶ -is-strict-order .is-strict-order.trans {x} {y} {z} = <á¶ -trans x y z
  <á¶ -is-strict-order .is-strict-order.has-prop {x} {y} = <á¶ -is-prop x y

  --------------------------------------------------------------------------------
  -- Left Invariance

  âá¶ -left-invariant : â (xs ys zs : Listâº â ð â) â fractal[ ys < zs ] â fractal[ xs âá¶  ys < xs âá¶  zs ]
  âá¶ -left-invariant [ x ] [ y ] [ z ] (single< y<z) = single< (ð.left-invariant y<z)
  âá¶ -left-invariant [ x ] (y â· ys) (z â· zs) (head< y<z) = head< (ð.left-invariant y<z)
  âá¶ -left-invariant [ x ] (y â· ys) (z â· zs) (tail< p ys<zs) = tail< (ap (x â_) p) ys<zs
  âá¶ -left-invariant (x â· xs) [ y ] [ z ] (single< y<z) = head< (ð.left-invariant y<z)
  âá¶ -left-invariant (x â· xs) (y â· ys) (z â· zs) (head< y<z) = head< (ð.left-invariant y<z)
  âá¶ -left-invariant (x â· xs) (y â· ys) (z â· zs) (tail< p ys<zs) = tail< (ap (x â_) p) (âá¶ -left-invariant xs ys zs ys<zs)

  --------------------------------------------------------------------------------
  -- Displacement Algebra

  âá¶ -is-displacement-algebra : is-displacement-algebra (fractal[_<_]) Îµá¶  _âá¶ _
  âá¶ -is-displacement-algebra .is-displacement-algebra.has-monoid = âá¶ -is-monoid
  âá¶ -is-displacement-algebra .is-displacement-algebra.has-strict-order = <á¶ -is-strict-order
  âá¶ -is-displacement-algebra .is-displacement-algebra.left-invariant {x} {y} {z} = âá¶ -left-invariant x y z
