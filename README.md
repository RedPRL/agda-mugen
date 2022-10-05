# `agda-mugen`

This is a formalization of some of the displacement algebras found in [mugen](https://github.com/RedPRL/mugen/),
as well as an exploration of some theoretical properties of Hierarchy Theories.

In particular, we present a collection of examples of displacement algebras (See [`Mugen.Algebra.Displacement`](https://github.com/RedPRL/agda-mugen/tree/main/src/Mugen/Algebra/Displacement)),
and prove some additional properties (right-invariance, existence of bottoms, and joins).
We also show that displacement algebras induce monads on the category of strict orders
(See [`Mugen.Cat.HierarchyTheory`](https://github.com/RedPRL/agda-mugen/blob/main/src/Mugen/Cat/HierarchyTheory.agda))
Furthermore, we define the endomorphism displacement algebra (See [`Mugen.Algebra.Displacement.Endo`](https://github.com/RedPRL/agda-mugen/blob/main/src/Mugen/Algebra/Displacement/Endo.agda)),
and have formalized the first step towards showing that this is generates the "universal hierarchy theory" (See [`Mugen.Cat.HierarchyTheory.Properties`](https://github.com/RedPRL/agda-mugen/blob/main/src/Mugen/Cat/HierarchyTheory/Properties.agda))

## Mapping Table for Dispalcements

| Displacements | POPL Paper Section | Agda module | OCaml module(s) |
| :- | :- | :- | :- |
| Natural numbers | 3.3.1 | [Nat](src/Mugen/Algebra/Displacement/Nat.agda) | [Shift.Nat](https://redprl.org/mugen/mugen/Mugen/Shift/Nat) and [ShiftWithJoin.Nat](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Nat)
| Integers | 3.3.1 | [Int](src/Mugen/Algebra/Displacement/Int.agda) | [Shift.Int](https://redprl.org/mugen/mugen/Mugen/Shift/Int) and [ShiftWithJoin.Int](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Int)
| Non-positive integers | 3.3.1 | [NonPositive](src/Mugen/Algebra/Displacement/NonPositive.agda) | [Shift.NonPositive](https://redprl.org/mugen/mugen/Mugen/Shift/NonPositive) and [ShiftWithJoin.NonPositive](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/NonPositive)
| Constant displacements | 3.3.2 | [Constant](src/Mugen/Algebra/Displacement/Constant.agda) | [Shift.Constant](https://redprl.org/mugen/mugen/Mugen/Shift/Constant) and [ShiftWithJoin.Constant](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Constant)
| Binary products | 3.3.3 | [Product](src/Mugen/Algebra/Displacement/Product.agda) | [Shift.Product](https://redprl.org/mugen/mugen/Mugen/Shift/Product) and [ShiftWithJoin.Product](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Product)
| Lexicographic binary products | 3.3.4 | [Lexicographic](src/Mugen/Algebra/Displacement/Lexicographic.agda) | [Shift.Lexicographic](https://redprl.org/mugen/mugen/Mugen/Shift/Lexicographic) and [ShiftWithJoin.Lexicographic](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Lexicographic)
| Infinity products | 3.3.5 | [InfinityProduct](src/Mugen/Algebra/Displacement/InfinityProduct.agda) | _(not implementable)_
| Nearly constant infinity products | 3.3.5 | [NearlyConstant](src/Mugen/Algebra/Displacement/NearlyConstant.agda) | [Shift.NearlyConstant](https://redprl.org/mugen/mugen/Mugen/Shift/NearlyConstant) and [ShiftWithJoin.NearlyConstant](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/NearlyConstant)
| Infinity products with finite support | 3.3.5 | [FiniteSupport](src/Mugen/Algebra/Displacement/FiniteSupport.agda) | [Shift.FiniteSupport](https://redprl.org/mugen/mugen/Mugen/Shift/FiniteSupport) and [ShiftWithJoin.FiniteSupport](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/FiniteSupport)
| Prefix order | 3.3.6 | [Prefix](src/Mugen/Algebra/Displacement/Prefix.agda) | [Shift.Prefix](https://redprl.org/mugen/mugen/Mugen/Shift/Prefix) and [ShiftWithJoin.Prefix](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Prefix)
| Fractal displacements | 3.3.7 | [Fractal](src/Mugen/Algebra/Displacement/Fractal.agda) | [Shift.Fractal](https://redprl.org/mugen/mugen/Mugen/Shift/Fractal) and [ShiftWithJoin.Fractal](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Fractal)
| Opposite displacements | 3.3.8 | [Opposite](src/Mugen/Algebra/Displacement/Opposite.agda) | [Shift.Opposite](https://redprl.org/mugen/mugen/Mugen/Shift/Opposite) and [ShiftWithJoin.Opposite](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Opposite)
| Endomorphisms | 3.6 | [Endomorphism](src/Mugen/Algebra/Displacement/Endomorphism.agda) | _(not implementable)_

## Building

This formalization depends on the [1Lab](https://github.com/plt-amy/1lab), which
can be installed by cloning the repo, and then adding a single line to the `~/.agda/libraries`
that points to the path where you cloned the repo. This formalization was checked against commit `f5465e94`.

Furthermore, this formalization requires Agda 2.6.3, which can be obtained by installing from source.
Simply clone the [Agda](https://github.com/agda/agda) repository, and then run `cabal install` to install.
If you do not have a working Haskell toolchain, the best route is to use [ghcup](https://www.haskell.org/ghcup/).
This formalization was checked against `efa6fe4cc`.

## Docker

A `Dockerfile` is also provided that packages the required versions of `agda` and the `1lab`.
To run it, first build the image with `docker build -t agda-mugen .`. Once that completes, you
can then run `docker run agda-mugen`, which will check the formalization.
