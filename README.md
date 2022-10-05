# `agda-mugen`

This is a formalization of the displacement algebras found in [mugen](https://github.com/RedPRL/mugen/), their properties, and part of meta-theoretic analysis.

## Formalized Results

### Displacement Algebras

| Displacements | Paper Section | Agda Module | OCaml Module(s) |
| :- | :- | :- | :- |
| Natural numbers | 3.3.1 | [Nat](src/Mugen/Algebra/Displacement/Nat.agda) | [Nat](https://redprl.org/mugen/mugen/Mugen/Shift/Nat) and [Nat](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Nat)
| Integers | 3.3.1 | [Int](src/Mugen/Algebra/Displacement/Int.agda) | [Int](https://redprl.org/mugen/mugen/Mugen/Shift/Int) and [Int](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Int)
| Non-positive integers | 3.3.1 | [NonPositive](src/Mugen/Algebra/Displacement/NonPositive.agda) | [NonPositive](https://redprl.org/mugen/mugen/Mugen/Shift/NonPositive) and [NonPositive](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/NonPositive)
| Constant displacements | 3.3.2 | [Constant](src/Mugen/Algebra/Displacement/Constant.agda) | [Constant](https://redprl.org/mugen/mugen/Mugen/Shift/Constant) and [Constant](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Constant)
| Binary products | 3.3.3 | [Product](src/Mugen/Algebra/Displacement/Product.agda) | [Product](https://redprl.org/mugen/mugen/Mugen/Shift/Product) and [Product](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Product)
| Lexicographic binary products | 3.3.4 | [Lexicographic](src/Mugen/Algebra/Displacement/Lexicographic.agda) | [Lexicographic](https://redprl.org/mugen/mugen/Mugen/Shift/Lexicographic) and [Lexicographic](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Lexicographic)
| Infinity products | 3.3.5 | [InfinityProduct](src/Mugen/Algebra/Displacement/InfinityProduct.agda) | _(not implementable)_
| Nearly constant infinity products | 3.3.5 | [NearlyConstant](src/Mugen/Algebra/Displacement/NearlyConstant.agda) | [NearlyConstant](https://redprl.org/mugen/mugen/Mugen/Shift/NearlyConstant) and [NearlyConstant](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/NearlyConstant)
| Infinity products with finite support | 3.3.5 | [FiniteSupport](src/Mugen/Algebra/Displacement/FiniteSupport.agda) | [FiniteSupport](https://redprl.org/mugen/mugen/Mugen/Shift/FiniteSupport) and [FiniteSupport](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/FiniteSupport)
| Prefix order | 3.3.6 | [Prefix](src/Mugen/Algebra/Displacement/Prefix.agda) | [Prefix](https://redprl.org/mugen/mugen/Mugen/Shift/Prefix) and [Prefix](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Prefix)
| Fractal displacements | 3.3.7 | [Fractal](src/Mugen/Algebra/Displacement/Fractal.agda) | [Fractal](https://redprl.org/mugen/mugen/Mugen/Shift/Fractal) and [Fractal](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Fractal)
| Opposite displacements | 3.3.8 | [Opposite](src/Mugen/Algebra/Displacement/Opposite.agda) | [Opposite](https://redprl.org/mugen/mugen/Mugen/Shift/Opposite) and [Opposite](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Opposite)
| Endomorphisms | 3.4 | [Endomorphism](src/Mugen/Algebra/Displacement/Endomorphism.agda) | _(not implementable)_

### Other Theorems

| Theorems | Paper Section | Agda Module |
| :- | :- | :- |
| Validity of McBride monads | 3.1 | [Mugen.Cat.HierarchyTheory](./src/Mugen/Cat/HierarchyTheory.agda)
| Embedding of endomorphisms | 3.4 | [Mugen.Cat.HierarchyTheory.Properties](./src/Mugen/Cat/HierarchyTheory/Properties.agda)

## Building

### Direct

1. Set up a working Haskell toolchain, for example using [ghcup](https://www.haskell.org/ghcup/).

2. Compile and install [Agda](https://github.com/agda/agda) at the commit `efa6fe4cc`. You will have to build Agda from the source.

3. Install [1Lab](https://github.com/plt-amy/1lab) and add the path to its `1lab.agda-lib` to `${AGDA_DIR}/libraries`. This formalization was checked against the commit `f5465e94` of the 1lab library.

4. Type check the formalization by running `make`.

### Docker Option 1

Run the following command to check formalization.

```sh
docker build -t agda-mugen .
docker run agda-mugen
```

### Docker Option 2

Run the following command to check formalization.
```sh
docker pull totbwf/agda-mugen
docker run totbwf/agda-mugen
```
