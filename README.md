# ♾ mugen 無限 in Agda

This is a formalization of the displacement algebras, their properties, and part of meta-theoretic analysis found in our POPL 2023 paper [“An Order-Theoretic Analysis of Universe Polymorphism”.](https://favonia.org/files/mugen.pdf) The accompanying OCaml implementation is at <https://github.com/RedPRL/mugen/>.

## Mechanized Results

### Displacement Algebras

| Displacements                         | Paper Section | Agda Module                                                            | OCaml Module(s)                                                                                                                                                     |
| :------------------------------------ | :------------ | :--------------------------------------------------------------------- | :------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Natural numbers                       | 3.3.1         | [Nat](src/Mugen/Algebra/Displacement/Nat.agda)                         | [Nat](https://redprl.org/mugen/mugen/Mugen/Shift/Nat) and [Nat](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Nat)                                             |
| Integers                              | 3.3.1         | [Int](src/Mugen/Algebra/Displacement/Int.agda)                         | [Int](https://redprl.org/mugen/mugen/Mugen/Shift/Int) and [Int](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Int)                                             |
| Non-positive integers                 | 3.3.1         | [NonPositive](src/Mugen/Algebra/Displacement/NonPositive.agda)         | [NonPositive](https://redprl.org/mugen/mugen/Mugen/Shift/NonPositive) and [NonPositive](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/NonPositive)             |
| Constant displacements                | 3.3.2         | [Constant](src/Mugen/Algebra/Displacement/Constant.agda)               | [Constant](https://redprl.org/mugen/mugen/Mugen/Shift/Constant)                                                                                                     |
| Binary products                       | 3.3.3         | [Product](src/Mugen/Algebra/Displacement/Product.agda)                 | [Product](https://redprl.org/mugen/mugen/Mugen/Shift/Product) and [Product](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Product)                             |
| Lexicographic binary products         | 3.3.4         | [Lexicographic](src/Mugen/Algebra/Displacement/Lexicographic.agda)     | [Lexicographic](https://redprl.org/mugen/mugen/Mugen/Shift/Lexicographic) and [Lexicographic](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Lexicographic)     |
| Infinite products                     | 3.3.5         | [InfiniteProduct](src/Mugen/Algebra/Displacement/InfiniteProduct.agda) | _(not implementable)_                                                                                                                                               |
| Nearly constant infinite products     | 3.3.5         | [NearlyConstant](src/Mugen/Algebra/Displacement/NearlyConstant.agda)   | [NearlyConstant](https://redprl.org/mugen/mugen/Mugen/Shift/NearlyConstant) and [NearlyConstant](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/NearlyConstant) |
| Infinite products with finite support | 3.3.5         | [FiniteSupport](src/Mugen/Algebra/Displacement/FiniteSupport.agda)     | [FiniteSupport](https://redprl.org/mugen/mugen/Mugen/Shift/FiniteSupport) and [FiniteSupport](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/FiniteSupport)     |
| Prefix order                          | 3.3.6         | [Prefix](src/Mugen/Algebra/Displacement/Prefix.agda)                   | [Prefix](https://redprl.org/mugen/mugen/Mugen/Shift/Prefix)                                                                                                         |
| Fractal displacements                 | 3.3.7         | [Fractal](src/Mugen/Algebra/Displacement/Fractal.agda)                 | [Fractal](https://redprl.org/mugen/mugen/Mugen/Shift/Fractal)                                                                                                       |
| Opposite displacements                | 3.3.8         | [Opposite](src/Mugen/Algebra/Displacement/Opposite.agda)               | [Opposite](https://redprl.org/mugen/mugen/Mugen/Shift/Opposite)                                                                                                     |
| Endomorphisms                         | 3.4           | [Endomorphism](src/Mugen/Algebra/Displacement/Endomorphism.agda)       | _(not implementable)_                                                                                                                                               |

### Other Theorems

| Theorems                   | Paper Section | Agda Module                                                                             |
| :------------------------- | :------------ | :-------------------------------------------------------------------------------------- |
| Validity of McBride monads | 3.1           | [Mugen.Cat.HierarchyTheory](./src/Mugen/Cat/HierarchyTheory.agda)                       |
| Embedding of endomorphisms | 3.4           | [Mugen.Cat.HierarchyTheory.Properties](./src/Mugen/Cat/HierarchyTheory/Properties.agda) |

## Building

### Docker

Run the following command to check formalization.

```sh
docker build -t agda-mugen:edge .
docker run agda-mugen:edge
```

### Direct

1. Set up a working Haskell toolchain, for example using [ghcup](https://www.haskell.org/ghcup/).

2. Compile and install [Agda](https://github.com/agda/agda) at the commit `5c8116227e2d9120267aed43f0e545a65d9c2fe2`. You will have to build Agda from the source.

3. Install [1Lab](https://github.com/plt-amy/1lab) and add the path to its `1lab.agda-lib` to `${AGDA_DIR}/libraries`. This formalization was checked against the commit `ac6f81089a261e9c0d2ce3ede37a4a09764cb2ad` of the 1lab library.

4. Type check the formalization by running `make`.
