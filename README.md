<!--- vim: set nowrap: --->

# ♾ mugen 無限 in Agda

This is a formalization of the displacement algebras, their properties, and part of meta-theoretic analysis found in our POPL 2023 paper [“An Order-Theoretic Analysis of Universe Polymorphism”.](https://favonia.org/files/mugen.pdf) The accompanying OCaml implementation is at <https://github.com/RedPRL/mugen/>.

🚧 This repository is under major rewrites and cleanups. See version 0.1.0 for the code that matches the POPL 2023 paper.

## Mechanized Results

### Displacement Algebras

🚧 The links are currently broken.

| Displacements                         | Paper Section    | Agda Module                                                                    | OCaml Module(s)                                                                                                                                                     |
| :------------------------------------ | :--------------- | :----------------------------------------------------------------------------- | :------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Natural numbers                       | 3.3.1            | [Nat](src/Mugen/Algebra/Displacement/Instances/Nat.agda)                       | [Nat](https://redprl.org/mugen/mugen/Mugen/Shift/Nat) and [Nat](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Nat)                                             |
| Integers                              | 3.3.1            | [Int](src/Mugen/Algebra/Displacement/Instances/Int.agda)                       | [Int](https://redprl.org/mugen/mugen/Mugen/Shift/Int) and [Int](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Int)                                             |
| Non-positive integers                 | 3.3.1            | [NonPositive](src/Mugen/Algebra/Displacement/Instances/NonPositive.agda)       | [NonPositive](https://redprl.org/mugen/mugen/Mugen/Shift/NonPositive) and [NonPositive](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/NonPositive)             |
| Constant displacements                | 3.3.2            | [Constant](src/Mugen/Algebra/Displacement/Instances/Constant.agda)             | [Constant](https://redprl.org/mugen/mugen/Mugen/Shift/Constant)                                                                                                     |
| Binary products                       | 3.3.3            | [Product](src/Mugen/Algebra/Displacement/Instances/Product.agda)               | [Product](https://redprl.org/mugen/mugen/Mugen/Shift/Product) and [Product](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Product)                             |
| Lexicographic binary products         | 3.3.4            | [Lexicographic](src/Mugen/Algebra/Displacement/Instances/Lexicographic.agda)   | [Lexicographic](https://redprl.org/mugen/mugen/Mugen/Shift/Lexicographic) and [Lexicographic](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/Lexicographic)     |
| Indexed products                      | 3.3.5            | [IndexedProduct](src/Mugen/Algebra/Displacement/Instances/IndexedProduct.agda) | _(not implementable)_                                                                                                                                               |
| Nearly constant infinite products     | 3.3.5            | [NearlyConstant](src/Mugen/Algebra/Displacement/Instances/NearlyConstant.agda) | [NearlyConstant](https://redprl.org/mugen/mugen/Mugen/Shift/NearlyConstant) and [NearlyConstant](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/NearlyConstant) |
| Infinite products with finite support | 3.3.5            | [FiniteSupport](src/Mugen/Algebra/Displacement/Instances/FiniteSupport.agda)   | [FiniteSupport](https://redprl.org/mugen/mugen/Mugen/Shift/FiniteSupport) and [FiniteSupport](https://redprl.org/mugen/mugen/Mugen/ShiftWithJoin/FiniteSupport)     |
| Prefix order                          | 3.3.6            | [Prefix](src/Mugen/Algebra/Displacement/Instances/Prefix.agda)                 | [Prefix](https://redprl.org/mugen/mugen/Mugen/Shift/Prefix)                                                                                                         |
| Fractal displacements                 | 3.3.7            | [Fractal](src/Mugen/Algebra/Displacement/Instances/Fractal.agda)               | [Fractal](https://redprl.org/mugen/mugen/Mugen/Shift/Fractal)                                                                                                       |
| Opposite displacements                | 3.3.8            | [Opposite](src/Mugen/Algebra/Displacement/Instances/Opposite.agda)             | [Opposite](https://redprl.org/mugen/mugen/Mugen/Shift/Opposite)                                                                                                     |
| Weird fractal displacements           | 3.3.9 (JFP only) | [WeirdFractal](src/Mugen/Algebra/Displacement/Instances/WeirdFractal.agda)     | [Fractal](https://redprl.org/mugen/mugen/Mugen/Shift/Fractal)                                                                                                       |
| Endomorphisms                         | 3.4 (Lemma 3.7)  | [Endomorphism](src/Mugen/Algebra/Displacement/Instances/Endomorphism.agda)     | _(not implementable)_                                                                                                                                               |

### Other Theorems

| Theorems                              | Paper Section      | Agda Module                                                                                      |
| :------------------------------------ | :----------------- | :----------------------------------------------------------------------------------------------- |
| Traditional level polymorphism        | 2.2                | [Traditional](./src/Mugen/Cat/HierarchyTheory/Traditional.agda)                                  |
| Validity of McBride monads            | 3.1                | [McBride](./src/Mugen/Cat/HierarchyTheory/McBride.agda)                                          |
| Embedding of endomorphisms            | 3.4 (Lemma 3.8)    | [EndomorphismEmbedding](./src/Mugen/Cat/HierarchyTheory/Universality/EndomorphismEmbedding.agda) |
| Embedding of small hierarchy theories | 3.4 (Lemma 3.9)    | [SubcategoryEmbedding](./src/Mugen/Cat/HierarchyTheory/Universality/SubcategoryEmbedding.agda)   |
| Universality of McBride monads        | 3.4 (Theorem 3.10) | [Universality](./src/Mugen/Cat/HierarchyTheory/Universality.agda)                                |

## Building

Run the following command to check formalization.

```sh
docker build -t agda-mugen:edge .
docker run agda-mugen:edge
```
