# `agda-mugen`

This is a formalization of some of the displacement algebras found in [mugen](https://github.com/RedPRL/mugen/),
as well as an exploration of some theoretical properties of Heirarchy Theories.

In particular, we present a collection of examples of displacement algebras (See [`Mugen.Algebra.Displacement`](https://github.com/RedPRL/agda-mugen/tree/main/src/Mugen/Algebra/Displacement)),
and prove some additional properties (right-invariance, existence of bottons, and joins).
We also show that displacement algebras induce monads on the category of strict orders
(See [`Mugen.Cat.HeirarchyTheory`](https://github.com/RedPRL/agda-mugen/blob/main/src/Mugen/Cat/HierarchyTheory.agda))
Furthermore, we define the endomorphism displacement algebra (See [`Mugen.Algebra.Displacement.Endo`](https://github.com/RedPRL/agda-mugen/blob/main/src/Mugen/Algebra/Displacement/Endo.agda)),
and have formalized the first step towards showing that this is generates the "universal heirarchy theory" (See [`Mugen.Cat.HeirarchyTheory.Properties`](https://github.com/RedPRL/agda-mugen/blob/main/src/Mugen/Cat/HierarchyTheory/Properties.agda))


## Building

This formalization depends on the [1Lab](https://github.com/plt-amy/1lab), which
can be installed by cloning the repo, and then adding a single line to the `~/.agda/libraries`
that points to the path where you cloned the repo. This formalization was checked against commit `9e1eb4cd`.

Furthermore, this formalization requires Agda 2.6.3, which can be obtained by installing from source.
Simply clone the [Agda](https://github.com/agda/agda) repository, and then run `cabal install` to install.
If you do not have a working Haskell toolchain, the best route is to use [ghcup](https://www.haskell.org/ghcup/).
This formalization was checked against `3044510c8`.

## Docker

A `Dockerfile` is also provided that packages the required versions of `agda` and the `1lab`.
To run it, first build the image with `docker build -t agda-mugen .`. Once that completes, you
can then run `docker run agda-mugen`, which will check the formalization.
