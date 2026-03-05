
# hs-to-coq

![hs-to-coq](https://github.com/plclub/hs-to-coq/workflows/hs-to-coq/badge.svg?branch=ghc910-coq820)

Join our discussion on: [![Zulip](https://img.shields.io/badge/Zulip-chat-informational.svg)](https://coq.zulipchat.com/#narrow/stream/240767-hs-to-coq-devs.20.26.20users)

This repository contains a converter from Haskell code to equivalent
Coq code, as part of the [CoreSpec] component of the [DeepSpec]
project.

CPP'18 paper ["Total Haskell is Reasonable
Coq"](https://arxiv.org/abs/1711.09286) by Antal Spector-Zabusky,
Joachim Breitner, Christine Rizkallah, and Stephanie Weirich. This
paper describes the following examples:

  * [bag](examples/bag) Multiset implementation from GHC's implemention
  * [compiler](examples/compiler) Hutton's razor
  * [base-src](examples/base-src) The sources of the `base/` directory


ICFP'18 paper ["Ready, set, verify! applying hs-to-coq to real-world
Haskell code (experience
report)"](https://dl.acm.org/citation.cfm?id=3236784) by Joachim
Breitner, Antal Spector-Zabusky, Yao Li, Christine Rizkallah, John
Wiegley, and Stephanie Weirich.  This paper describes the verification
of the [containers](examples/containers) library.


[**Documentation for the `hs-to-coq` tool is
available!**](https://hs-to-coq.readthedocs.io/en/latest/)

# Installation

**Current target: GHC 9.10.3 and Coq 8.20** (branch `ghc910-coq820`)

## Compilation

The recommended way of building `hs-to-coq` is to use `stack`. If you have not
setup stack before, run:

    stack setup

To build `hs-to-coq`, then run

    stack build

## Building the `base` library

This repository comes with a version of (parts of the) Haskell base library
converted to Coq, which you will likely need if you want to verify Haskell
code.

You must have Coq 8.20 and ssreflect to build the base library. To
install these tools:

  1. `opam repo add coq-released https://coq.inria.fr/opam/released` (for
     SSReflect and MathComp)
  2. `opam update`
  3. `opam install coq.8.20.1 coq-mathcomp-ssreflect`

Once installed, you can build the base library with

    cd base && coq_makefile -f _CoqProject -o Makefile && make -j && cd ..

The directory `base-thy/` contains auxiliary definitions and lemmas, such as
lawful type-class instances. You can build these with

    cd base-thy && coq_makefile -f _CoqProject -o Makefile && make -j && cd ..

## Regenerating the `base` library

The `base/` directory contains a convenience copy of the generated Coq files.
To regenerate from Haskell source (requires the `ghc-internal` submodule):

    git submodule update --init --recursive
    make -C examples/base-src clean
    make -C examples/base-src

This runs hs-to-coq on the GHC 9.10 base/ghc-internal sources and
compiles the resulting Coq files. Set `LANG=C.utf8` if you encounter
encoding errors (generated files contain Unicode characters like `∘`).

# Using the tool

To use the tool, run it (using `stack`), passing the Haskell file to be
translated and an output directory to write to:

    stack exec hs-to-coq -- -o output-directory/ Input/File.hs

Very likely you want to make use of the `base/` library. In that case, make
sure you pass `-e base/edits`.

Have a look at the example directories, e.g. `examples/successors`, for a
convenient `Makefile` based setup.

## Edits

The `edits` file contains directives to `hs-to-coq` for ignoring or
transforming some Haskell constructs into proper Coq.

For example, it is common in Haskell to have the following code:

```
module Foo where
...
newtype SomeType = SomeType { someFiled :: Integer }
```

Coq has a single namespace for types and values hence the type name
will conflict with constructor name. One can pass `-e edit` file
containing custom directives to ensure correctness of generated code
with the following directive:

```
rename value Foo.SomeType = Foo.MkSomeType
```


See the [manual](https://hs-to-coq.readthedocs.io/en/latest/) for documentation
for the edits files.


# Other directories

* The `examples/` directories contains a number of example translation and
  verification projects, including

  * [intervals](examples/intervals) A simple example described in this
    [blog post](https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it).

  * [containers](examples/containers) Modules from the `containers` library,
	including `Data.Set` and `Data.IntSet`
  * [bag](examples/bag) Multiset implementation from GHC's implemention
  * [successors](examples/successors) Successors Monad
  * [compiler](examples/compiler) Hutton's razor
  * [quicksort](examples/quicksort) Quicksort
  * [rle](examples/rle) Run-length encoding
  * [coinduction](examples/coinduction) Translating infinite data structures
  * [dlist](examples/dlist) Difference lists
  * [lambda](examples/lambda) Lambda calculus
  * [simple](examples/simple) Simple example
  * [base-src](examples/base-src) The sources of the `base/` directory
  * [tests](examples/tests) Simple unit-tests
  * [base-tests](examples/base-tests) Unit-tests that require `base/`


  Some examples use git submodules, so run

      git submodule update --init --recursive

  once.

* `structural-isomorphism-plugin`: (In progress.)  A GHC plugin that connects
   the re-extracted converted code back into GHC, allowing us to run Haskell
   programs against verified/verifiable code.  Currently does not work.


[CoreSpec]: https://deepspec.org/entry/Project/Haskell+CoreSpec
[DeepSpec]: http://www.deepspec.org/
