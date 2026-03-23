This directory contains the specifications and proofs of [the translated Gallina
code](../lib) of Haskell's `containers` library.

## Dependencies

Building the theories requires:

- **Coq 8.20**
- **MathComp 2.2.0+** (for `ssrnat`, `seq`, `eqtype`, and `HB.instance`/`hasDecEq.Build` in `HSUtil.v`)
- **base library** (`../../base/`) — must be built first
- **base-thy proofs** (`../../base-thy/`) — must be built first
- **containers lib** (`../lib/`) — the translated Gallina code, must be built first

### Build instructions

```bash
# 1. Build prerequisites (from the repository root)
(cd base; coq_makefile -f _CoqProject -o Makefile && make -j)
(cd base-thy; coq_makefile -f _CoqProject -o Makefile && make -j)
(cd examples/containers/lib; coq_makefile -f _CoqProject -o Makefile && make -j)

# 2. Build the theories
cd examples/containers/theories
coq_makefile -f _CoqProject -o Makefile
make -j
```

### Installing MathComp via opam

```bash
opam install coq-mathcomp-ssreflect   # installs ssreflect + hierarchy-builder
```

The minimum required version is 2.2.0. Earlier versions (including all of MathComp 1.x) lack the Hierarchy Builder API (`HB.instance`, `hasDecEq.Build`) used in `HSUtil.v`.

## Contents

We have formalized and proved a representative subset of three modules, namely,
`Data.Set`, `Data.IntSet`, and `Data.Map`. They can be found in:
* `SetProofs.v` for `Data.Set` (this includes theorems for operations,
  type class laws, and Coq's finite set theorems),
* `IntSetProofs.v` for `Data.IntSet` (this includes theorems for operations,
  type class laws, and Coq's finite set theorems),
* `IntSetPropertyProofs.v` for proofs that `Data.IntSet` satisfies the
  QuickCheck properties from the library's test suite,
* the `MapProofs` directory for `Data.Map` (formalizations for
  `Data.Map` is too big so we divided it into several files under one
  directory).

There is also a small subset of specifications and proofs for `Data.IntMap` in
`IntMapProofs.v`.

All the files follow the same naming convention for theorems. Most top-level
theorems will start with the operations they specify, with `_Desc` as their
suffixes. For example, the top-level theorem of `insert` operation is named
`insert_Desc`. A few operations do not have theorems in the form of `Desc`: they
are specified in terms of equality or iff relations with other terms. These
theorems also start with the names of the operations, with `_spec` or `_eq` as
their suffixes (for example, `member_spec` is the top-level theorem for the
`member` function of `Data.Set`).

Each file contains some comments explaining what has been formalized and
contains some instructions on how to navigate there. Formalizations for
`Data.Map` has its own README file [here](MapProofs/README.md).
