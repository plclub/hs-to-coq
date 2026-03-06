This directory contains the Coq representation of Haskell's `containers`
library, as well as our specifications and proofs.

Our ICFP'18 paper ["Ready, set, verify! applying hs-to-coq to real-world Haskell
code (experience report)"](https://dl.acm.org/citation.cfm?id=3236784) and its
[extended version](https://arxiv.org/abs/1803.06960) describe the verification
of this library.

## Dependencies

Building requires:

- **Coq 8.20**
- **MathComp 2.2.0+** (for ssreflect and Hierarchy Builder; install via `opam install coq-mathcomp-ssreflect`)
- **base library** (`../../base/`) — must be built first
- **base-thy proofs** (`../../base-thy/`) — must be built first

## Contents

The most important components are in the `lib` and `theories` directories:

* `lib/` — Pre-translated Coq representation of Haskell's `containers` library
  (v0.6.0.1). These `.v` files were translated with an older GHC and are stable;
  they are **not regenerated** from source in the current build.
* `theories/` — Specifications and proofs for the `containers` library. See
  [theories/README.md](theories/README.md) for details on what has been verified.

Other notable components:

* `edits` and `module-edits/` — Edit directives that guided the translation
  (organized to mirror the `lib/` directory structure).
* `manual/` — Manually translated modules.
* `hs-spec/` — Properties translated from Haskell QuickCheck tests.
* `extraction/` — Extraction of the Coq translation back to Haskell.

## Build instructions

```bash
# 1. Build prerequisites (from the repository root)
(cd base; coq_makefile -f _CoqProject -o Makefile && make -j)
(cd base-thy; coq_makefile -f _CoqProject -o Makefile && make -j)

# 2. Build containers lib
(cd examples/containers/lib; coq_makefile -f _CoqProject -o Makefile && make -j)

# 3. Build containers theories (proofs)
(cd examples/containers/theories; coq_makefile -f _CoqProject -o Makefile && make -j)
```

Alternatively, run `boot.sh` in the [examples](../) directory to build
everything (base, containers, and all other examples). You do not need to
compile the `hs-to-coq` tool to build the Coq files.

## Regenerating lib/ (advanced)

The `.v` files in `lib/` are a convenience copy. Regeneration from Haskell
source requires the `hs-to-coq` tool (see [build instructions](../../README.md)).
Note that the containers v0.6.0.1 source has a `foldl'` ambiguity with GHC 9.10,
so regeneration is currently not supported with the latest GHC.
