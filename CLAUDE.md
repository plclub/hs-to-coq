# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**hs-to-coq** converts Haskell source code to Coq (Gallina) using the GHC API. It is part of the DeepSpec/CoreSpec project. The tool parses Haskell via GHC, applies user-specified "edits" to guide the translation, and pretty-prints valid Coq output.

- **Current target**: GHC 9.10.3, Coq 8.20 (branch `ghc910-coq820`)
- **Languages**: Haskell (the tool, ~14K LOC in `src/`), Coq (generated output and proofs)

## Build Commands

```bash
# Build the hs-to-coq Haskell executable
stack build

# Run hs-to-coq on a Haskell file
stack exec hs-to-coq -- -e edits -o output/ Input.hs

# Build Coq base library (must build before tests)
cd base && coq_makefile -f _CoqProject -o Makefile && make -j

# Build base-thy proofs (depends on base)
cd base-thy && coq_makefile -f _CoqProject -o Makefile && make -j

# Build everything (base + base-thy + containers)
make

# Re-generate base/ from Haskell sources
make -C examples/base-src vfiles

# Run unit tests (translates .hs → .v, then type-checks with coqc)
make -C examples/tests

# Run base-dependent tests
make -C examples/base-tests

# Run all examples (full bootstrap)
cd examples && ./boot.sh

# Build a specific example (e.g., containers)
make -C examples/containers/lib
```

Use relative path instead of absolute path when `cd` to a directory.

## Architecture

### Translation Pipeline

1. **Parse & typecheck** Haskell via GHC API (`src/lib/HsToCoq/ProcessFiles.hs`)
2. **Load edits** from `.edits` files (`src/lib/HsToCoq/Edits/Parser.y`, `Types.hs`)
3. **Convert** GHC AST → Coq Gallina AST (`src/lib/HsToCoq/ConvertHaskell/`)
4. **Pretty-print** Gallina to `.v` files (`src/lib/HsToCoq/Coq/Pretty.hs`)
5. **Output** `.h2ci` interface files for cross-module translation

### Key Source Directories

- `src/lib/HsToCoq/Coq/Gallina.hs` — Coq AST data types (Term, Sentence, Definition, Inductive, etc.)
- `src/lib/HsToCoq/Coq/Pretty.hs` — Pretty-printer rendering Gallina AST as Coq source
- `src/lib/HsToCoq/ConvertHaskell/` — Core conversion engine:
  - `Expr.hs` — Expression conversion (largest file, ~1600 lines)
  - `Module.hs` — Whole-module conversion
  - `Monad.hs` — Conversion monad carrying edits/renamings/state
  - `Declarations/` — Data types, classes, instances, type synonyms
  - `HsType.hs`, `Pattern.hs`, `Variables.hs` — Type/pattern/variable conversion
- `src/lib/HsToCoq/Edits/` — Edit DSL parser and types
- `src/lib/HsToCoq/CLI.hs` — Command-line interface and file processing orchestration
- `src/include/ghc-compat.h` — CPP macros for GHC version compatibility (8.4–9.10)
- `src/lib/HsToCoq/Util/GHC/` — GHC API compatibility wrappers

### The Edits System

Edits files are a plain-text DSL that guides translation of constructs that don't directly map to Coq. Key directives: `skip`, `rename`, `rewrite`, `redefine`, `add`, `order`, `termination`, `coinductive`, `axiomatize`, `manual notation`. Full documentation in `doc/source/edits.rst`.

Edits are organized per-module:
```
module-edits/<Module>/<Path>/edits       # per-module edits
module-edits/<Module>/<Path>/preamble.v  # Coq code prepended to output
module-edits/<Module>/<Path>/midamble.v  # Coq code inserted mid-file
```

### Output Directories

- `base/` — **Generated** Coq base library. **Do not edit directly** — regenerate from `examples/base-src/` instead.
- `base-thy/` — Hand-written proofs and lawful typeclass instances for `base/`
- `examples/` — Translation examples; each has `Makefile`, `edits`, `module-edits/`, `lib/` (output), `theories/` (proofs)

### Build Plumbing

- `common.mk` — Included by all example Makefiles; defines `HS_TO_COQ` variable (resolves to `stack exec hs-to-coq --`)
- Each Coq directory uses `_CoqProject` + `coq_makefile` to generate its Makefile
- `.h2ci` files store interface information for cross-module translation

## Test Structure

- `examples/tests/` — Unit tests: each `.hs` file is translated to `.v` and type-checked with `coqc`. Tests categorized as `PASS`, `TODO_PASS` (known failures), `TODO_TRANSLATE`.
- `examples/base-tests/` — Tests requiring the `base/` Coq library to be built first.
- Test-specific edits/preambles go in `examples/tests/<TestName>/edits` and `<TestName>/preamble.v`.

## CI (`.github/workflows/hs-to-coq.yml`)

Four jobs: `build-haskell` (Stack + GHC 9.10.3), `test-coq-files` (Coq 8.20 Docker), `tests` (unit + example tests), `test-translation` (verifies generated `.v` files match repo convenience copies via `git diff-index`).

## GHC Version Compatibility

Cross-version compatibility is managed via CPP macros in `src/include/ghc-compat.h`. Key macros: `NOEXT`/`NOEXTP` (for "Trees That Grow" extension fields), `GHC_910()`, `GHC_900()` (version-gated code blocks). When updating for a new GHC version, these macros and the wrappers in `src/lib/HsToCoq/Util/GHC/` are the primary adaptation points.

## GHC 9.10 Migration (ghc910-coq820 branch)

GHC 9.10 moved most `base` implementations to `ghc-internal`. Source files are now at `ghc-internal/src/GHC/Internal/...` instead of `base/*.hs`. The Makefile in `examples/base-src/` uses a symlink `ghc-internal -> ../ghc/ghc/libraries/ghc-internal` and `rename module` edits to map `GHC.Internal.*` names back to canonical output names.

### Modules that can't be regenerated
These must use old versions from git master with manual fixes:
- `Control/Category`, `Control/Arrow` — Category__arrow fails with dummy unit-id
- `Data/Foldable`, `Data/Traversable` — deriving issues with Generics types
- `Data/Functor/Const`, `Data/Functor/Identity` — deriving issues

### Common edit patterns for GHC 9.10
- **mconcat `foldl' (<>) mempty`**: GHC 9.10 generates this but it creates circular deps. Fix: `redefine` to use `foldr mappend mempty` + `order mempty mconcat`
- **`GHC.Prim.coerce` with abstract types**: Coq can't resolve `Coercible` for newtypes with abstract type vars. Fix: replace with explicit pattern matching
- **`rightSection`**: GHC 9.10 desugars `(op x)` to `rightSection op x`. Defined in `base/GHC/Prim.v`
- **`foldMap'` in Foldable**: GHC 9.10 added this to the Foldable class. Old restored .v files need the field added manually

### Coq 8.20 compatibility
- `Program Instance` needs `#[global]` prefix for cross-module visibility
- Type and constructor cannot share the same name (e.g., `StateT`)
- `omega` tactic replaced by `lia`

