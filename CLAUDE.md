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

# Build a specific example (e.g., containers lib + theories)
make -C examples/containers
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

Four jobs: `build-haskell` (haskell:9.10.3 Docker), `test-coq-files` (mathcomp/mathcomp:2.5.0-coq-8.20 Docker), `tests` (haskell-actions + opam for Coq), `test-translation` (haskell:9.10.3 Docker, verifies base/ regeneration matches). Sets `LANG=C.utf8` globally for Unicode support.

**Container job gotcha**: Container jobs need `STACK_ROOT: /workspace/.stack` as a job-level env var because `/github/home/` is owned by root but the runner user differs. Cache paths must use `${{ env.STACK_ROOT }}` instead of `~/.stack`. The non-container `tests` job uses `~/.stack` normally.

## GHC Version Compatibility

Cross-version compatibility is managed via CPP macros in `src/include/ghc-compat.h`. Key macros: `NOEXT`/`NOEXTP` (for "Trees That Grow" extension fields), `GHC_910()`, `GHC_900()` (version-gated code blocks). When updating for a new GHC version, these macros and the wrappers in `src/lib/HsToCoq/Util/GHC/` are the primary adaptation points.

## GHC 9.10 Migration (ghc910-coq820 branch)

GHC 9.10 moved most `base` implementations to `ghc-internal`. Source files are now at `ghc-internal/src/GHC/Internal/...` instead of `base/*.hs`. The Makefile in `examples/base-src/` uses a symlink `ghc-internal -> ../ghc/ghc/libraries/ghc-internal` and `rename module` edits to map `GHC.Internal.*` names back to canonical output names.

### Modules that can't be regenerated
These must use old versions from git master with manual fixes:
- `Data/Functor/Classes` — GHC 9.10 added quantified superclass constraints to Eq2/Ord2 (`forall a. Eq a => Eq1 (f a)`) that Coq can't resolve in the CPS encoding

Previously broken modules now regenerable:
- `Data/Foldable`, `Data/Traversable`, `Data/Functor/Const`, `Data/Functor/Identity` — fixed via `DerivSkipInfo` filtering + parsed-AST standalone-deriving stripping + `skip method` default-binding filtering in `Class.hs`
- `Control/Category`, `Control/Arrow` — fixed by stripping invisible RuntimeRep args from `(->)` TyCon in Type.hs and flexible type matching in lookupInstance
- Identity and Traversable now fully auto-generated (edits handle coerce issues)
- `_CoqProject` ordering matters: Identity/Traversable must be listed early (EARLY_GHC_INTERNAL_MODULES in Makefile) to avoid Coq typeclass resolution stack overflow

### Deriving pipeline (GHC 9.10)
GHC's `load LoadAllTargets` processes standalone `deriving instance` declarations during typechecking — before `addDerivedInstances` runs. If any fail (e.g. types from skipped modules), `load` returns `Failed`. The fallback in `ProcessFiles.hs` strips all standalone deriving decls from the **parsed** AST, then typechecks, then uses `addDerivedInstances` to re-derive the ones we want.

### Locale for hs-to-coq
Generated `.v` files contain Unicode (e.g. `∘`). Set `LANG=C.utf8` before running hs-to-coq or the output will fail with encoding errors on systems with POSIX locale.

### Common edit patterns for GHC 9.10
- **`skip` vs `skip method`**: Never use `skip Mod.func` for class methods — use `skip method Mod.Class func` only. Using both causes "skipping a binding" errors.
- **`SigPat` in GHC 9.10**: `foldl'`/`foldr'`/`foldMap'` default implementations use `SigPat` which hs-to-coq doesn't support. Skip via `skip method`.
- **mconcat `foldl' (<>) mempty`**: GHC 9.10 generates this but it creates circular deps. Fix: `redefine` to use `foldr mappend mempty` + `order mempty mconcat`
- **`GHC.Prim.coerce` with abstract types**: Coq can't resolve `Coercible` for newtypes with abstract type vars. Fix: replace with explicit pattern matching
- **`rightSection`**: GHC 9.10 desugars `(op x)` to `rightSection op x`. Defined in `base/GHC/Prim.v`. Operators with invalid Coq chars (like `$`) are rendered as z-encoded names (e.g. `op_zd__`) instead of notation form. Proofs involving `rightSection` need `unfold GHC.Prim.rightSection` before `lia`
- **`foldMap'` in Foldable**: GHC 9.10 added this to the Foldable class. Old restored .v files need the field added manually

### Containers submodule
Containers is at v0.6.0.1, which has `foldl'` ambiguity with GHC 9.10 (Prelude now re-exports `Data.Foldable.foldl'`). The `.v` files in `examples/containers/lib/` were translated with an older GHC and are stable. Regeneration is skipped in CI. The Makefile's `clean` target preserves `.v` source files (only removes build artifacts); use `distclean` to remove everything.

### Coq 8.20 compatibility
- `Program Instance` needs `#[global]` prefix for cross-module visibility
- `Program Definition` with `#[global]` needs locality before `Program` (i.e., `#[global] Program Definition`, not `Program #[global] Definition`)
- Type and constructor cannot share the same name (e.g., `StateT`)
- `omega` tactic replaced by `lia`; `le_lt_n_Sm` removed (use `lia` instead)
- `intuition` solves more goals — proof bullet structures may need adjustment
- `f_solver` may solve different/more goals, changing remaining goal structure
- `auto` no longer solves `E.eq` reflexivity goals from OrderedType — use explicit `apply E.eq_refl`/`apply E.eq_sym`
- `zify` handles `Z.of_N (Z.to_N ...)` differently — use `try rewrite Z2N.id` instead of `rewrite Z2N.id`
- Section `Variable` hypotheses now generate side conditions in `rewrite` that weren't needed before
- `Require Import` inside sections may not export notations after section ends (e.g., `==>` from Morphisms)
- Names from `Coq.Lists.List` (like `filter`, `partition`) may shadow project names — qualify explicitly
- `Program Definition` obligation ordering may differ (e.g., fst before snd)
- Bound variable naming in goals may change (e.g., `bm0` → `bm`) — use explicit `with` clauses
- Typeclass resolution may not unfold definition chains (`Key→N→Word`) — add explicit instances

## Workflow

- Every time before you commit, you should also check if other modules have been broken due to this change. For example, check `examples/test` even if you have only been working on `examples/containers`.
- Commit to git at each milestone with `Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>`

