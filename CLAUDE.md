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
make -C examples/containers          # lib + theories
make -C examples/containers/lib      # just the generated library
make -C examples/containers/theories # just the proofs (depends on lib)
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

**Container job gotcha**: Container jobs use `--allow-different-user` for stack commands (ownership mismatch between host-mounted workspace and container user). For docker-coq-action, use `before_script` with `sudo chown -R coq:coq .` (not `custom_script`, which bypasses permission setup). `common.mk` already includes `--allow-different-user` in the `HS_TO_COQ` variable.

**test-translation job**: Uses `git submodule update --init examples/ghc/ghc` (not `submodules: recursive`) — GHC has ~20 nested submodules that are not needed.

**CI cache key**: Must include `src/**` in `hashFiles` — otherwise source changes don't invalidate the cache, and stale binaries persist in `.stack-work`.

**Unicode encoding**: `src/exe/Main.hs` calls `setLocaleEncoding utf8` at startup so all file I/O uses UTF-8 regardless of system locale. Edits/midamble/preamble files may contain Unicode (e.g., `∘` in Coq identifiers). To test locally without UTF-8 locale: `LANG=C make -C examples/base-src clean && make vfiles`. Avoid Unicode in comments (smart quotes etc.) — use ASCII equivalents.

## GHC Version Compatibility

Cross-version compatibility is managed via CPP macros in `src/include/ghc-compat.h`. Key macros: `NOEXT`/`NOEXTP` (for "Trees That Grow" extension fields), `GHC_910()`, `GHC_900()` (version-gated code blocks). When updating for a new GHC version, these macros and the wrappers in `src/lib/HsToCoq/Util/GHC/` are the primary adaptation points.

## GHC 9.10 Migration (ghc910-coq820 branch)

GHC 9.10 moved most `base` implementations to `ghc-internal`. Source files are now at `ghc-internal/src/GHC/Internal/...` instead of `base/*.hs`. The Makefile in `examples/base-src/` uses a symlink `ghc-internal -> ../ghc/ghc/libraries/ghc-internal` and `rename module` edits to map `GHC.Internal.*` names back to canonical output names.

### Modules that can't be regenerated
These must use old versions from git master with manual fixes:
- `Data/Functor/Classes` — hs-to-coq generates valid output, but Coq can't compile it: GHC 9.10 added quantified superclass constraints to Eq2/Ord2 (`forall a. Eq a => Eq1 (f a)`) that Coq can't resolve in the CPS encoding. The manual version has the same compilation failure. Nothing downstream imports Eq2/Ord2 so this is tolerated.

Previously broken modules now regenerable:
- `Data/Foldable`, `Data/Traversable`, `Data/Functor/Const`, `Data/Functor/Identity` — fixed via `DerivSkipInfo` filtering + parsed-AST standalone-deriving stripping + `skip method` default-binding filtering in `Class.hs`
- `Control/Category`, `Control/Arrow` — fixed by stripping invisible RuntimeRep args from `(->)` TyCon in Type.hs and flexible type matching in lookupInstance
- **`(->)` TyCon in GHC 9.10**: `FunTyCon` reports 0 `tyConBinders` (unlike regular TyCons). RuntimeRep args appear as regular type args. `Type.hs` handles this by detecting `GHC.Prim.arrow` with null binders and passing empty args to `convertTyConApp`. `lookupInstance` uses `termHead` for flexible matching (e.g., `arrow` matches `arrow LiftedRep LiftedRep`).
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

### Edits system gotchas
- **`skip` overrides `redefine`**: In `definitionTask` (Monad.hs), `skip` is checked first. Remove `skip` directives before adding `redefine` for the same function.
- **`redefine` type annotations**: The edits parser doesn't support `*` in product types or `%type` scope annotations. Omit the type signature (use `:=` directly) to work around parse errors.
- **`order` with `redefine`**: When `redefine` introduces definition dependencies, add explicit `order` directives to ensure correct output ordering.
- **Parser extensions (ghc910-coq820)**: `if/then/else`, `#n` hash-number literals, and `let fix ... in` are supported in `redefine` bodies (added in Lexer.hs/Parser.y).

### GHC example (examples/ghc/)
Translated from GHC 9.10.3. All lib/*.v regenerated and compile. All 28 theories/*.v files compile (many proofs Admitted). Key GHC 9.10 changes affecting theories:
- `Alt` type: tuple → `Mk_Alt` constructor. Intro patterns change from `[[dc pats] rhs]` to `[dc pats rhs]`.
- `Mk_Id` has 7 fields (added `varMult : Mult` as 4th field). Pattern matches need extra wildcard.
- `realUnique` type: `N` → `Unique`. Breaks proofs using `N.eqb_neq`, `N.compare_refl`.
- `lookupIdSubst`: no longer takes `String` doc parameter.
- `mkVarApps`: uses `foldl'` not `foldl`. Use `hs_coq_foldl'_list`.
- State monad: bare function type (`s -> (a * s)`) not newtype wrapper. `StateLogic.v` rewritten.
- `substExpr`, `cseExpr`, `cseBind`, `try_for_cse`: axiomatized. Computation proofs Admitted.
- GoDom strict positivity: use `alt_rhs` projection function, not pattern-match lambda.
- `Var` has single constructor (`Mk_Id` only, no `TyVar`).
- `cse_bind` has 5 args (added `env_rhs` parameter).
- Makefile uses explicit GHC 9.10 path mappings (e.g., `SRCPATH_Var = ghc/compiler/GHC/Types/Var.hs`).

### Containers submodule
Containers is at v0.7. The `.v` files in `examples/containers/lib/` were translated with an older GHC and are stable. Regeneration is tested in CI. The Makefile's `clean` target preserves `.v` source files (only removes build artifacts); use `distclean` to remove everything. IntSet `split`/`splitMember`, Set and Map `fromDistinctAscList`/`fromDistinctDescList`/`fromAscList`/`fromDescList` all use native v0.7 definitions with rewritten proofs. Map `fromList` proofs are `Admitted` due to Coq 8.20 `Program Fixpoint` obligation structure changes (pre-existing issue). `hs-spec/IntSetProperties.v` is auto-generated from v0.7 `intset-properties.hs` (`tasty-quickcheck`/`tasty-hunit` added to cabal deps). The manual `Test/QuickCheck/Property.v` provides z-encoded operator aliases (`op_zizazazi__` etc.) for auto-generated code.

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
- `setoid_rewrite` under binders may fail with `UNDEFINED EVARS` — replace with explicit `replace`+`funext` or direct monad law rewrites
- `Foldable__list_foldMap` is now `mconcat ∘ map` (not direct `foldr`) — proofs unfolding Foldable for lists need different unfolding chains
- `eval unfold f` in sections with implicit args: use `let x := constr:(@f explicit_args) in let rhs := eval unfold f in x` — plain `eval unfold f in f` can't infer implicit params
- `f_equal` is more aggressive — may fully solve goals that previously required `extensionality` or further tactics, causing "No such goal" errors on dead proof code
- `Program Fixpoint ... := _.` with `Next Obligation.`: obligations may have all variables pre-introduced (no products to `intros`). The CPS pattern `intros X HX. apply HX. clear HX.` needs replacing with direct `apply HK` using already-in-context hypotheses. Use `match goal with` to find and rename hypotheses robustly.
- `clear -H1 H2` in sections: only keeps named hypotheses and their transitive dependencies. Section variables like `HEqLaws`/`HOrdLaws` are cleared if no kept hypothesis depends on them. This breaks tactics like `order e` that need them. Fix: `clear -H1 H2 HEqLaws HOrdLaws`.

## Workflow

- Keep a record (as a markdown file) of every time the user intervene
- Every time before you commit, you should also check if other modules have been broken due to this change. For example, check `examples/test` even if you have only been working on `examples/containers`.
- After significant functional changes (e.g., replacing `redefine` with native implementations), update README files, CLAUDE.md, and any plan documents to reflect the new state before committing.
- Commit to git at each milestone with `Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>`

