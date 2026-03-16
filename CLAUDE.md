# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**hs-to-coq** converts Haskell source code to Coq (Gallina) using the GHC API. It is part of the DeepSpec/CoreSpec project. The tool parses Haskell via GHC, applies user-specified "edits" to guide the translation, and pretty-prints valid Coq output.

- **Current target**: GHC 9.10.3, Coq 8.20 (branch `ghc910-coq820`)
- **Languages**: Haskell (the tool, ~14K LOC in `src/`), Coq (generated output and proofs)

## Build Commands

```bash
stack build                                    # Build hs-to-coq executable
stack exec hs-to-coq -- -e edits -o output/ Input.hs  # Run on a file
make                                           # Build base + base-thy + containers
make -C examples/base-src vfiles               # Re-generate base/ from Haskell sources
make -C examples/tests                         # Unit tests (.hs → .v → coqc)
make -C examples/base-tests                    # Tests requiring base/
make -C examples/containers                    # containers lib + theories (regenerates + builds)
make -C examples/transformers                   # transformers lib
make -C examples/ghc clean && make -C examples/ghc  # Regenerate+compile GHC lib + theories
cd examples && ./boot.sh                       # Full bootstrap (all examples)
# Individual Coq dirs: cd <dir> && coq_makefile -f _CoqProject -o Makefile && make -j
```

Use relative path instead of absolute path when `cd` to a directory.

### CI commands
- `/ci` — run CI checks locally, report pass/fail
- `/ci-fix` — run CI checks, diagnose and fix failures, commit fixes

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

### Stale .vo recovery
If you see "inconsistent assumptions over library Coq.Init.Prelude", rebuild the full chain: `base` → `base-thy` → `examples/containers` → `examples/ghc`. Each needs `make clean && make -j`.

### Axiomatized lib functions
When lib/*.v functions are `Axiom`, theories/*.v proofs that unfold them must be `Admitted`. Check with `grep "^Axiom" lib/Module.v` before attempting computation-based proofs. See "GHC example" section for the full list of axiomatized functions.

## Test Structure

- `examples/tests/` — Unit tests: each `.hs` file is translated to `.v` and type-checked with `coqc`. Tests categorized as `PASS`, `TODO_PASS` (known failures), `TODO_TRANSLATE`.
- `examples/base-tests/` — Tests requiring the `base/` Coq library to be built first.
- Test-specific edits/preambles go in `examples/tests/<TestName>/edits` and `<TestName>/preamble.v`.

## CI (`.github/workflows/hs-to-coq.yml`)

Four jobs: `build-haskell` (haskell:9.10.3 Docker), `test-coq-files` (mathcomp/mathcomp:2.5.0-coq-8.20 Docker, builds base+containers+ghc lib and theories), `tests` (haskell-actions + opam for Coq), `test-translation` (haskell:9.10.3 Docker, verifies base/containers/ghc regeneration matches). Sets `LANG=C.utf8` globally for Unicode support.

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

### Common edit patterns for GHC 9.10
- **`skip` vs `skip method`**: Never use `skip Mod.func` for class methods — use `skip method Mod.Class func` only. Using both causes "skipping a binding" errors.
- **`SigPat` in GHC 9.10**: `foldl'`/`foldr'`/`foldMap'` default implementations use `SigPat` which hs-to-coq doesn't support. Skip via `skip method`.
- **mconcat `foldl' (<>) mempty`**: GHC 9.10 generates this but it creates circular deps. Fix: `redefine` to use `foldr mappend mempty` + `order mempty mconcat`
- **`GHC.Prim.coerce` with abstract types**: Coq can't resolve `Coercible` for newtypes with abstract type vars. Fix: replace with explicit pattern matching
- **`rightSection`**: GHC 9.10 desugars `(op x)` to `rightSection op x`. Defined in `base/GHC/Prim.v`. Operators with invalid Coq chars (like `$`) are rendered as z-encoded names (e.g. `op_zd__`) instead of notation form. Proofs involving `rightSection` need `unfold GHC.Prim.rightSection` before `lia`
- **`<*` operator ambiguity**: `GHC.Base.<*` parses as `GHC.Base.<` followed by `*`. Excluded from `qualidHasValidCoqOp` in `Gallina/Util.hs` — renders as `op_zlzt__` instead. Definition added via `add` directive in base-src edits.
- **`foldMap'` in Foldable**: GHC 9.10 added this to the Foldable class. Old restored .v files need the field added manually

### Edits system gotchas
- **`skip` overrides `redefine`**: In `definitionTask` (Monad.hs), `skip` is checked first. Remove `skip` directives before adding `redefine` for the same function.
- **`redefine` type annotations**: The edits parser doesn't support `*` in product types or `%type` scope annotations. Omit the type signature (use `:=` directly) to work around parse errors.
- **`order` with `redefine`**: When `redefine` introduces definition dependencies, add explicit `order` directives to ensure correct output ordering.
- **`redefine Inductive` sorts**: The code generator's `Set` heuristic (for prop-lowerable types) doesn't apply to `redefine Inductive` — must specify `: Set` explicitly for empty/single-no-arg-constructor types.
- **Parser extensions (ghc910-coq820)**: `if/then/else`, `#n` hash-number literals, and `let fix ... in` are supported in `redefine` bodies (added in Lexer.hs/Parser.y).

### GHC example (examples/ghc/)
Translated from GHC 9.10.3. All lib/*.v and 28 theories/*.v compile. `make clean && make` regenerates lib/ (removes dir, rebuilds via hs-to-coq + lndir for ~60 manual files). Edit `manual/*.v` directly (not `lib/*.v` symlinks).

Key GHC 9.10 type changes: `Alt` uses `Mk_Alt` constructor (not tuple); `Mk_Id` has 7 fields (`varMult : Mult` added 4th); `realUnique` is `Unique` not `N`; `Var` has single constructor `Mk_Id` (no `TyVar`); `cse_bind` has 5 args; `lookupIdSubst` dropped `String` doc param; State monad is bare function type; `mkVarApps` uses `foldl'`. GoDom: use `alt_rhs` projection (strict positivity).

Un-axiomatized: `Subst` type (concrete inductive in Core.v, merged from GHC.Core.TyCo.Subst via CORESYN group), `substExpr`/`substBind` (mutually recursive Fixpoint in CoreSubst midamble), `exitifyRec` (concrete with `deferredFix2`), `Id.idJoinPointHood` (concrete definition). CoreSubst uses hybrid auto-generation: 4 functions auto-generated from GHC 9.10 source (`extendIdSubst`, `extendIdSubstList`, `extendSubstList`, `lookupIdSubst_maybe`), 9 redefined in edits (simplified for `TvSubstEnv=CvSubstEnv=unit`), core subst functions in midamble (ordering: midamble before generated code). Key proven theorems: `WellScoped_substExpr` (Qed, 0 Admitted in CoreSubst.v), `exitifyProgram_WellScoped_JPV` (Qed), `deAnnotate_snd_collectNAnnBndrs` (Core.v), `stripTicksE_id`/`stripTicksT_nil` (CSE.v), 36 FSet interface lemmas (VarSetFSet.v; 5 key-surjectivity lemmas newly proved via `StrongValidVarSet` axiom: subset_1, is_empty_1, for_all_1/2, exists_2), `freeVarsOf_freeVars_revised` (CoreFVs.v). Zero Admitted in: CoreInduct, CoreFVs, CoreSemantics, JoinPointInvariants, CoreSubst, ScopeInvariant, Var, VarSet, VarSetStrong, UniqSetInv, StateLogic, FV, VarEnv. Key axioms: `tyCoFVsOfType_is_emptyFV`/`tyCoFVsOfCo_is_emptyFV` (type FVs are empty since types are axiomatized), `tyCoVarsOfTypeDSet_empty`, 0 Local Axioms in ContainerProofs.v (imports `deferredFix2_eq` + `All_IntMaps_WF` from IntMapProofs). ContainerProofs has 94 proved lemmas including union/difference/intersection/disjoint/delete/filter properties; all 4 previously-axiomatized characterizations (`lookup_union_eq`, `lookup_difference_eq`, `lookup_intersection_eq`, `disjoint_spec`) now proved via well-founded induction on `size_nat m1 + size_nat m2`. Still axiomatized: `cseExpr`, `cseBind`, `try_for_cse`, `floatExpr`/`floatBind`/`floatRhs`, `fiExpr`/`fiBinds`/`fiRhs`, `mkExitJoinId`.

Build details: `manual/AxiomatizedTypes.v` instances must be `#[global]`. `axiomatize module OccurAnal` needs preamble.v + midamble.v. Midamble placed AFTER types+auto-Defaults, BEFORE values — use `skip` + midamble for custom Defaults. Makefile sed post-processing: BasicTypes/Literal (`#[global]`), UniqFM (phantom kinds), Core.v (mutual type fixes via `fix-files/`).
Core.v post-processing uses `fix-files/` for multi-line insertions (portable across GNU/BSD sed). GHC regeneration on macOS requires GNU sed: `brew install gnu-sed && PATH="/opt/homebrew/opt/gnu-sed/libexec/gnubin:$PATH" make -C examples/ghc vfiles`.

### Paper claims audit
`paper-claims-audit.md` (project root) documents the status of formal verification claims from three publications (JFP 2021, arxiv:1910.11724, ICFP 2018) against the current codebase. Key results: all core verification theorems (WellScoped_substExpr, exitifyProgram_WellScoped_JPV, FSet/FMapInterface, type class laws) still hold. MonoidLaws for Map proved in TypeclassProofs.v (was a gap vs JFP Fig 4). Map fromList `Program Fixpoint` regressions from Coq 8.20 fixed (0 Admitted). Regressions: CSE (5 Admitted, axiomatized source).

### Containers submodule
Containers v0.7. `make clean` removes `lib/` and `hs-spec/`; `make` regenerates and builds everything. IntSet/Set/Map have native v0.7 split/fromAscList/fromDescList definitions. `hs-spec/IntSetProperties.v` auto-generated from v0.7 test sources. Full type class laws verified: EqLaws, OrdLaws, SemigroupLaws, MonoidLaws, FunctorLaws for Map (all Qed in TypeclassProofs.v). Map fromList proofs fully verified (0 Admitted in FromListProofs.v).

### Transformers example (examples/transformers/)
Regenerated from GHC 9.10 transformers source via symlink `transformers -> ../ghc/ghc/libraries/transformers`. Makefile strips MonadTrans quantified superclass constraint via sed post-processing. Uses `skip class` for `Contravariant` and `Foldable1` (not in base).

### Coq 8.20 compatibility
- `#[global]` required: `Program Instance` and `Program Definition` need `#[global]` prefix. Locality goes before `Program` (i.e., `#[global] Program Definition`).
- Type and constructor cannot share the same name (e.g., `StateT`)
- `omega` → `lia`; `le_lt_n_Sm` removed (use `lia` instead)
- `intuition`/`f_equal`/`auto` solve more goals — proof bullet structures may break. `auto` no longer resolves `E.eq` goals — use explicit `apply E.eq_refl`.
- Section `Variable` hypotheses generate side conditions in `rewrite`. `clear -H1 H2` clears section variables — add them to keep list (e.g., `clear -H1 H2 HEqLaws HOrdLaws`).
- `Program Fixpoint ... := _.` obligations: see "Coq 8.20 proof tactics" section below.
- Typeclass resolution may not unfold definition chains (`Key→N→Word`) — add explicit instances
- Names from `Coq.Lists.List` (like `filter`, `partition`) may shadow project names — qualify explicitly
- `eval unfold f` in sections: use `let x := constr:(@f args) in let rhs := eval unfold f in x`
- `Foldable__list_foldMap` is now `mconcat ∘ map` (not direct `foldr`) — different unfolding chains needed
- **Deprecated warnings (all fixed)**: `Hint` needs `#[export]` or `: core`; `Arguments` scope uses `%_` not `%`; empty/singleton-constructor inductives use `Set` not `Type` to avoid auto-prop-lowering; `app_length` → `length_app`, `map_length` → `length_map`, `seq_length` → `length_seq`; `N.mod_eq` etc. → `N.Div0.*`; `Declare Scope` before `Bind Scope`
- **Implicit binders in record literals (all fixed)**: `fun {a : Type}` inside `{| field := ... |}` triggers `unexpected-implicit-declaration` — use `fun (a : Type)` (explicit) instead. Code generator uses `quantifyExplicit` (Instances.hs) + `toExplicitBinder` (Gallina/Util.hs) for this. Same applies to midambles, edits, and manual .v files.
- **Require inside Module/Section (all fixed)**: Triggers `require-in-section` warning. Move `Require` to file top-level; use `Export`/`Import` inside the block if needed. If moving causes name shadowing, keep in place and suppress with `#[local] Set Warnings "-require-in-section".` / `#[local] Set Warnings "require-in-section".`
  - **Danger**: Moving `Require Import GHC.Base` to top shadows `Nat.le` (Prop) with bool-valued `<=`, breaking proofs that use `length x <= length y`. Always verify moved imports don't change notation scope.
- **SSReflect `spurious-ssr-injection` (all fixed)**: `repeat case` on enum types with `==` triggers this. Suppress with `#[local] Set Warnings "-spurious-ssr-injection"`, or replace `[]` intro patterns with named wildcards.

### Coq 8.20 proof tactics
- **`Program Fixpoint` obligations**: Coq 8.20 pre-introduces ALL obligation variables. Use `revert dependent P` to recover CPS structure, or work with auto-named `H`/`H0`/`H1`.
- **`order e` + `==`**: `order e` can't handle `Eq_` class `==`. Convert `(x == y) = true` to `(y <= x) = true` via `Eq_le_r` first.
- **Z multiplication match form**: `2 * 2^x` reduces to `match 2^x with 0=>0|Z.pos p=>Z.pos p~0|Z.neg p=>Z.neg p~0 end`. Use `change (match ...) with (2 * 2^x)%Z in *` to normalize before `lia`/`rewrite`.
- **`applyDesc` consumes `Hsem`**: `try replace (sem s) in *` clears `Hsem`. If you need `Hsem` later, use manual CPS: `eapply lem. exact HB. intros s HB _ Hsem. apply showDesc'. split; [assumption|].`
- **`SomeIf` opacity**: `unfold SomeIf` before `destruct`/`simpl` to enable `if`-reduction.
- **`destruct_match` in Map proofs**: Picks up wrong matches (e.g. `Z.pow` in hypotheses). Use explicit `destruct p as [kx vx]; destruct (not_ordered ...) eqn:Hord` instead.
- **`++` associativity**: Coq `++` is right-associative. `A ++ nil ++ B` is `A ++ (nil ++ B)` — use `app_nil_l`, not `app_nil_r`.

## Workflow

- Every time before you commit, you should also check if other modules have been broken due to this change. For example, check `examples/test` even if you have only been working on `examples/containers`.
- After significant functional changes (e.g., replacing `redefine` with native implementations), update README files, CLAUDE.md, and any plan documents to reflect the new state before committing.
- Commit to git at each milestone with `Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>`

