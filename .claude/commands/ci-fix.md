---
description: Run all CI checks locally, diagnose and fix any failures, then commit the fixes. Use this whenever you want to make sure everything passes before pushing, or after making changes that might break downstream Coq compilation or tests.
allowed-tools: Bash, Read, Write, Edit, Glob, Grep, Agent, mcp__rocq-mcp__rocq_get_goals, mcp__rocq-mcp__rocq_run_tactic, mcp__rocq-mcp__rocq_start_proof, mcp__rocq-mcp__rocq_get_state_at_position, mcp__rocq-mcp__rocq_search
argument-hint: "[job] (build|test-coq|tests|test-translation|all)"
---

Run CI checks locally (mirroring `.github/workflows/hs-to-coq.yml`), diagnose and fix any failures, then commit the fixes. All tools (stack, coqc, coq_makefile) are already installed — no Docker or opam setup needed. Do NOT use `--allow-different-user` (that's only for CI containers).

All commands run from the workspace root using relative paths.

The argument is: $ARGUMENTS

If the argument is empty or "all", run ALL four jobs in order. Otherwise run only the specified job.

## Workflow

For each job:
1. Run the CI step
2. If it passes, move on
3. If it fails, diagnose the error, fix it, re-run to verify, then continue
4. After all jobs pass, commit any changes made during fixing

Keep an intervention log at `.claude/ci-fix-log.md` documenting each failure and how it was fixed. This helps track what went wrong and why.

## Job: build

```bash
stack build
```

**If it fails**: Read the compiler error carefully. The Haskell source is in `src/`. Fix the compilation error, re-run `stack build` to verify.

## Job: test-coq

Build all Coq targets in dependency order. For each directory, generate the Makefile from `_CoqProject` first. Run each group sequentially — they depend on each other in order.

```bash
# 1. base + base-thy
(cd base; coq_makefile -f _CoqProject -o Makefile) && make -j -C base
(cd base-thy; coq_makefile -f _CoqProject -o Makefile) && make -j -C base-thy

# 2. containers
(cd examples/containers/lib; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/containers/lib
(cd examples/containers/theories; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/containers/theories

# 3. transformers
(cd examples/transformers/lib; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/transformers/lib

# 4. graph
(cd examples/graph/lib; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/graph/lib
(cd examples/graph/theories; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/graph/theories

# 5. ghc
(cd examples/ghc/lib; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/ghc/lib
(cd examples/ghc/theories; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/ghc/theories

# 6. core-semantics
(cd examples/core-semantics/lib; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/core-semantics/lib

# 7. resources
coqc -Q base "" examples/resources/list_monad.v
```

### Diagnosing Coq failures

When coqc fails, the error message tells you the file, line, and nature of the problem. The fix strategy depends on the file type:

**Generated files** (`lib/*.v` under examples): These are produced by hs-to-coq. Don't edit them directly — the fix goes in the corresponding edits/preamble/midamble:
  - `module-edits/<Module>/edits` — skip, rename, redefine, rewrite, order directives
  - `module-edits/<Module>/preamble.v` — Coq code prepended to output
  - `module-edits/<Module>/midamble.v` — Coq code inserted mid-file
  - Exception: `examples/ghc/manual/*.v` files ARE hand-written (symlinked into `lib/`). Edit those directly.
  - After editing edits/preamble/midamble, regenerate: `make -C examples/<project> vfiles` (or `make -C examples/base-src vfiles` for base/)
  - Then re-run coqc to verify

**Hand-written proof files** (`theories/*.v`, `base-thy/*.v`): Fix these directly. Common issues:
  - Tactic failures: use the Rocq MCP tools to explore proof state and find working tactics
  - Missing lemmas: search with `mcp__rocq-mcp__rocq_search`
  - Name changes: grep for the old name to find where it moved
  - `Admitted` proofs that should be `Qed`: try completing the proof

**Common Coq 8.20 issues** (see CLAUDE.md for full list):
  - `#[global]` needed on `Program Instance`/`Program Definition`
  - `omega` → `lia`
  - `Hint` needs `#[export]` or `: core`
  - `Arguments` scope uses `%_` not `%`
  - `app_length` → `length_app`, `map_length` → `length_map`
  - Implicit binders in record literals: `fun {a}` → `fun (a : Type)` inside `{| field := ... |}`

**"Inconsistent assumptions over library Coq.Init.Prelude"**: Stale .vo files. Clean and rebuild from the failing point:
```bash
make -C <dir> clean && make -j -C <dir>
```

## Job: tests

Build base first, then run unit tests and small examples.

```bash
# Build base
(cd base; coq_makefile -f _CoqProject -o Makefile) && make -j -C base

# Unit tests (exit code 2 is OK — TODO_PASS failures are expected)
make -C examples/tests || test $? -eq 2

# Base tests (exit code 2 is OK)
make -C examples/base-tests || test $? -eq 2

# Build base-thy
(cd base-thy; coq_makefile -f _CoqProject -o Makefile) && make -j -C base-thy

# Small examples
make -C examples/compiler
make -C examples/rle
make -C examples/quicksort
make -C examples/dlist
make -C examples/coinduction
make -C examples/intervals
make -C examples/successors
make -C examples/lambda
make -C examples/simple
(cd examples/bag; coq_makefile -f _CoqProject -o Makefile) && make -C examples/bag
coqc -Q base "" examples/resources/list_monad.v
```

**If a test fails**: Check if it's in the `PASS` or `TODO_PASS` category in `examples/tests/Makefile`. `TODO_PASS` failures (exit 2) are expected. Only `PASS` test failures need fixing.

For PASS test failures:
- Read the failing `.hs` file and its test-specific `edits`/`preamble.v` if they exist
- Check if it's a translation problem (fix edits) or a Coq compilation problem (fix preamble/generated code)
- Re-run just the failing test: `make -C examples/tests <TestName>.vo`

## Job: test-translation

Regenerate base, containers, and ghc, then verify the convenience copies match what's committed. Requires git submodules.

```bash
# Check submodules are initialized
git submodule update --init examples/ghc/ghc
git submodule update --init examples/containers/containers
git submodule update --init examples/graph/graph

# Build hs-to-coq first
stack build
```

Then for each target:

```bash
# base
make -C examples/base-src clean && make -C examples/base-src vfiles
git add base && git diff-index --cached --quiet HEAD -- base
git reset HEAD base

# containers
make -C examples/containers vfiles
git add examples/containers/lib && git diff-index --cached --quiet HEAD -- examples/containers/lib
git reset HEAD examples/containers/lib

# ghc
make -C examples/ghc clean && make -C examples/ghc vfiles
git add examples/ghc/lib && git diff-index --cached --quiet HEAD -- examples/ghc/lib
git reset HEAD examples/ghc/lib

# graph
make -C examples/graph clean && make -C examples/graph vfiles
git add examples/graph/lib && git diff-index --cached --quiet HEAD -- examples/graph/lib
git reset HEAD examples/graph/lib
```

**If `git diff-index` exits non-zero**: The convenience copy is out of date. This usually means someone edited hs-to-coq source or edits files without regenerating. Show `git diff --cached --stat` before resetting to see what changed. The fix is simple — the regenerated files ARE the fix. Stage and commit them.

Before committing regenerated files, first verify they compile by running the test-coq steps for the affected directories.

## After all jobs pass

1. Check if any files were modified during fixing:
   ```bash
   git status
   git diff --stat
   ```

2. If there are changes, commit them with a descriptive message explaining what was fixed. Group related fixes into logical commits (e.g., one for Coq proof fixes, one for regenerated files, one for Haskell source fixes).

3. Print a summary table:

```
| Job              | Status | Fixes Applied          |
|------------------|--------|------------------------|
| build            | PASS   | none                   |
| test-coq         | PASS   | Fixed Foo.v line 42    |
| tests            | PASS   | none                   |
| test-translation | PASS   | Regenerated base/      |
```

## Important caveats

- **Never skip verification**: After any fix, re-run the failing step to confirm it passes before moving on.
- **Downstream breakage**: Fixing one file can break downstream dependencies. After fixing a file in `base/`, re-check `base-thy/`, `containers/`, `ghc/`, etc.
- **Axiomatized functions**: Check `grep "^Axiom" lib/Module.v` before attempting computation-based proofs on axiomatized functions. If a lib function is `Axiom`, proofs that unfold it must remain `Admitted`.
- **Generated vs manual**: In `examples/ghc/lib/`, some files are symlinks to `manual/*.v` — edit the manual source, not the symlink. Check with `ls -la examples/ghc/lib/File.v`.
- **Edits system**: `skip` overrides `redefine`. If adding a `redefine`, remove any existing `skip` for the same function first.
- **Don't use --allow-different-user**: That flag is only for CI containers, not local runs.
