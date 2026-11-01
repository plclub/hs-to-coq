# Tool tests

This directory contains the Haskell test suites and shell integration runners
for hs-to-rocq. Compiler fixtures remain in
[`examples/tests/`](../examples/tests/README.md), shared by the Coq 8.20 and
Rocq 9.0 Make wrappers. Base-dependent fixtures remain in
`examples/base-tests/`.

Run the commands below from the repository root.

## Haskell test suites

Run all three Cabal suites with either build tool:

```bash
stack test
# Or, with cabal-install:
cabal test all
```

Use the project's Haskell toolchain (currently GHC 9.10.3); Stack selects it
through `stack.yaml`. The build tool resolves the Haskell dependencies declared
in [`hs-to-rocq.cabal`](../hs-to-rocq.cabal). These suites do not need a Coq/Rocq
compiler, a generated base library, or a separately built translator executable.
The `ci-catalog` suite also requires Bash on `PATH`.

| Suite | Main file | Checks |
| --- | --- | --- |
| `edits` | [`test/Edits.hs`](Edits.hs) | Public edits parser and builder APIs, including syntax, configuration, precedence, and diagnostics. |
| `rocq-version` | [`test/RocqVersion.hs`](RocqVersion.hs) | Target-version parsing and AST/text namespace rewriting. |
| `ci-catalog` | [`test/CiCatalog.hs`](CiCatalog.hs) | Workflow/catalog agreement, `/ci-fix` delegation, failure propagation, Bash syntax, and catalog regressions. |

To focus on one suite:

| Stack | Cabal |
| --- | --- |
| `stack test hs-to-rocq:edits` | `cabal test edits` |
| `stack test hs-to-rocq:rocq-version` | `cabal test rocq-version` |
| `stack test hs-to-rocq:ci-catalog` | `cabal test ci-catalog` |

`CiCatalog` runs its complete self-tests with no arguments. It reads the
workflow, both command documents, and the pinned `ci-catalog-old-head.md`
fixture. Its shell regressions use stubbed tools; they do not run the documented
builds or regeneration. The `--self-test` argument remains accepted for direct
compatibility:

```bash
stack exec -- runghc -package=yaml test/CiCatalog.hs --self-test
```

## Shell integration checks

Shell runners are explicit checks, not part of `stack test` or `cabal test all`.
They require Bash and standard Unix utilities. The fake-tool harness also needs
Make, but no Haskell or Coq/Rocq toolchain:

```bash
bash test/harness.sh
```

The real-translator checks use Stack to invoke `hs-to-rocq`, so build the
executable with Stack first, even if you ran the Haskell suites with Cabal:

```bash
stack build
bash test/edits.sh
bash test/concurrent.sh
```

Neither script needs a Coq/Rocq compiler or a compiled base library:

- `edits.sh` checks translation output and rejection diagnostics. With no
  arguments it checks both targets; select one with
  `bash test/edits.sh --target-version 8.20` or `--target-version 9.0`.
- `concurrent.sh` runs translators concurrently with a shared Haskell dependency
  on both targets. It checks output files, the absence of shared GHC object
  artifacts by default, and the explicit GHC code-generation override.

The runners use temporary directories and remove them on exit. The
[coverage matrix](../examples/tests/README.md#edit-coverage-matrix) records the
edits API, CLI, and compiler witnesses and their limitations.

## Compiler and base checks

Build the translator with Stack first. For each command, use the matching
Coq 8.20 or Rocq 9.0 environment with its Equations plugin installed:

```bash
make -C examples/tests
make -C examples/rocq9.0/tests
```

These shared compiler suites do not need the translated base library. Each
Make entry point also runs `edit-checks`: the `edits` Cabal suite via
`stack --allow-different-user test hs-to-rocq:edits`, followed by `test/edits.sh`
for that wrapper's target version. See the
[shared test guide](../examples/tests/README.md#run-the-tests) for focused Make
targets and expected-failure categories.

Base checks require the matching compiler and compiled base library; building
the base also requires the matching `coq_makefile`. Their existing Make entry
points include the relocated `test/deriving.sh` and `test/identity-traversal.sh`
runners:

```bash
# Coq 8.20; requires compiled base/
make -C examples/base-tests
# Rocq 9.0; compiles its base before running the checks
make -C examples/rocq9.0 base
```

The deriving runner also needs the Stack-built translator; the traversal runner
uses Git to locate the repository and compiles
`examples/base-tests/IdentityTraversal.v`. See
[deriving and base integration](../examples/tests/README.md#deriving-and-base-integration)
for direct commands, prerequisites, and the scope of the assumption checks.

## Local CI and validation records

Use [`.claude/commands/ci.md`](../.claude/commands/ci.md) for the authoritative
seven-job catalog and compiler environments;
[`ci-fix.md`](../.claude/commands/ci-fix.md) adds repair guidance.
CI runs the Haskell suites in `build-haskell`, then runs the harness and concurrent
translation checks separately.

The [historical validation records](../examples/tests/README.md#issue-228-validation)
remain scoped to their recorded revisions. This guide describes commands and
coverage, not a new verification result.
