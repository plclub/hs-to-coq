# Todo List: hs-to-coq GHC 9.10 + Coq 8.20 Migration

## Completed
- [x] Base library compiles (GHC 9.10 module renames, coerce expansion, foldl' alias)
- [x] Base-thy compiles (no Admitted proofs outside comments)
- [x] Base regeneration stable (`make -C examples/base-src vfiles` produces identical output)
- [x] Containers lib compiles (omega→lia, #[global], Foldable field removals)
- [x] Containers theories: all 13 proof files compile with Coq 8.20
- [x] Unit tests: all PASS tests pass
- [x] Base-tests: all PASS tests pass
- [x] Pretty.hs fixes: locality before Program, invalid operator chars fallback
- [x] common.mk: LANG=C.utf8 for Unicode
- [x] CI workflow: Docker images, 10 examples in tests job, base regeneration test
- [x] All 10 examples build:
  - coinduction: GHC.Num.Natural rename, rightSection proof fixes
  - intervals: GHC.Internal.Int.Int64 rename, omega→lia
  - successors: `$` operator fix via qualidHasValidCoqOp
  - quicksort: rightSection unfold before destruct, Omega→Lia
  - compiler, rle, dlist, lambda, simple: build without changes

## Known Issues (not blocking CI)
- [ ] `bag` example: ssreflect proofs need updating for Coq 8.20/mathcomp
- [ ] `graph`, `shuffle`, `wc`, `core-semantics`, `transformers`: submodules not checked out
- [ ] Unit tests: MutrecInst, TopBind, ExceptInDataDefinition still in TODO_PASS
- [ ] Containers submodule at v0.6.0.1: `foldl'` ambiguity prevents regeneration with GHC 9.10
- [ ] Containers regeneration test skipped in CI

## Not Started
- [ ] Push changes to remote
