# Todo List: hs-to-coq GHC 9.10 + Coq 8.20 Migration

## Completed
- [x] hs-to-coq compiles with GHC 9.10.3
- [x] Base library compiles (GHC 9.10 module renames, coerce expansion, foldl' alias)
- [x] Base-thy compiles (no Admitted proofs outside comments)
- [x] Base regeneration stable (`make -C examples/base-src clean && make -C examples/base-src` works)
- [x] Data/Functor/Identity and Data/Traversable auto-generated (removed from HANDMOD)
- [x] Containers lib compiles (omega→lia, #[global], Foldable field removals)
- [x] Containers theories: all proof files compile with Coq 8.20
- [x] Unit tests: all PASS tests pass (4 TODO_PASS expected)
- [x] Base-tests: all PASS tests pass (3 TODO_PASS expected)
- [x] Pretty.hs fixes: locality before Program, invalid operator chars fallback
- [x] common.mk: LANG=C.utf8 for Unicode
- [x] CI workflow: Docker images (haskell:9.10.3, mathcomp:2.5.0-coq-8.20), 10 examples, permission fixes
- [x] All 10 examples build: compiler, rle, quicksort, dlist, coinduction, intervals, successors, lambda, simple, containers
- [x] README updated for GHC 9.10.3 and Coq 8.20
- [x] CLAUDE.md updated with comprehensive docs
- [x] GHC submodule at ghc-9.10.3-release
- [x] Containers `make clean && make` works (Makefile preserves .v files, builds lib + theories)
- [x] Improved error messages in ProcessFiles.hs (load failure recovery, per-module diagnostics)

## Known Issues (not blocking CI)
- [ ] `Data/Functor/Classes` still manual: quantified superclass constraints in Eq2/Ord2
- [ ] `Control/Category`, `Control/Arrow` still manual: Category__arrow unit-id issue
- [ ] `bag` example: ssreflect proofs need updating for Coq 8.20/mathcomp
- [ ] `graph`, `shuffle`, `wc`, `core-semantics`, `transformers`: submodules not checked out
- [ ] Unit tests: MutrecInst, TopBind, ExceptInDataDefinition, TypeAnnotations still in TODO_PASS
- [ ] Containers submodule at v0.6.0.1: `foldl'` ambiguity prevents regeneration with GHC 9.10
- [ ] `act` not available for local CI testing
