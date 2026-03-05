# Todo List: hs-to-coq GHC 9.10 + Coq 8.20 Migration

## Completed
- [x] Base library compiles (GHC 9.10 module renames, coerce expansion, foldl' alias)
- [x] Base-thy compiles (no Admitted proofs)
- [x] Containers lib compiles (omega→lia, #[global], Foldable field removals)
- [x] Containers theories: all 13 proof files compile with Coq 8.20
- [x] Unit tests: all PASS tests pass, Deriv2/3 moved to PASS
- [x] Base-tests: all PASS tests pass
- [x] Fix Pretty.hs: locality attribute before Program keyword
- [x] Fix Pretty.hs: operators with invalid Coq chars (e.g. `$`) use z-encoded names
- [x] Fix common.mk: LANG=C.utf8 for Unicode
- [x] CI workflow updated: Docker images for GHC 9.10.3 and Coq 8.20
- [x] Example fixes:
  - successors: `$` operator token fix via Pretty.hs qualidHasValidCoqOp
  - intervals: GHC.Internal.Int.Int64 rename edit, omega→lia in proofs
  - coinduction: GHC.Num.Natural rename edit, rightSection proof fixes
  - compiler, rle, quicksort, dlist, lambda, simple: all build successfully

## Known Issues (not blocking CI)
- [ ] `bag` example: ssreflect proofs need updating for Coq 8.20/mathcomp changes
- [ ] `graph`, `shuffle` examples: submodules not checked out
- [ ] Unit tests: MutrecInst, TopBind, ExceptInDataDefinition still in TODO_PASS
- [ ] Containers submodule stays at v0.6.0.1 (v0.7 would require 11K+ line changes)

## Not Started
- [ ] Push changes to remote
