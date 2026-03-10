# hs-to-coq GHC 9.10 / Coq 8.20 Migration TODO

## Task Status

### 1. Update hs-to-coq to support Haskell 9.10 and Coq 8.20
- [x] Tool builds with GHC 9.10.3 (stack.yaml uses lts-24.32)
- [x] Generated Coq compiles with Coq 8.20
- [x] Fix deprecated Coq 8.20 warnings (commit 06ceab6e)
- [x] Add #[export] to bare Hint declarations (commit 57678959)

### 2. Update all submodules
- [x] examples/ghc/ghc — ghc-9.10.3-release
- [x] examples/containers/containers — v0.7
- [x] Verify other submodules: graph (fgl 5.5.0.1, in CI), core-semantics (manual fix, in CI), shuffle (2/5 modules, not in CI — missing Random Int), wc (blocked by coq-itree, not in CI), doc theme (N/A)

### 3. Update manually written Coq code
- [x] base-thy proofs updated for Coq 8.20
- [x] containers/theories updated for Coq 8.20
- [x] ghc/theories updated for Coq 8.20
- [x] Deprecated warnings fixed across all components

### 4. Check GitHub workflow and fix examples
- [x] CI has 4 jobs: build-haskell, test-coq-files, tests, test-translation
- [x] CI uses haskell:9.10.3 and mathcomp/mathcomp:2.5.0-coq-8.20 Docker images
- [x] Working examples added to CI (commit f997ae57)
- [ ] Verify all CI jobs pass on GitHub

### 5. examples/base-src works correctly
- [x] `make -C examples/base-src vfiles` regenerates base/ successfully
- [x] All generated .v files compile with coqc
- [x] No changes to base/ directly — all changes via base-src edits/manual files

### 6. base-thy compiles — no Admitted or Axiom
- [x] All base-thy .v files compile
- [x] Zero Admitted proofs
- [x] Zero Axiom declarations

### 7. examples/containers works
- [x] containers/lib compiles
- [x] containers/theories compiles
- Note: IntSetWordProofs.v has ~80 Admitted (pre-existing, not a regression)
- Note: MapProofs/FromListProofs.v has 2 Admitted (pre-existing)

### 8. Commit to Git at milestones
- [x] Deprecated warning fixes committed (06ceab6e)

### 9. Update documents
- [x] Update CLAUDE.md to reflect deprecated warning fixes
- [x] Update memory files to remove stale info
- [x] Review README for accuracy (reflects GHC 9.10.3 / Coq 8.20, examples table up to date)

### 10. Update GitHub actions
- [x] Uses haskell:9.10.3 Docker for Haskell builds
- [x] Uses mathcomp/mathcomp:2.5.0-coq-8.20 Docker for Coq builds
- [x] Uses haskell-actions/setup for tests job
- [x] Verify Docker image versions are latest appropriate (haskell:9.10.3 matches target GHC; mathcomp:2.5.0-coq-8.20 is latest for Coq 8.20)

### 11. Test GitHub actions locally
- [x] Test build-haskell job locally (stack build succeeds)
- [x] Test test-coq-files job locally (base, base-thy, containers, transformers, graph, ghc, core-semantics all build)
- [x] Test tests job locally (unit tests pass, base-tests pass, all small examples build)
- [x] Test test-translation job locally (base, containers, ghc all regenerate with zero diff)

### 12. CLAUDE.md audit
- [x] Audit and trim CLAUDE.md (173 lines, under 200 limit)
- [x] Ensure deprecated warning info is up to date
- [x] Remove outdated migration notes
