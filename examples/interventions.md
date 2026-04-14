# Interventions Log

## Phase 1: Coq 8.20 Compatibility Fixes

### graph/lib (Data/Graph/Inductive/)
- `Graph.v`: `Require Import Omega` → `Require Import Lia`; `omega` → `lia`
- `Internal/Heap.v`: Same Omega→Lia fix; `plus_assoc` → `rewrite H1. lia.` (Nat.add_assoc not in scope); all `omega` → `lia`

### graph/theories
- All 8 .v files: `Require Import Omega` → `Require Import Lia`; `omega` → `lia` (bulk sed)
- `Crush.v`: `elimtype False` → `exfalso` (elimtype removed in Coq 8.20)
- `NicerQueue.v`: `Foldable.Foldable__list_foldl'` → `Foldable.Foldable__list_foldl` + `unfold foldl'` → `unfold foldl'. unfold foldl.` (foldl' no longer a class field)
- `Path.v`: `Nat.le`/`Nat.lt` → `le`/`lt` (via sed); `unfold le` removed (le is inductive, can't unfold); `unfold Nat.le in H2` blocks → replaced with `Peano.le`/`Peano.lt` assertions + `lia`; `Eq___option_op_zeze__` → `simpl`

### shuffle/lib
- All 5 .v files with termination proofs: `Lt.lt_n_S` → `-> PeanoNat.Nat.succ_lt_mono` (Lt.lt_n_S removed in Coq 8.20)

### resources
- `list_monad.v`: `From Coq Require Import ssrnat seq` → `From mathcomp Require Import ssreflect ssrnat seq` (MathComp 2.x paths)

## Phase 1: GHC 9.10 Compatibility

### transformers/lib
- Created symlink `examples/transformers/transformers` → `../ghc/ghc/libraries/transformers`
- Added to `edits`: `skip class Data.Functor.Contravariant.Contravariant`, `skip class Data.Foldable1.Foldable1`
- Created `module-edits/Control/Monad/Trans/Class/edits` (empty, allows generation)
- Post-generation fix: removed quantified superclass `{forall {m}, ... GHC.Base.Monad (t m)}` from `MonadTrans` definition (Coq can't resolve)

### base/GHC/Base.v
- Added `op_zlzt__` definition (Haskell's `<*` operator, = `liftA2 (fun x _ => x)`)
- Added `_<*_` and `GHC.Base.<*` notations

### core-semantics
- `lib/GHC/SmallStep.v`: `Require Omega` → `Require Import Lia`; `Omega.omega` → `lia`
- `module-edits/GHC/SmallStep/midamble.v`: same Omega→Lia fix
- Cannot regenerate from source: `ghc-core-smallstep` submodule uses pre-GHC 9.10 module names
- `Id.mkSysLocalOrCoVar` → `Id.mkSysLocal` + added `Mult` argument (`HsToRocq.Err.default`)
- `Unique.mkBuiltinUnique` → `GHC.Builtin.Uniques.mkBuiltinUnique` (module moved in GHC 9.10)
- `CoreSubst.substExpr Panic.someSDoc` → `CoreSubst.substExpr` (SDoc parameter removed in GHC 9.10)
- Alt patterns: `pair (pair altcon pats) rhs` → `Core.Mk_Alt altcon pats rhs` (Alt is now inductive, not tuple)
- Removed `Require Panic.` (no longer used)

### ghc/lib/Literal.v
- Added `#[global]` to `Default__LitNumType` and `Default__Literal` instances (needed for cross-module visibility in Coq 8.20)

### resources/list_monad.v
- `From Coq Require Import ssrnat seq` → `From mathcomp Require Import ssreflect ssrnat seq` (MathComp 2.x)

## Phase 2: Translation Reproducibility

### base-src edits (op_zlzt__)
- Moved `op_zlzt__` from manual base/GHC/Base.v edit to `add GHC.Base Definition` in module-edits/GHC/Base/edits
- Removed `<*` and `GHC.Base.<*` notations (unused, and GHC.Base.<* is ambiguous with Coq's `<` operator)

### src/lib/HsToRocq/Rocq/Gallina/Util.hs
- Added `<*` to `isAmbiguousRocqOp` in `qualidHasValidRocqOp` — `GHC.Base.<*` parses as `GHC.Base.<` followed by `*`
- Now renders as `op_zlzt__` instead of `<*` notation

### examples/ghc/Makefile
- Moved Literal.v `#[global]` sed from OUTFILES_GEN to OUTFILES_CORE rule (Literal is in CORE_MODULES, not MODULES)
- Updated README.md generation to match committed version

### examples/transformers/Makefile
- Added post-generation sed to strip MonadTrans quantified superclass constraint

## Phase 3: CI Fixes

### examples/ghc/Makefile
- Moved `CallArity` from `EXTRAS` to `HANDMOD` — CallArity has a manual version in `manual/CallArity.v` but was listed in EXTRAS (which triggers hs-to-rocq generation). In parallel Make, this caused a race condition: if hs-to-rocq ran before `lndir` created the symlink, it produced `CallArity.h2ci` (not in git), causing the `test-translation` CI job to fail.

### .github/workflows/hs-to-rocq.yml
- Added `mkdir -p /root/.docker && echo '{}' > /root/.docker/config.json` before cache steps in `build-haskell` and `test-translation` container jobs to suppress `WARNING: Error loading config file: open /root/.docker/config.json: permission denied`.

## Phase 4: CI Coverage Expansion

### .github/workflows/hs-to-rocq.yml
- Added transformers/lib to `test-coq-files` job
- Added graph/lib + graph/theories (8 of 11 files, excluding 3 that need coq-equations: BFSProofs, HeapProofs, SPProofs) to `test-coq-files` job
- Added core-semantics/lib to `test-coq-files` job (depends on ghc/lib + transformers)
- Added resources/list_monad.v to both `test-coq-files` and `tests` jobs
- Updated job name to "Testing all Coq examples (Coq 8.20)"

## Phase 5: Proof Regression Fixes (ghc910-coq820)

### examples/ghc/manual/GHC/Utils/Monad/State/Strict.v
- Replaced 3 `Admitted` typeclass instances (`Functor__State`, `Applicative__State`, `Monad__State`) with concrete CPS implementations matching hs-to-rocq encoding. State is bare function type `s -> (a * s)` in GHC 9.10.

### examples/ghc/theories/StateLogic.v
- Restored all 14 Admitted proofs to Qed. Key proof patterns: unfold `op_zgzgze__`/`State.Monad__State`/`State.Monad__State_op_zgzgze__` chain, then `simpl` + `expand_pairs`. The `liftA2` proofs need similar `Applicative__State_liftA2` unfolding.

### examples/ghc/theories/ContainerProofs.v
- Added `Eq_membership` axiom (IntMap equality implies pointwise member equality). Uses explicit named parameters `(A : Type) (HeqA : Eq_ A) (HlawsA : EqLaws A)` — backtick syntax makes `A` implicit in a way that `(A:=Var)` syntax doesn't work.

### examples/ghc/theories/CoreFVs.v
- Added 4 axioms for `tyCoFVsOfType`/`tyCoFVsOfCo` well-formedness and locality
- Proved `varTypeTyCoFVs_WF` lemma from axioms
- Fixed `addBndr_WF`: now independently proven (was unsoundly relying on Admitted `addBndr_fv`)
- Restored `expr_fvs_WF`: structural induction on `core_induct`, destruct `binds` for Let case
- Restored `exprFreeVars_Cast`: uses `change` to expose `unionFV`, then `unionVarSet_unionFV` (swaps FV args!), `filterVarSet_equal`, `tyCoFVsOfCo_not_local`

### examples/ghc/theories/VarSet.v
- Restored `IntMapEq_VarSetEq`: uses `Eq_membership` from ContainerProofs.v
- Restored `elemVarSet_minusVarSetTrue`/`elemVarSet_minusVarSetFalse`: uses `eqE` then `set_b_iff`, `F.diff_iff`, `singleton_1`
- Restored `elemVarSet_unitVarSet_is_eq`: destruct 7-field `Mk_Id` + `MkUnique` wrappers then `reflexivity`

### Not fixable
- `addBndr_fv`, `exprFreeVars_mkLams_rev/mkLams`: varTypeTyCoFVs no longer emptyFV, Denotes set changed
- `exprFreeVars_Type/Coercion`: need `=` not `[=]`
- `no_TyCoVars`: statement is false in GHC 9.10
- `exprFreeVars_Case`, `freeVarsOf_freeVars_revised`, `deAnnotate_freeVars`: depend on above
- All Exitify/CoreSubst/Var.v isJoinId proofs: axiomatized definitions
- FromListProofs.v: Coq 8.20 Program Fixpoint obligations (~250 lines each, deferred)

## Summary of Results
- **23 examples fully compile** (base, base-thy, containers lib+theories, ghc lib+theories, transformers, graph/lib, core-semantics, bag, compiler, coinduction, dlist, intervals, successors, rle, quicksort, lambda, simple, resources)
- **1 partial**: graph/theories (8/11, 3 need coq-equations)
- **1 partial**: shuffle/lib (2/5, missing Random Int instance)
- **2 blocked**: wc (needs coq-itree), shuffle/theories
- **3 N/A**: tip, locks, base-src (no buildable .v files in git)
- **Translation reproducibility**: base, containers, ghc all regenerate to match committed copies exactly
