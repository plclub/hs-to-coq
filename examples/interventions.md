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
- Blocked by missing `Id.mkSysLocalOrCoVar` (renamed in GHC 9.10)

### ghc/lib/Literal.v
- Added `#[global]` to `Default__LitNumType` and `Default__Literal` instances (needed for cross-module visibility in Coq 8.20)

### resources/list_monad.v
- `From Coq Require Import ssrnat seq` → `From mathcomp Require Import ssreflect ssrnat seq` (MathComp 2.x)

## Summary of Results
- **21 examples fully compile** (base, base-thy, containers lib+theories, ghc lib+theories, transformers, graph/lib, compiler, coinduction, dlist, intervals, successors, rle, quicksort, lambda, simple, resources)
- **1 partial**: graph/theories (8/11, 3 need coq-equations)
- **1 partial**: shuffle/lib (2/5, missing Random Int instance)
- **3 blocked**: wc (needs coq-itree), core-semantics (GHC 9.10 API changes), shuffle/theories
- **3 N/A**: tip, locks, base-src (no buildable .v files in git)
