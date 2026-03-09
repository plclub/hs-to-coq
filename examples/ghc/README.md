Coqified GHC Core
=================

This directory contains a Coq translation of key GHC compiler modules
(core language, optimization passes, utility types), generated from
**GHC 9.10.3** using hs-to-coq with **Coq 8.20**.

Compilation
-----------

This directory depends on GHC's `base` and `containers` libraries. Before
compiling here make sure those libraries have already been compiled.

    make -C ../../base
    make -C ../containers

Then build the generated library and theory proofs:

    make                # regenerates lib/*.v and compiles them
    cd theories && coq_makefile -f _CoqProject -o Makefile && make -j

Or from scratch:

    make clean && make  # full clean rebuild of lib/
    cd theories && coq_makefile -f _CoqProject -o Makefile && make -j

What's here
-----------

 * `ghc`: A pristine check-out of GHC (submodule, currently at 9.10.3)
 * `lib`: Generated Coq output — symlinks to `manual/` for hand-written
   modules, generated `.v` files for translated modules
 * `theories`: Hand-written proofs about the generated code (28 files)
 * `Makefile`: Lists the modules to translate and their GHC 9.10 source paths
 * `edits`: Top level edit file (includes `rename module` directives)
 * `axiomatize-types.edits`: Axiomatization of mutual type ball
   (Type, Coercion, TyCon, DataCon, etc.)
 * `module-edits/*`: Per-module edits, `preamble.v` and `midamble.v`
 * `manual`: Hand-written Coq modules (~60 files) for axiomatized types,
   GHC 9.10 stubs, and modules that can't be auto-generated
 * `ghc-head`: Modified GHC source files used instead of the submodule source
 * `deps`: Per-module Makefile dependency fragments

Translated modules
------------------

**Utilities** (10): Util, SrcLoc, Unique, UniqSupply, HsSyn, BasicTypes,
DynFlags, Panic, OccName, Module

**Data structures** (11): Bag, EnumSet, BooleanFormula, UniqFM, UniqSet,
OrdList, FiniteMap, ListSetOps, Pair, Maybes, MonadUtils

**Core type ball** (12, compiled into `Core.v`): IdInfo, Class, TyCon,
DataCon, PatSyn, Var, VarSet, VarEnv, CoreSyn, Demand, Type, TyCoRep,
Coercion

**Core modules** (13): FastStringEnv, Constants, Id, CoreSubst, PrelNames,
CoreUtils, Name, NameEnv, NameSet, FV, Literal, FieldLabel, CoreFVs,
Exitify

**Extras** (15): TrieMap, CSE, CoreStats, UnVarGraph, CoreArity, CoreTidy,
CallArity, CoAxiom, TysWiredIn, MkCore, Digraph, SetLevels, CoreMonad,
OccurAnal, FloatIn, FloatOut

**Hand-written** (~60): AxiomatizedTypes, State, ConLike, Outputable,
PrimOp, RepType, GHC/Core/TyCo/Subst, GHC/Core/Multiplicity, and many
GHC 9.10 stub modules (see `HANDMOD` in Makefile)

Theory proofs (28 files)
------------------------

All 28 theory files compile. Many proofs are `Admitted` due to GHC 9.10
API changes (axiomatized types and functions).

| File | Status | Notes |
|------|--------|-------|
| Axioms.v | Compiles | Axioms about uniqAway, VarSets; some removed (initExitJoinUnique, idJoinPointHood) |
| Base.v | Compiles | |
| ContainerProofs.v | Compiles | |
| Core.v | Compiles | |
| CoreFVs.v | Compiles | |
| CoreInduct.v | Compiles | `CoreLT_collectNBinders` Admitted (error_sub removed) |
| CoreSemantics.v | Compiles | subst_expr'/subst_ok removed (substExpr axiomatized) |
| CoreStats.v | Compiles | |
| CoreSubst.v | Compiles | Many proofs Admitted (Subst type axiomatized, can't pattern-match Mk_Subst) |
| CSE.v | Compiles | All proofs Admitted (cseExpr/cseBind axiomatized) |
| Exitify.v | Compiles | exitifyRec_WellScoped/JPI Admitted (exitifyRec axiomatized) |
| Forall.v | Compiles | |
| FV.v | Compiles | |
| GhcTactics.v | Compiles | |
| GhcUtils.v | Compiles | |
| JoinPointInvariants.v | Compiles | |
| OrdList.v | Compiles | |
| ScopeInvariant.v | Compiles | |
| StateLogic.v | Compiles | Rewritten for bare function type State monad |
| TrieMap.v | Compiles | |
| Unique.v | Compiles | |
| UniqSetInv.v | Compiles | |
| Var.v | Compiles | isJoinId lemmas Admitted (idJoinPointHood skipped) |
| VarEnv.v | Compiles | |
| VarSet.v | Compiles | |
| VarSetFSet.v | Compiles | |
| VarSetStrong.v | Compiles | |
| Util.v | Compiles | |

GHC 9.10 migration details
---------------------------

### Module reorganization

GHC 9.10 reorganized its module hierarchy (e.g., `CoreSyn` →
`GHC.Core`, `Var` → `GHC.Types.Var`). The Makefile has explicit
`SRCPATH_*` mappings for each module. The `edits` file uses
`rename module` directives to keep Coq output names unchanged.

### Key API changes

 * **Alt type**: Changed from tuple `(AltCon * list Var * Expr Var)` to
   algebraic `Mk_Alt` constructor. Theory intro patterns changed from
   `[[dc pats] rhs]` to `[dc pats rhs]`.
 * **Mk_Id fields**: 7 fields (added `varMult : Mult` as 4th). Pattern
   matches need an extra wildcard.
 * **realUnique type**: `N` → `Unique`. Breaks proofs using `N.eqb_*`.
 * **lookupIdSubst**: No longer takes `String` doc parameter.
 * **State monad**: Bare function type `s -> (a * s)`, not newtype wrapper.
 * **Var type**: Single constructor `Mk_Id` only (no TyVar/TcTyVar).
 * **Subst type**: Moved to `GHC.Core.TyCo.Subst`, axiomatized (can't
   pattern-match `Mk_Subst`).

### Axiomatized functions

These functions are declared as `Axiom` in lib/ and cannot be unfolded
in proofs:
 * `substExpr`, `substBind` (CoreSubst)
 * `cseExpr`, `cseBind`, `try_for_cse`, `cse_bind` (CSE)
 * `exitifyRec` (Exitify)
 * `floatExpr`, `floatBind`, `floatRhs` (FloatOut)
 * `fiExpr`, `fiBinds`, `fiRhs`, `floatIsCase` (FloatIn)
 * `Id.idJoinPointHood` (skipped — uses Outputable.JoinPointHood)
 * All of OccurAnal (axiomatized module)

### Makefile post-processing

The Makefile applies `sed` fixes to generated `.v` files:
 * **UniqFM.v**: Removes phantom kind parameters from `UniqFM`
 * **BasicTypes.v**: Makes all `Default__*` instances `#[global]`
 * **Core.v**: Extensive fixes for the mutual type ball (inserts ConLike
   type definition, fixes imports, removes circular dependencies)
 * **Var-related**: Removes redundant wildcard branches for single-constructor types
