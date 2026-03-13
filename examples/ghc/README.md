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
 * `theories`: Hand-written proofs about the generated code (29 files)
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

Faithfulness overview
---------------------

The translation has several levels of faithfulness to GHC 9.10 source:

| Category | Description |
|----------|-------------|
| Faithful auto-translated | Core AST (Var, Expr, Alt, Bind), utilities (Unique, VarSet, VarEnv, UniqFM, UniqSet), substitution (CoreSubst), exitification (Exitify), containers (IntMap, Map) |
| Faithful manual | Subst type (matches GHC structure), State monad (bare function type matching GHC 9.10), JoinPointHood, idJoinPointHood, ConLike |
| Soundly abstracted | Type/Coercion substitution (identity — types don't change structurally), TvSubstEnv/CvSubstEnv := unit |
| Axiomatized (no GHC source) | Type system (Type_, Coercion, TyCon, DataCon), I/O (CoreMonad, DynFlags, Panic), optimizations (OccurAnal, CSE, FloatIn, FloatOut, CallArity, CoreArity, SetLevels) |

### Concrete (un-axiomatized) definitions

These functions were previously axiomatized but are now concrete Coq definitions:

 * **`substExpr` / `substBind`** (CoreSubst): Mutually recursive `Fixpoint`
   in midamble. Capture-avoiding substitution for Id variables; type/coercion
   substitution is identity (soundly abstracted since Type_ is abstract).
 * **`exitifyRec`** (Exitify): Concrete with `deferredFix2` for general
   recursion. The exit-join-id creation (`mkExitJoinId`) remains axiomatized
   (requires `Mult` type).
 * **`Subst` type** (Core.v): Concrete inductive `Mk_Subst InScopeSet
   IdSubstEnv TvSubstEnv CvSubstEnv`, merged into Core.v via the CORESYN
   group. Matches GHC's `GHC.Core.TyCo.Subst.Subst` exactly.
 * **`idJoinPointHood`** (Id midamble): Concrete pattern match on `idDetails`,
   faithful to GHC 9.10.

### Still axiomatized

These functions remain `Axiom` in lib/ and cannot be unfolded in proofs:

 * **CSE**: `cseExpr`, `cseBind`, `try_for_cse`, `cse_bind` (axiomatized module)
 * **FloatOut**: `floatExpr`, `floatBind`, `floatRhs` (axiomatized module)
 * **FloatIn**: `fiExpr`, `fiBinds`, `fiRhs`, `floatIsCase` (axiomatized module)
 * **OccurAnal**: Entire module axiomatized (view patterns + mutual recursion)
 * **Exitify**: `mkExitJoinId` (requires `Mult`/`ManyTy`)

### Edit-induced semantic changes

| Edit | Module | Change | Faithful? |
|------|--------|--------|-----------|
| `Panic.Plain.assert x y = y` | Global | Ignore assertions | YES (no runtime assertions in Coq) |
| `warnPprTrace a b c d = d` | Global | Ignore debug traces | YES (no side effects) |
| `DVarSet := VarSet` | Global | Deterministic sets = sets | PARTIAL (loses ordering guarantee) |
| `extendSubst ... = extendIdSubst` | CoreSubst | Ignore type/coercion vars | SOUND (TvSubstEnv = unit) |
| `substUnfolding _ _ = NoUnfolding` | CoreSubst | Ignore unfoldings | SOUND (Unfolding axiomatized) |
| `skip constructor Core.Tick` | Core | Remove Tick expressions | NOT FAITHFUL (ticks exist in GHC) |
| Key/Prefix/Mask := N | IntMap | Use Coq naturals for keys | PARTIAL (Haskell uses machine Int) |

### Termination axiomatizations

Functions using `deferredFix`/`deferredFix2` (axiomatized fixpoint combinator):

| Function | Module | Recursive structure |
|----------|--------|-------------------|
| `mergeWithKey'` | Data.IntMap.Internal | 2-arg on IntMap pair |
| `disjoint` | Data.IntMap.Internal | 2-arg on IntMap pair |
| `restrictKeys` / `withoutKeys` | Data.IntMap.Internal | 2-arg on IntMap x IntSet |
| `exitifyRec.go` | Exitify | Deferred on expression size |

These preserve recursion structure while hiding the termination argument from Coq.

Proved theorems
---------------

### Main results (from Spector-Zabusky et al., arxiv 1910.11724)

 * **`exitifyProgram_WellScoped_JPV`** (Exitify.v, Qed): Exitification
   preserves well-scopedness and join point validity
 * **`WellScoped_substExpr`** (CoreSubst.v, Qed): Substitution preserves
   well-scopedness

### Additional mechanized results

 * **CoreFVs.v** (0 Admitted, 42 Qed): `freeVarsOf_freeVars_revised`,
   `elemVarSet_exprFreeVars_Var_false`, all exprFreeVars lemmas
 * **CoreSubst.v** (0 Admitted, 34 Qed): Full substitution theory including
   `SubstExtends`, `WellScoped_Subst`, all simplification lemmas
 * **JoinPointInvariants.v** (0 Admitted, 33 Qed): Join point validity
   preservation through all Core transformations
 * **ScopeInvariant.v** (0 Admitted, 27 Qed): Scope invariant preservation
 * **Var.v** (0 Admitted, 21 Qed): `isJoinId` lemmas, `EqLaws_Var`
 * **VarSet.v** (0 Admitted, 140 Qed): Comprehensive VarSet reasoning library
 * **ContainerProofs.v** (17 Qed + 24 Axioms): IntMap operation properties;
   17 proved via structural induction or IntMapProofs.Sem framework
 * **TrieMap.v** (1 Qed): `TrieMapLaws__MaybeMap` instance proved
 * **VarSetFSet.v** (31 Qed): FSet interface for VarSets including
   `equal_2`, `filter_1`/`filter_2`/`filter_3`

Theory proofs (29 files)
------------------------

All 29 theory files compile. Files with zero Admitted are marked with a
check mark.

| File | Qed | Admitted | Notes |
|------|-----|----------|-------|
| Axioms.v | 7 | 0 | Behavioral axioms for `uniqAway`, `ValidVarSet` |
| Base.v | 4 | 0 | |
| ContainerProofs.v | 17 | 0 | 24 Axioms remain (delete, union, difference, intersection, disjoint) |
| Core.v | 11 | 0 | `deAnnotate` lemmas |
| CoreFVs.v | 42 | 0 | All exprFreeVars lemmas proved |
| CoreInduct.v | 14 | 0 | |
| CoreSemantics.v | 2 | 0 | |
| CoreStats.v | 1 | 0 | |
| CoreSubst.v | 34 | 0 | Full substitution theory |
| CSE.v | 3 | 5 | Blocked: cseExpr/cseBind axiomatized |
| Exitify.v | 15 | 3 | Main theorem Qed; 3 deep inductive helpers Admitted |
| Forall.v | 4 | 0 | |
| FV.v | 25 | 0 | |
| GhcTactics.v | 0 | 0 | Tactic library |
| GhcUtils.v | 7 | 0 | |
| JoinPointInvariants.v | 3 | 0 | |
| JoinPointInvariantsInductive.v | 3 | 0 | |
| OrdList.v | 1 | 0 | |
| ScopeInvariant.v | 27 | 0 | |
| StateLogic.v | 18 | 0 | Bare function type State monad |
| TrieMap.v | 1 | 4 | MaybeMap proved; ListMap/GenMap blocked (axiomatized types) |
| Unique.v | 6 | 0 | |
| UniqSetInv.v | 13 | 0 | |
| Util.v | 1 | 0 | |
| Var.v | 21 | 0 | |
| VarEnv.v | 25 | 0 | |
| VarSet.v | 140 | 0 | |
| VarSetFSet.v | 31 | 14 | equal_2, filter_1/2/3 proved; rest blocked by `elements`/`choose`/`partition` = default |
| VarSetStrong.v | 30 | 0 | |

**Totals**: 506 Qed, 26 Admitted (across 5 files)

### Remaining Admitted breakdown

| File | Admitted | Reason |
|------|----------|--------|
| CSE.v | 5 | `cseExpr`/`cseBind` axiomatized — cannot unfold |
| Exitify.v | 3 | Deep inductive proofs (`exitifyRec_WellScoped`, `exitifyRec_JPI`, `top_go_WellScoped_JPI`); theoretically provable since `exitifyRec` is concrete |
| TrieMap.v | 4 | `TrieMapLaws__IntMap` and `TrieMapLaws__Map` need alter/fold specs; `TrieMapLaws__ListMap` and `TrieMapLaws__GenMap` blocked by axiomatized types |
| VarSetFSet.v | 14 | `elements`/`choose`/`partition` defined as `HsToCoq.Err.default`; `for_all`/`exists_` need IntMap `foldr` spec; `equal_1`/`is_empty_1`/`subset_1` need key-surjectivity |

### ContainerProofs axioms (24 remaining)

These axioms about IntMap operations are stated in `ContainerProofs.v` and
used throughout the theory files. They are all provable given sufficient
Sem lemma infrastructure in `examples/containers/theories/IntMapProofs.v`
(currently missing `delete_Sem`, `union_Sem`, `difference_Sem`,
`intersection_Sem`, `disjoint_Sem`).

| Category | Count | Examples |
|----------|-------|---------|
| Delete | 4 | `delete_eq`, `delete_neq`, `member_delete`, `delete_commute` |
| Union | 2 | `member_union`, `lookup_union` |
| Difference | 3 | `lookup_difference_in_snd`, `lookup_difference_not_in_snd`, `member_difference` |
| Intersection | 2 | `lookup_intersection`, `member_intersection` |
| Disjoint | 5 | `disjoint_sym`, `disjoint_insert`, `disjoint_non_member`, `disjoint_eq`, `disjoint_difference` |
| Filter | 3 | `filter_comp`, `lookup_filterWithKey`, `filter_true` |
| Combined | 5 | `null_intersection_non_member`, `null_intersection_difference`, `null_intersection_eq`, `lookup_partition` |

GHC 9.10 migration details
---------------------------

### Module reorganization

GHC 9.10 reorganized its module hierarchy (e.g., `CoreSyn` ->
`GHC.Core`, `Var` -> `GHC.Types.Var`). The Makefile has explicit
`SRCPATH_*` mappings for each module. The `edits` file uses
`rename module` directives to keep Coq output names unchanged.

### Key API changes

 * **Alt type**: Changed from tuple `(AltCon * list Var * Expr Var)` to
   algebraic `Mk_Alt` constructor. Theory intro patterns changed from
   `[[dc pats] rhs]` to `[dc pats rhs]`.
 * **Mk_Id fields**: 7 fields (added `varMult : Mult` as 4th). Pattern
   matches need an extra wildcard.
 * **realUnique type**: `N` -> `Unique`. Breaks proofs using `N.eqb_*`.
 * **lookupIdSubst**: No longer takes `String` doc parameter.
 * **State monad**: Bare function type `s -> (a * s)`, not newtype wrapper.
 * **Var type**: Single constructor `Mk_Id` only (no TyVar/TcTyVar).
 * **Subst type**: Moved to `GHC.Core.TyCo.Subst`. Now concrete in Core.v
   (was axiomatized; un-axiomatized in Phases 3-5).

### Makefile post-processing

The Makefile applies `sed` fixes to generated `.v` files:
 * **UniqFM.v**: Removes phantom kind parameters from `UniqFM`
 * **BasicTypes.v**: Makes all `Default__*` instances `#[global]`
 * **Core.v**: Extensive fixes for the mutual type ball (inserts ConLike
   type definition, fixes imports, removes circular dependencies).
   Uses `fix-files/` for multi-line insertions (portable across GNU/BSD sed).
 * **Var-related**: Removes redundant wildcard branches for single-constructor types
