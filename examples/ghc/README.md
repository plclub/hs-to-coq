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

    make -C lib
    cd theories && coq_makefile -f _CoqProject -o Makefile && make -j

What's here
-----------

 * `ghc`: A pristine check-out of GHC (submodule, currently at 9.10.3)
 * `lib`: Generated Coq output from hs-to-coq translation
 * `theories`: Hand-written proofs about the generated code (28 files)
 * `Makefile`: Lists the modules to translate and their GHC 9.10 source paths
 * `edits`: Top level edit file
 * `axiomatize-types.edits`: Axiomatization of mutual type ball
 * `module-edits/*`: Per-module edits, `preamble.v` and `midamble.v`
 * `manual`: Hand-written versions of some modules
 * `ghc-head`: Modified GHC source files for translation

GHC 9.10 Notes
--------------

GHC 9.10 reorganized its module hierarchy. The Makefile maps old module
names to new GHC 9.10 source paths (e.g., `CoreSyn` → `GHC/Core.hs`,
`Var` → `GHC/Types/Var.hs`). The `edits` file uses `rename module`
directives to keep Coq output names unchanged.

Key API changes affecting theories:
 * `Alt` changed from tuple to `Mk_Alt` constructor
 * `Mk_Id` has 7 fields (added `varMult : Mult`)
 * `realUnique` type changed from `N` to `Unique`
 * `lookupIdSubst` no longer takes a `String` doc parameter
 * State monad uses bare function type (not newtype wrapper)
 * Several functions axiomatized (`substExpr`, `cseExpr`, `cseBind`)

Many theory proofs are `Admitted` pending further work to adapt to
GHC 9.10's changed definitions.
