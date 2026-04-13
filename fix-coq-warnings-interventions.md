# Fix Coq Warnings — Interventions Log

No user interventions were needed during this task.

## Summary of changes

### hs-to-rocq code generator changes
1. **`src/lib/HsToRocq/Rocq/Gallina/Util.hs`**: Added `toExplicitBinder` function (converts implicit binders to explicit)
2. **`src/lib/HsToRocq/ConvertHaskell/Declarations/Instances.hs`**: Added `quantifyExplicit` and used it in both CPS record and simple class paths to avoid `fun {a : Type}` inside `{| ... |}`

### Manual/edit file fixes for "Require inside Module/Section"
3. **`examples/base-src/manual/GHC/Num.v`**: Moved `Require Export BinInt.` before `Module Notations.`
4. **`examples/base-src/module-edits/GHC/Base/midamble.v`**: Moved `Require String Ascii.` before `Module ManualNotations.`
5. **`examples/graph/theories/Path.v`**: Moved 8 `Require Import` statements from inside `Section Path` to top of file
6. **`examples/containers/theories/MapProofs/Bounds.v`**: Moved `Require Import Coq.Program.Tactics.` to top
7. **`examples/containers/theories/SetProofs.v`**: Moved 3 Require statements to top
8. **`examples/containers/theories/MapProofs/ToListProofs.v`**: Moved `Require Import Coq.Sorting.Sorted.` to top
9. **`examples/containers/theories/MapProofs/DeleteUpdateProofs.v`**: Moved `Require Import Coq.Classes.Morphisms.` to top
10. **`examples/containers/theories/MapProofs/UnionIntersectDifferenceProofs.v`**: Moved 3 Require statements to top
11. **`examples/containers/theories/MapProofs/TypeclassProofs.v`**: Moved 2 Require statements to top

### Manual/edit file fixes for "Ignoring implicit binder"
12. **`examples/base-src/manual/Data/Functor/Classes.v`**: Changed `fun {a : Type}` to `fun (a : Type)` in all record literal fields
13. **`examples/base-src/module-edits/Data/Foldable/midamble.v`**: Changed implicit/generalized binders to explicit in `default_foldable` helper functions
14. **`examples/ghc/manual/State.v`**: Changed `fun {a : Type}` to `fun (a : Type)` in record literal fields
15. **`examples/ghc/manual/NestedRecursionHelpers.v`**: Changed `forall {a}` to `forall a` in Ltac type pattern
16. **`examples/ghc/module-edits/UniqFM/midamble.v`**: Changed `fun {a} {b}` to `fun (a : Type) (b : Type)` in record literal
17. **`examples/ghc/module-edits/TrieMap/edits`**: Changed `fun {b}` to `fun b` in rewrite rules
18. **`examples/containers/theories/MapProofs/TypeclassProofs.v`**: Changed `fun {a}` to `fun (a : Type)` in record literal
