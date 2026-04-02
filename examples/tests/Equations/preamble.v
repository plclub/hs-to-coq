(* Stub for HsToCoq.Err since tests don't link against base *)
Module HsToCoq.
Module Err.
Class Default (a : Type) := Build_Default { default : a }.
End Err.
End HsToCoq.

(* Stub for GHC.Err.patternFailure — needed by guardFirst (incomplete guard pattern) *)
Module GHC.
Module Err.
Axiom patternFailure : forall {A : Type}, A.
End Err.
End GHC.
