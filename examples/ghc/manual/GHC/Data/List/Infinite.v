(* Stub module for GHC.Data.List.Infinite *)
Require HsToCoq.Err.

Axiom Infinite : Type -> Type.

Instance Default__Infinite {a} : HsToCoq.Err.Default (Infinite a). Admitted.
