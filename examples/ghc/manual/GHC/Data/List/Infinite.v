(* Stub module for GHC.Data.List.Infinite *)
Require HsToRocq.Err.

Axiom Infinite : Type -> Type.

Instance Default__Infinite {a} : HsToRocq.Err.Default (Infinite a). Admitted.
