Require NestedRecursionHelpers.

(* default = emptyCSEnv *)
#[global] Instance Default__CSEnv : HsToCoq.Err.Default CSEnv := {| HsToCoq.Err.default := CS Core.emptySubst GHC.Core.Map.Expr.emptyCoreMap GHC.Core.Map.Expr.emptyCoreMap |}.
