Require NestedRecursionHelpers.

(* default = emptyCSEnv *)
#[global] Instance Default__CSEnv : HsToRocq.Err.Default CSEnv := {| HsToRocq.Err.default := CS Core.emptySubst GHC.Core.Map.Expr.emptyCoreMap GHC.Core.Map.Expr.emptyCoreMap |}.
