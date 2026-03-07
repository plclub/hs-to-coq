Require NestedRecursionHelpers.

(* default = emptyCSEnv *)
#[global] Instance Default__CSEnv : HsToCoq.Err.Default CSEnv := {| HsToCoq.Err.default := CS CoreSubst.emptySubst TrieMap.emptyCoreMap TrieMap.emptyCoreMap |}.
