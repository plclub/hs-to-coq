Require NestedRecursionHelpers.

(* default = emptyCSEnv *)
Instance Default__CSEnv : HsToCoq.Err.Default CSEnv := {| HsToCoq.Err.default := CS CoreSubst.emptySubst TrieMap.emptyCoreMap TrieMap.emptyCoreMap |}.
