(* Stub module for GHC.Core.TyCo.Tidy *)
Require AxiomatizedTypes.
Require Core.

Axiom tidyType : Core.TidyEnv -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.
Axiom tidyCo : Core.TidyEnv -> AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.
Axiom tidyVarBndr : Core.TidyEnv -> Core.Var -> (Core.TidyEnv * Core.Var)%type.
