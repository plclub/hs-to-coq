(* Stub module for GHC.Builtin.Types.Prim *)
Require AxiomatizedTypes.
Require Core.

Axiom alphaTyVar : Core.Var.
Axiom runtimeRep1TyVar : Core.Var.
Axiom runtimeRep1Ty : AxiomatizedTypes.Type_.
Axiom addrPrimTy : AxiomatizedTypes.Type_.
Axiom mkTemplateTyVars : list AxiomatizedTypes.Kind -> list Core.Var.
