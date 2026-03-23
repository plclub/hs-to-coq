(* Stub module for GHC.Core.FamInstEnv *)
Require AxiomatizedTypes.

Axiom FamInstEnvs : Type.
Axiom topNormaliseType_maybe : FamInstEnvs -> AxiomatizedTypes.Type_ -> option (AxiomatizedTypes.Coercion * AxiomatizedTypes.Type_)%type.
