(* Stub module for GHC.Core.TyCo.FVs *)
Require AxiomatizedTypes.
Require Core.
Require FV.

Axiom tyCoFVsOfType : AxiomatizedTypes.Type_ -> FV.FV.
Axiom tyCoFVsOfTypes : list AxiomatizedTypes.Type_ -> FV.FV.
Axiom tyCoFVsOfCo : AxiomatizedTypes.Coercion -> FV.FV.
Axiom tyCoVarsOfTypeDSet : AxiomatizedTypes.Type_ -> Core.DTyCoVarSet.
Axiom tyCoVarsOfCoDSet : AxiomatizedTypes.Coercion -> Core.DTyCoVarSet.
Axiom tyCoVarsOfType : AxiomatizedTypes.Type_ -> Core.TyCoVarSet.
Axiom tyCoVarsOfTypes : list AxiomatizedTypes.Type_ -> Core.TyCoVarSet.
Axiom tyCoVarsOfCo : AxiomatizedTypes.Coercion -> Core.TyCoVarSet.
Axiom occCheckExpand : list Core.Var -> AxiomatizedTypes.Type_ -> option AxiomatizedTypes.Type_.
Axiom noFreeVarsOfType : AxiomatizedTypes.Type_ -> bool.
Axiom coVarsOfCo : AxiomatizedTypes.Coercion -> Core.CoVarSet.
Axiom coVarsOfType : AxiomatizedTypes.Type_ -> Core.CoVarSet.
Axiom tyCoVarsOfMCo : Core.MCoercionN -> Core.TyCoVarSet.
