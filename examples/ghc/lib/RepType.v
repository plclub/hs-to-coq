(* Stub module for RepType / GHC.StgToCmm.RepType *)
Require AxiomatizedTypes.

Axiom isZeroBitTy : AxiomatizedTypes.Type_ -> bool.
Axiom PrimRep : Type.
Axiom typePrimRep : AxiomatizedTypes.Type_ -> list PrimRep.
