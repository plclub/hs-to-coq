(* Stub module for PrimOp *)
Require AxiomatizedTypes.

Definition PrimOp := AxiomatizedTypes.PrimOp.
Axiom tagToEnumKey : nat.
Axiom primOpIsCheap : PrimOp -> bool.
Axiom primOpIsWorkFree : PrimOp -> bool.
Axiom primOpOkForSpeculation : PrimOp -> bool.
Axiom primOpOkForSideEffects : PrimOp -> bool.
Axiom primOpOkToDiscard : PrimOp -> bool.
