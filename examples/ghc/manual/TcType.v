(* Stub module for TcType — provides ConcreteTyVars *)
Require HsToCoq.Err.

Axiom ConcreteTyVars : Type.
Axiom noConcreteTyVars : ConcreteTyVars.

#[global] Instance Default__ConcreteTyVars : HsToCoq.Err.Default ConcreteTyVars. Admitted.
