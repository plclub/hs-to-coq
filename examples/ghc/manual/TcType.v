(* Stub module for TcType — provides ConcreteTyVars *)
Require HsToRocq.Err.

Axiom ConcreteTyVars : Type.
Axiom noConcreteTyVars : ConcreteTyVars.

#[global] Instance Default__ConcreteTyVars : HsToRocq.Err.Default ConcreteTyVars. Admitted.
