(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require HsToCoq.Err.

(* Converted type declarations: *)

#[global] Definition ConTag :=
  nat%type.

Inductive Boxity : Type := | Boxed : Boxity | Unboxed : Boxity.

Instance Default__Boxity : HsToCoq.Err.Default Boxity :=
  HsToCoq.Err.Build_Default _ Boxed.

(* Converted value declarations: *)

#[global] Definition isBoxed : Boxity -> bool :=
  fun arg_0__ => match arg_0__ with | Boxed => true | Unboxed => false end.

(* External variables:
     bool false nat true HsToCoq.Err.Build_Default HsToCoq.Err.Default
*)
