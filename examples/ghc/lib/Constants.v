(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require HsToRocq.Nat.

(* No imports to convert. *)

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping definition `Constants.hiVersion' *)

Axiom mAX_TUPLE_SIZE : nat.

Axiom mAX_CTUPLE_SIZE : nat.

Axiom mAX_SUM_SIZE : nat.

Axiom mAX_REDUCTION_DEPTH : nat.

Axiom mAX_SOLVER_ITERATIONS : nat.

Axiom mAX_QC_FUEL : nat.

Axiom mAX_WANTEDS_FUEL : nat.

Axiom mAX_GIVENS_FUEL : nat.

Axiom wORD64_SIZE : nat.

Axiom fLOAT_SIZE : nat.

Axiom dOUBLE_SIZE : nat.

Axiom tARGET_MAX_CHAR : nat.

(* External variables:
     nat
*)
