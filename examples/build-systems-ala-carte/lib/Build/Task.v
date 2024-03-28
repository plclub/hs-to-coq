(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* No imports to convert. *)

(* Converted type declarations: *)

Inductive Task (c : (Type -> Type) -> Type) (k : Type) (v : Type) : Type :=
  | Mk_Task (run : forall {f}, forall `{c f}, (k -> f v) -> f v) : Task c k v.

Definition Tasks c k v :=
  (k -> option (Task c k v))%type.

Arguments Mk_Task {_} {_} {_} _.

Definition run {c : (Type -> Type) -> Type} {k : Type} {v : Type} (arg_0__
    : Task c k v) :=
  let 'Mk_Task run := arg_0__ in
  run.

(* No value declarations to convert. *)

(* Skipping definition `Build.Task.compose' *)

(* Skipping definition `Build.Task.liftTask' *)

(* Skipping definition `Build.Task.liftTasks' *)

(* External variables:
     Type option
*)
