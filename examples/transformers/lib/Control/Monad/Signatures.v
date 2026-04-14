(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* No imports to convert. *)

(* Converted type declarations: *)

#[global] Definition Pass w m a :=
  (m (a * (w -> w))%type -> m a)%type.

#[global] Definition Listen w m a :=
  (m a -> m (a * w)%type)%type.

#[global] Definition CallCC m a b :=
  (((a -> m b) -> m a) -> m a)%type.

(* No value declarations to convert. *)

(* External variables:
     op_zt__
*)
