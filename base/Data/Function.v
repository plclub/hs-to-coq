(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* No imports to convert. *)

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping definition `Data.Function.fix_' *)

#[global] Definition on {b : Type} {c : Type} {a : Type}
   : (b -> b -> c) -> (a -> b) -> a -> a -> c :=
  fun lop_ziztzi__ f => fun x y => lop_ziztzi__ (f x) (f y).

#[global] Definition op_za__ {a : Type} {b : Type} : a -> (a -> b) -> b :=
  fun x f => f x.

Notation "'_&_'" := (op_za__).

Infix "&" := (_&_) (at level 99).

Module Notations.
Notation "'_Data.Function.&_'" := (op_za__).
Infix "Data.Function.&" := (_&_) (at level 99).
End Notations.

(* External variables:
     Type
*)
