(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Prim.
Import GHC.Prim.Notations.

(* Converted type declarations: *)

Inductive EncodingTable : Type :=
  | EncodingTable : _GHC.Prim.Addr#_ -> EncodingTable.

(* Converted value declarations: *)

Axiom lowerTable : EncodingTable.

Axiom encode8_as_16h : EncodingTable ->
                       GHC.Word.Word8 -> GHC.Types.IO GHC.Word.Word16.

(* External variables:
     GHC.Prim.op_Addrzh__ GHC.Types.IO GHC.Word.Word16 GHC.Word.Word8
*)
