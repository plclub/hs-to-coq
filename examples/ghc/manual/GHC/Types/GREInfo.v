(* Stub for GHC.Types.GREInfo — new in GHC 9.10 *)

Require Import GHC.Base.
Require Import Name.
Require Import FieldLabel.

(* Types used by ConLike *)
Axiom ConLikeName : Type.
Axiom ConInfo : Type.

Axiom DataConName : Name.Name -> ConLikeName.
Axiom PatSynName : Name.Name -> ConLikeName.
Axiom mkConInfo : nat -> list FieldLabel.FieldLabel -> ConInfo.
