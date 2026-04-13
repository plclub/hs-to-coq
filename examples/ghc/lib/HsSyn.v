(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require HsToRocq.Err.

(* Converted type declarations: *)

Inductive SrcUnpackedness : Type :=
  | SrcUnpack : SrcUnpackedness
  | SrcNoUnpack : SrcUnpackedness
  | NoSrcUnpack : SrcUnpackedness.

Inductive SrcStrictness : Type :=
  | SrcLazy : SrcStrictness
  | SrcStrict : SrcStrictness
  | NoSrcStrict : SrcStrictness.

Inductive Role : Type :=
  | Nominal : Role
  | Representational : Role
  | Phantom : Role.

#[global] Definition ConTag :=
  nat%type.

Inductive Boxity : Type := | Boxed : Boxity | Unboxed : Boxity.

Instance Default__SrcUnpackedness : HsToRocq.Err.Default SrcUnpackedness :=
  HsToRocq.Err.Build_Default _ SrcUnpack.

Instance Default__SrcStrictness : HsToRocq.Err.Default SrcStrictness :=
  HsToRocq.Err.Build_Default _ SrcLazy.

Instance Default__Role : HsToRocq.Err.Default Role :=
  HsToRocq.Err.Build_Default _ Nominal.

Instance Default__Boxity : HsToRocq.Err.Default Boxity :=
  HsToRocq.Err.Build_Default _ Boxed.

(* Midamble *)

Require FastString.
Require GHC.Base.

(* FieldLabelString is a newtype around FastString in GHC 9.10 *)
Definition FieldLabelString : Type := FastString.FastString.

(* GHC 9.10: Eq instance for Role needed by CoreUtils.mkCast *)
#[local] Definition Eq___Role_op_zeze__ : Role -> Role -> bool :=
  fun a b => match a, b with
    | Nominal, Nominal => true
    | Representational, Representational => true
    | Phantom, Phantom => true
    | _, _ => false
  end.

#[local] Definition Eq___Role_op_zsze__ : Role -> Role -> bool :=
  fun a b => negb (Eq___Role_op_zeze__ a b).

#[global]
Program Instance Eq___Role : GHC.Base.Eq_ Role :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Role_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Role_op_zsze__ |}.

(* Converted value declarations: *)

#[global] Definition isBoxed : Boxity -> bool :=
  fun arg_0__ => match arg_0__ with | Boxed => true | Unboxed => false end.

(* External variables:
     bool false nat true HsToRocq.Err.Build_Default HsToRocq.Err.Default
*)
