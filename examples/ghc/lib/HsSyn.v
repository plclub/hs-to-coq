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

Instance Default__SrcUnpackedness : HsToCoq.Err.Default SrcUnpackedness :=
  HsToCoq.Err.Build_Default _ SrcUnpack.

Instance Default__SrcStrictness : HsToCoq.Err.Default SrcStrictness :=
  HsToCoq.Err.Build_Default _ SrcLazy.

Instance Default__Role : HsToCoq.Err.Default Role :=
  HsToCoq.Err.Build_Default _ Nominal.

Instance Default__Boxity : HsToCoq.Err.Default Boxity :=
  HsToCoq.Err.Build_Default _ Boxed.

(* Midamble *)

Require FastString.

(* FieldLabelString is a newtype around FastString in GHC 9.10 *)
Definition FieldLabelString : Type := FastString.FastString.

(* Converted value declarations: *)

#[global] Definition isBoxed : Boxity -> bool :=
  fun arg_0__ => match arg_0__ with | Boxed => true | Unboxed => false end.

Require Import GHC.Base.

#[local] Definition eq_Role (a b : Role) : bool :=
  match a, b with
  | Nominal, Nominal => true
  | Representational, Representational => true
  | Phantom, Phantom => true
  | _, _ => false
  end.

#[global] Instance Eq___Role : Eq_ Role :=
  fun _ k__ => k__ {| op_zeze____ := eq_Role ;
                      op_zsze____ := fun a b => negb (eq_Role a b) |}.

#[local] Definition eq_Boxity (a b : Boxity) : bool :=
  match a, b with
  | Boxed, Boxed => true
  | Unboxed, Unboxed => true
  | _, _ => false
  end.

#[global] Instance Eq___Boxity : Eq_ Boxity :=
  fun _ k__ => k__ {| op_zeze____ := eq_Boxity ;
                      op_zsze____ := fun a b => negb (eq_Boxity a b) |}.

(* External variables:
     bool false nat true HsToCoq.Err.Build_Default HsToCoq.Err.Default
*)
