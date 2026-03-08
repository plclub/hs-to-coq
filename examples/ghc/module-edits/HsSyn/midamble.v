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
