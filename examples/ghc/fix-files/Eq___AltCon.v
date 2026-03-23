
#[local] Definition Eq___AltCon_op_zeze__ : AltCon -> AltCon -> bool :=
  fun a b => match a, b with
    | DataAlt dc1, DataAlt dc2 => dc1 GHC.Base.== dc2
    | LitAlt l1, LitAlt l2 => l1 GHC.Base.== l2
    | DEFAULT, DEFAULT => true
    | _, _ => false
  end.

#[local] Definition Eq___AltCon_op_zsze__ : AltCon -> AltCon -> bool :=
  fun a b => negb (Eq___AltCon_op_zeze__ a b).

#[global]
Program Instance Eq___AltCon : GHC.Base.Eq_ AltCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___AltCon_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___AltCon_op_zsze__ |}.
