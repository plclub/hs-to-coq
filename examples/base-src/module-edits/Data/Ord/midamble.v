#[local] Definition Eq___Down_op_zeze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

#[local] Definition Eq___Down_op_zsze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

#[global] Program Instance Eq___Down {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Down a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Down_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Down_op_zsze__ |}.
