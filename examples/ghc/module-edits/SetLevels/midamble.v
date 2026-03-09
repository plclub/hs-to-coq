(* GHC 9.10: Eq instances needed by FloatOut.v *)
Definition Eq__LevelType_op_zeze (a b : LevelType) : bool :=
  match a, b with
  | BndrLvl, BndrLvl => true
  | JoinCeilLvl, JoinCeilLvl => true
  | _, _ => false
  end.

#[global]
Instance Eq__LevelType : GHC.Base.Eq_ LevelType :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq__LevelType_op_zeze ;
           GHC.Base.op_zsze____ := fun a b => negb (Eq__LevelType_op_zeze a b) |}.
