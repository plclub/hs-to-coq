Require Import HsToRocq.Err.
Require Import Coq.NArith.BinNat.

#[global] Instance Default__OccName : Default OccName :=
    Build_Default _ (Mk_OccName default default).

(* GHC 9.10: FldName constructor added - need manual Eq instance *)
#[local] Definition Eq__NameSpace_op_zeze : NameSpace -> NameSpace -> bool :=
  fun x y => match x, y with
    | VarName, VarName => true
    | FldName a, FldName b => (a GHC.Base.== b)
    | DataName, DataName => true
    | TvName, TvName => true
    | TcClsName, TcClsName => true
    | _, _ => false
  end.

#[global]
Instance Eq___NameSpace : GHC.Base.Eq_ NameSpace :=
  fun _ k => k {|
    GHC.Base.op_zeze____ := Eq__NameSpace_op_zeze ;
    GHC.Base.op_zsze____ := fun x y => negb (Eq__NameSpace_op_zeze x y)
  |}.

(* GHC 9.10: Uniquable__NameSpace references GHC.Builtin.Uniques - provide stub *)
#[global]
Instance Uniquable__NameSpace : Unique.Uniquable NameSpace :=
  fun _ k => k {|
    Unique.getUnique__ := fun ns => match ns with
      | VarName   => Unique.mkUniqueGrimily 1%N
      | FldName _ => Unique.mkUniqueGrimily 2%N
      | DataName  => Unique.mkUniqueGrimily 3%N
      | TvName    => Unique.mkUniqueGrimily 4%N
      | TcClsName => Unique.mkUniqueGrimily 5%N
    end
  |}.
