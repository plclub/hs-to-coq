#[global] Instance Default__Unique : HsToRocq.Err.Default Unique
  := HsToRocq.Err.Build_Default _ (MkUnique HsToRocq.Err.default).

#[global] Program Instance Uniquable__Word : Uniquable GHC.Num.Word :=
  fun _ k => k {| getUnique__ x := MkUnique x |}.

