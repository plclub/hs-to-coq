#[global] Instance Default__Unique : HsToCoq.Err.Default Unique
  := HsToCoq.Err.Build_Default _ (MkUnique HsToCoq.Err.default).

#[global] Program Instance Uniquable__Word : Uniquable GHC.Num.Word :=
  fun _ k => k {| getUnique__ x := MkUnique x |}.

