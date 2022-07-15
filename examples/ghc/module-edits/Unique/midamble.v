Instance Default__Name : HsToCoq.Err.Default Unique
  := HsToCoq.Err.Build_Default _ (MkUnique HsToCoq.Err.default).

Program Instance Uniquable__Word : Uniquable GHC.Num.Word :=
  fun _ k => k {| getUnique__ x := MkUnique x |}.

