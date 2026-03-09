#[global] Instance Default_FloatBind : HsToCoq.Err.Default MkCore.FloatBind.
Admitted.

#[global] Instance Default_FloatInBind : HsToCoq.Err.Default FloatInBind :=
  HsToCoq.Err.Build_Default _ (FB HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
