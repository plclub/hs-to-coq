#[global] Instance Default_FloatBind : HsToRocq.Err.Default MkCore.FloatBind.
Admitted.

#[global] Instance Default_FloatInBind : HsToRocq.Err.Default FloatInBind :=
  HsToRocq.Err.Build_Default _ (FB HsToRocq.Err.default HsToRocq.Err.default HsToRocq.Err.default).
