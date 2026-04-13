(* GHC 9.10: Default instances that depend on TailUsageDetails/WithTailUsageDetails.
   Must be in midamble because auto-generated defaults come before midamble,
   but these need types defined after the auto-generated defaults.
   With skip directives, the problematic auto-generated instances are removed. *)

#[global] Instance Default__TailUsageDetails : HsToRocq.Err.Default TailUsageDetails :=
  HsToRocq.Err.Build_Default _ (TUD HsToRocq.Err.default HsToRocq.Err.default).

#[global] Instance Default__WithTailUsageDetails {a} `{HsToRocq.Err.Default a}
  : HsToRocq.Err.Default (WithTailUsageDetails a) :=
  HsToRocq.Err.Build_Default _ (WTUD HsToRocq.Err.default HsToRocq.Err.default).

#[global] Instance Default__LocalOcc : HsToRocq.Err.Default LocalOcc :=
  HsToRocq.Err.Build_Default _ (OneOccL HsToRocq.Err.default HsToRocq.Err.default HsToRocq.Err.default).

#[global] Instance Default__NodeDetails : HsToRocq.Err.Default NodeDetails :=
  HsToRocq.Err.Build_Default _ (ND HsToRocq.Err.default HsToRocq.Err.default HsToRocq.Err.default HsToRocq.Err.default HsToRocq.Err.default HsToRocq.Err.default).
