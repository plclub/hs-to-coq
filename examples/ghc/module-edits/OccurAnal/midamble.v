(* GHC 9.10: Default instances that depend on TailUsageDetails/WithTailUsageDetails.
   Must be in midamble because auto-generated defaults come before midamble,
   but these need types defined after the auto-generated defaults.
   With skip directives, the problematic auto-generated instances are removed. *)

#[global] Instance Default__TailUsageDetails : HsToCoq.Err.Default TailUsageDetails :=
  HsToCoq.Err.Build_Default _ (TUD HsToCoq.Err.default HsToCoq.Err.default).

#[global] Instance Default__WithTailUsageDetails {a} `{HsToCoq.Err.Default a}
  : HsToCoq.Err.Default (WithTailUsageDetails a) :=
  HsToCoq.Err.Build_Default _ (WTUD HsToCoq.Err.default HsToCoq.Err.default).

#[global] Instance Default__LocalOcc : HsToCoq.Err.Default LocalOcc :=
  HsToCoq.Err.Build_Default _ (OneOccL HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

#[global] Instance Default__NodeDetails : HsToCoq.Err.Default NodeDetails :=
  HsToCoq.Err.Build_Default _ (ND HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
