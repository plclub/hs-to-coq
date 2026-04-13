(* ------------- VarEnv midamble.v ------------ *)
(* GHC 9.10: InScopeSet has 1 field (VarSet only, no nat counter) *)
#[global] Instance Default__InScopeSet : HsToRocq.Err.Default InScopeSet :=
  HsToRocq.Err.Build_Default _ (InScope HsToRocq.Err.default).
#[global] Instance Default__RnEnv2 : HsToRocq.Err.Default RnEnv2 :=
  HsToRocq.Err.Build_Default _ (RV2 HsToRocq.Err.default HsToRocq.Err.default HsToRocq.Err.default).
#[global] Instance Default__TidyEnv : HsToRocq.Err.Default TidyEnv :=
  HsToRocq.Err.Build_Default _ (pair HsToRocq.Err.default HsToRocq.Err.default).

