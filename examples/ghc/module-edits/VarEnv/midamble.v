(* ------------- VarEnv midamble.v ------------ *)
(* GHC 9.10: InScopeSet has 1 field (VarSet only, no nat counter) *)
#[global] Instance Default__InScopeSet : HsToCoq.Err.Default InScopeSet :=
  HsToCoq.Err.Build_Default _ (InScope HsToCoq.Err.default).
#[global] Instance Default__RnEnv2 : HsToCoq.Err.Default RnEnv2 :=
  HsToCoq.Err.Build_Default _ (RV2 HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
#[global] Instance Default__TidyEnv : HsToCoq.Err.Default TidyEnv :=
  HsToCoq.Err.Build_Default _ (pair HsToCoq.Err.default HsToCoq.Err.default).

