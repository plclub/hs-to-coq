Definition RuleBase := (NameEnv.NameEnv (list CoreRule))%type.

Axiom RuleEnv : Type.

#[global] Instance Default__TyFamEqnValidityInfo : HsToRocq.Err.Default TyFamEqnValidityInfo. Admitted.

#[global] Instance Default__AlgTyConRhs : HsToRocq.Err.Default AlgTyConRhs. Admitted.

#[global] Instance Default__TyConDetails : HsToRocq.Err.Default TyConDetails. Admitted.

#[global] Instance Default__TyCon : HsToRocq.Err.Default TyCon. Admitted.

#[global] Instance Default__DmdType : HsToRocq.Err.Default DmdType. Admitted.

#[global] Instance Default__IdInfo : HsToRocq.Err.Default IdInfo. Admitted.

#[global] Instance Default__Var : HsToRocq.Err.Default Var. Admitted.

#[global] Instance Default__DataCon : HsToRocq.Err.Default DataCon. Admitted.

#[global] Instance Default__CoreRule : HsToRocq.Err.Default CoreRule. Admitted.

#[global] Instance Default__RuleEnv : HsToRocq.Err.Default RuleEnv. Admitted.

