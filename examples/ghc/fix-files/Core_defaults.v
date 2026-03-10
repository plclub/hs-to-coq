Definition RuleBase := (NameEnv.NameEnv (list CoreRule))%type.

Axiom RuleEnv : Type.

#[global] Instance Default__TyFamEqnValidityInfo : HsToCoq.Err.Default TyFamEqnValidityInfo. Admitted.

#[global] Instance Default__AlgTyConRhs : HsToCoq.Err.Default AlgTyConRhs. Admitted.

#[global] Instance Default__TyConDetails : HsToCoq.Err.Default TyConDetails. Admitted.

#[global] Instance Default__TyCon : HsToCoq.Err.Default TyCon. Admitted.

#[global] Instance Default__DmdType : HsToCoq.Err.Default DmdType. Admitted.

#[global] Instance Default__IdInfo : HsToCoq.Err.Default IdInfo. Admitted.

#[global] Instance Default__Var : HsToCoq.Err.Default Var. Admitted.

#[global] Instance Default__DataCon : HsToCoq.Err.Default DataCon. Admitted.

#[global] Instance Default__CoreRule : HsToCoq.Err.Default CoreRule. Admitted.

#[global] Instance Default__RuleEnv : HsToCoq.Err.Default RuleEnv. Admitted.

