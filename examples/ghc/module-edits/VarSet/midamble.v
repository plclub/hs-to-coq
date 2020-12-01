(*
Definition DVarSet :=
  (UniqSetInv.UniqSet Var)%type.

Definition CoVarSet :=
  (UniqSetInv.UniqSet CoVar)%type.

Definition DIdSet :=
  (UniqSetInv.UniqSet Id)%type.

Definition IdSet :=
  (UniqSetInv.UniqSet Id)%type.

Definition DTyCoVarSet :=
  (UniqSetInv.UniqSet TyCoVar)%type.

Definition TyCoVarSet :=
  (UniqSetInv.UniqSet TyCoVar)%type.

Definition TyVarSet :=
  (UniqSetInv.UniqSet TyVar)%type.

Definition VarSet :=
  (UniqSetInv.UniqSet Var)%type.

Inductive InScopeSet : Type := | InScope : VarSet -> nat -> InScopeSet.

Definition InScopeEnv :=
  (InScopeSet * IdUnfoldingFun)%type%type.


Definition RuleFun :=
  (DynFlags.DynFlags ->
   InScopeEnv -> Id -> list CoreExpr -> option CoreExpr)%type.

Inductive CoreRule : Type
  := | Rule (ru_name : BasicTypes.RuleName) (ru_act : BasicTypes.Activation)
  (ru_fn : Name.Name) (ru_rough : list (option Name.Name)) (ru_bndrs
    : list CoreBndr) (ru_args : list CoreExpr) (ru_rhs : CoreExpr) (ru_auto : bool)
  (ru_origin : Module.Module) (ru_orphan : IsOrphan) (ru_local : bool)
   : CoreRule
  |  BuiltinRule (ru_name : BasicTypes.RuleName) (ru_fn : Name.Name) (ru_nargs
    : nat) (ru_try : RuleFun)
   : CoreRule.

Definition RuleBase :=
  (NameEnv.NameEnv (list CoreRule))%type.

Inductive RuleEnv : Type
  := | Mk_RuleEnv (re_base : RuleBase) (re_visible_orphs : Module.ModuleSet)
   : RuleEnv.

Inductive RnEnv2 : Type
  := | RV2 (envL : VarEnv Var) (envR : VarEnv Var) (in_scope : InScopeSet)
   : RnEnv2.

Inductive TCvSubst : Type
  := | Mk_TCvSubst : InScopeSet -> TvSubstEnv -> CvSubstEnv -> TCvSubst.

Inductive LiftingContext : Type
  := | LC : TCvSubst -> LiftCoEnv -> LiftingContext.
*)
