(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require Core.
Require CoreUtils.
Require GHC.Base.
Require GHC.Core.TyCo.Subst.
Require GHC.Types.Cpr.
Require HsToCoq.Err.
Require UnVarGraph.
Require Util.

(* Converted type declarations: *)

Inductive EtaInfo : Type := | EI : list Core.Var -> Core.MCoercionR -> EtaInfo.

Inductive Cost : Type := | IsCheap : Cost | IsExpensive : Cost.

Inductive ArityOpts : Type :=
  | ArityOpts (ao_ped_bot : bool) (ao_dicts_cheap : bool) : ArityOpts.

#[global] Definition ATLamInfo :=
  (Cost * BasicTypes.OneShotInfo)%type%type.

Inductive ArityType : Type :=
  | AT : list ATLamInfo -> Core.Divergence -> ArityType.

#[global] Definition SafeArityType :=
  ArityType%type.

Inductive ArityEnv : Type :=
  | AE (am_opts : ArityOpts) (am_sigs : (Core.IdEnv SafeArityType)) (am_free_joins
    : bool)
   : ArityEnv.

Instance Default__Cost : HsToCoq.Err.Default Cost :=
  HsToCoq.Err.Build_Default _ IsCheap.

Instance Default__ArityOpts : HsToCoq.Err.Default ArityOpts :=
  HsToCoq.Err.Build_Default _ (ArityOpts HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__ArityEnv : HsToCoq.Err.Default ArityEnv :=
  HsToCoq.Err.Build_Default _ (AE HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default).

#[global] Definition ao_dicts_cheap (arg_0__ : ArityOpts) :=
  let 'ArityOpts _ ao_dicts_cheap := arg_0__ in
  ao_dicts_cheap.

#[global] Definition ao_ped_bot (arg_0__ : ArityOpts) :=
  let 'ArityOpts ao_ped_bot _ := arg_0__ in
  ao_ped_bot.

#[global] Definition am_free_joins (arg_0__ : ArityEnv) :=
  let 'AE _ _ am_free_joins := arg_0__ in
  am_free_joins.

#[global] Definition am_opts (arg_0__ : ArityEnv) :=
  let 'AE am_opts _ _ := arg_0__ in
  am_opts.

#[global] Definition am_sigs (arg_0__ : ArityEnv) :=
  let 'AE _ am_sigs _ := arg_0__ in
  am_sigs.

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreArity.Outputable__ArityType' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreArity.Outputable__ArityEnv' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreArity.Outputable__EtaInfo' *)

Axiom manifestArity : Core.CoreExpr -> BasicTypes.Arity.

Axiom joinRhsArity : Core.CoreExpr -> BasicTypes.JoinArity.

Axiom exprBotStrictness_maybe : Core.CoreExpr ->
                                option (BasicTypes.Arity * Core.DmdSig * GHC.Types.Cpr.CprSig)%type.

Axiom arityTypeBotSigs_maybe : ArityType ->
                               option (BasicTypes.Arity * Core.DmdSig * GHC.Types.Cpr.CprSig)%type.

Axiom typeArity : AxiomatizedTypes.Type_ -> BasicTypes.Arity.

Axiom typeOneShots : AxiomatizedTypes.Type_ -> list BasicTypes.OneShotInfo.

Axiom typeOneShot : AxiomatizedTypes.Type_ -> BasicTypes.OneShotInfo.

Axiom idStateHackOneShotInfo : Core.Id -> BasicTypes.OneShotInfo.

Axiom isOneShotBndr : Core.Var -> bool.

Axiom isStateHackType : AxiomatizedTypes.Type_ -> bool.

Axiom zapLamBndrs : BasicTypes.FullArgCount -> list Core.Var -> list Core.Var.

Axiom allCosts : forall {a}, (a -> Cost) -> list a -> Cost.

Axiom addCost : Cost -> Cost -> Cost.

Axiom mkBotArityType : list BasicTypes.OneShotInfo -> ArityType.

Axiom botArityType : ArityType.

Axiom topArityType : ArityType.

Axiom arityTypeArity : SafeArityType -> BasicTypes.Arity.

Axiom arityTypeOneShots : SafeArityType -> list BasicTypes.OneShotInfo.

Axiom safeArityType : ArityType -> SafeArityType.

Axiom trimArityType : BasicTypes.Arity -> ArityType -> ArityType.

Axiom exprEtaExpandArity : forall `{Util.HasDebugCallStack},
                           ArityOpts -> Core.CoreExpr -> option SafeArityType.

Axiom findRhsArity : ArityOpts ->
                     BasicTypes.RecFlag -> Core.Id -> Core.CoreExpr -> (bool * SafeArityType)%type.

Axiom combineWithCallCards : ArityEnv ->
                             ArityType -> list Core.Card -> ArityType.

Axiom useSiteCallCards : Core.Id -> list Core.Card.

Axiom arityLam : Core.Id -> ArityType -> ArityType.

Axiom floatIn : Cost -> ArityType -> ArityType.

Axiom addWork : ArityType -> ArityType.

Axiom add_work : ATLamInfo -> ATLamInfo.

Axiom arityApp : ArityType -> Cost -> ArityType.

Axiom andArityType : ArityEnv -> ArityType -> ArityType -> ArityType.

Axiom andWithTail : ArityEnv -> Core.Divergence -> ArityType -> ArityType.

Axiom findRhsArityEnv : ArityOpts -> bool -> ArityEnv.

Axiom freeJoinsOK : ArityEnv -> bool.

Axiom modifySigEnv : (Core.IdEnv ArityType -> Core.IdEnv ArityType) ->
                     ArityEnv -> ArityEnv.

Axiom del_sig_env : Core.Id -> ArityEnv -> ArityEnv.

Axiom del_sig_env_list : list Core.Id -> ArityEnv -> ArityEnv.

Axiom extendSigEnv : ArityEnv -> Core.Id -> SafeArityType -> ArityEnv.

Axiom delInScope : ArityEnv -> Core.Id -> ArityEnv.

Axiom delInScopeList : ArityEnv -> list Core.Id -> ArityEnv.

Axiom lookupSigEnv : ArityEnv -> Core.Id -> option SafeArityType.

Axiom pedanticBottoms : ArityEnv -> bool.

Axiom exprCost : ArityEnv ->
                 Core.CoreExpr -> option AxiomatizedTypes.Type_ -> Cost.

Axiom myExprIsCheap : ArityEnv ->
                      Core.CoreExpr -> option AxiomatizedTypes.Type_ -> bool.

Axiom myIsCheapApp : Core.IdEnv SafeArityType -> CoreUtils.CheapAppFun.

Axiom arityType : forall `{Util.HasDebugCallStack},
                  ArityEnv -> Core.CoreExpr -> ArityType.

Axiom idArityType : Core.Id -> ArityType.

Axiom cheapArityType : forall `{Util.HasDebugCallStack},
                       Core.CoreExpr -> ArityType.

Axiom exprArity : Core.CoreExpr -> BasicTypes.Arity.

Axiom exprIsDeadEnd : Core.CoreExpr -> bool.

Axiom etaExpand : BasicTypes.Arity -> Core.CoreExpr -> Core.CoreExpr.

Axiom etaExpandAT : Core.InScopeSet ->
                    SafeArityType -> Core.CoreExpr -> Core.CoreExpr.

Axiom eta_expand : Core.InScopeSet ->
                   list BasicTypes.OneShotInfo -> Core.CoreExpr -> Core.CoreExpr.

Axiom etaInfoApp : Core.InScopeSet -> Core.CoreExpr -> EtaInfo -> Core.CoreExpr.

Axiom etaInfoAppTy : AxiomatizedTypes.Type_ ->
                     EtaInfo -> AxiomatizedTypes.Type_.

Axiom etaInfoAbs : EtaInfo -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkEtaWW : list BasicTypes.OneShotInfo ->
                GHC.Base.String ->
                Core.InScopeSet -> AxiomatizedTypes.Type_ -> (Core.InScopeSet * EtaInfo)%type.

Axiom mkEtaForAllMCo : Core.ForAllTyBinder ->
                       AxiomatizedTypes.Type_ -> Core.MCoercion -> Core.MCoercion.

Axiom tryEtaReduce : UnVarGraph.UnVarSet ->
                     list Core.Var -> Core.CoreExpr -> Core.SubDemand -> option Core.CoreExpr.

Axiom cantEtaReduceFun : Core.Id -> bool.

Axiom pushCoArgs : Core.CoercionR ->
                   list Core.CoreArg -> option (list Core.CoreArg * Core.MCoercion)%type.

Axiom pushMCoArg : Core.MCoercionR ->
                   Core.CoreArg -> option (Core.CoreArg * Core.MCoercion)%type.

Axiom pushCoArg : Core.CoercionR ->
                  Core.CoreArg -> option (Core.CoreArg * Core.MCoercion)%type.

Axiom pushCoTyArg : Core.CoercionR ->
                    AxiomatizedTypes.Type_ ->
                    option (AxiomatizedTypes.Type_ * Core.MCoercionR)%type.

Axiom pushCoValArg : Core.CoercionR ->
                     option (Core.MCoercionR * Core.MCoercionR)%type.

Axiom pushCoercionIntoLambda : forall `{Util.HasDebugCallStack},
                               Core.InScopeSet ->
                               Core.Var ->
                               Core.CoreExpr -> Core.CoercionR -> option (Core.Var * Core.CoreExpr)%type.

Axiom pushCoDataCon : Core.DataCon ->
                      list Core.CoreExpr ->
                      AxiomatizedTypes.Coercion ->
                      option (Core.DataCon * list AxiomatizedTypes.Type_ * list Core.CoreExpr)%type.

Axiom collectBindersPushingCo : Core.CoreExpr ->
                                (list Core.Var * Core.CoreExpr)%type.

Axiom etaExpandToJoinPoint : BasicTypes.JoinArity ->
                             Core.CoreExpr -> (list Core.CoreBndr * Core.CoreExpr)%type.

Axiom etaExpandToJoinPointRule : BasicTypes.JoinArity ->
                                 Core.CoreRule -> Core.CoreRule.

Axiom etaBodyForJoinPoint : nat ->
                            Core.CoreExpr -> (list Core.CoreBndr * Core.CoreExpr)%type.

Axiom freshEtaId : nat ->
                   GHC.Core.TyCo.Subst.Subst ->
                   Core.Scaled AxiomatizedTypes.Type_ ->
                   (GHC.Core.TyCo.Subst.Subst * Core.Id)%type.

(* External variables:
     bool list nat op_zt__ option AxiomatizedTypes.Coercion AxiomatizedTypes.Type_
     BasicTypes.Arity BasicTypes.FullArgCount BasicTypes.JoinArity
     BasicTypes.OneShotInfo BasicTypes.RecFlag Core.Card Core.CoercionR Core.CoreArg
     Core.CoreBndr Core.CoreExpr Core.CoreRule Core.DataCon Core.Divergence
     Core.DmdSig Core.ForAllTyBinder Core.Id Core.IdEnv Core.InScopeSet
     Core.MCoercion Core.MCoercionR Core.Scaled Core.SubDemand Core.Var
     CoreUtils.CheapAppFun GHC.Base.String GHC.Core.TyCo.Subst.Subst
     GHC.Types.Cpr.CprSig HsToCoq.Err.Build_Default HsToCoq.Err.Default
     HsToCoq.Err.default UnVarGraph.UnVarSet Util.HasDebugCallStack
*)
