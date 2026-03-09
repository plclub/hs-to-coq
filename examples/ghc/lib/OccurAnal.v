(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

(* GHC 9.10: OccurAnal uses Outputable.JoinPointHood *)
Require Import Outputable.
Require Import GHC.Base.
Require Import Coq.Strings.String.
Open Scope string_scope.

(* Converted imports: *)

Require BasicTypes.
Require Core.
Require Digraph.
Require GHC.Err.
Require GHC.Types.Tickish.
Require HsToCoq.Err.
Require Module.
Require Unique.

(* Converted type declarations: *)

#[global] Definition OneShots :=
  (list BasicTypes.OneShotInfo)%type.

Inductive OccEncl : Type :=
  | OccRhs : OccEncl
  | OccScrut : OccEncl
  | OccVanilla : OccEncl.

#[global] Definition NodeScore :=
  (nat * nat * bool)%type%type.

Inductive LocalOcc : Type :=
  | OneOccL (lo_n_br : BasicTypes.BranchCount) (lo_tail : BasicTypes.TailCallInfo)
  (lo_int_cxt : BasicTypes.InterestingCxt)
   : LocalOcc
  | ManyOccL : BasicTypes.TailCallInfo -> LocalOcc.

#[global] Definition OccInfoEnv :=
  (Core.IdEnv LocalOcc)%type.

#[global] Definition ZappedSet :=
  OccInfoEnv%type.

Inductive UsageDetails : Type :=
  | UD (ud_env : OccInfoEnv) (ud_z_many : ZappedSet) (ud_z_in_lam : ZappedSet)
  (ud_z_tail : ZappedSet)
   : UsageDetails.

Inductive TailUsageDetails : Type :=
  | TUD : BasicTypes.JoinArity -> UsageDetails -> TailUsageDetails.

Inductive WithTailUsageDetails a : Type :=
  | WTUD : TailUsageDetails -> a -> WithTailUsageDetails a.

Inductive NodeDetails : Type :=
  | ND (nd_bndr : Core.Id) (nd_rhs : (WithTailUsageDetails Core.CoreExpr)) (nd_inl
    : Core.IdSet) (nd_simple : bool) (nd_weak_fvs : Core.IdSet) (nd_active_rule_fvs
    : Core.IdSet)
   : NodeDetails.

Inductive WithUsageDetails a : Type :=
  | WUD : UsageDetails -> a -> WithUsageDetails a.

#[global] Definition LetrecNode :=
  (Digraph.Node Unique.Unique NodeDetails)%type.

#[global] Definition JoinPointInfo :=
  (Core.IdEnv OccInfoEnv)%type.

Inductive OccEnv : Type :=
  | Mk_OccEnv (occ_encl : OccEncl) (occ_one_shots : OneShots) (occ_unf_act
    : Core.Id -> bool) (occ_rule_act : BasicTypes.Activation -> bool) (occ_bs_env
    : (Core.IdEnv (Core.OutId * Core.MCoercion)%type)) (occ_bs_rng : Core.VarSet)
  (occ_join_points : JoinPointInfo)
   : OccEnv.

#[global] Definition ImpRuleEdges :=
  (Core.IdEnv (list (BasicTypes.Activation * Core.VarSet)%type))%type.

#[global] Definition IdWithOccInfo :=
  Core.Id%type.

Inductive SimpleNodeDetails : Type :=
  | SND (snd_bndr : IdWithOccInfo) (snd_rhs : Core.CoreExpr) (snd_score
    : NodeScore)
   : SimpleNodeDetails.

#[global] Definition LoopBreakerNode :=
  (Digraph.Node Unique.Unique SimpleNodeDetails)%type.

#[global] Definition Binding :=
  (Core.Id * Core.CoreExpr)%type%type.

Arguments WTUD {_} _ _.

Arguments WUD {_} _ _.

Instance Default__OccEncl : HsToCoq.Err.Default OccEncl :=
  HsToCoq.Err.Build_Default _ OccRhs.

Instance Default__UsageDetails : HsToCoq.Err.Default UsageDetails :=
  HsToCoq.Err.Build_Default _ (UD HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__OccEnv : HsToCoq.Err.Default OccEnv :=
  HsToCoq.Err.Build_Default _ (Mk_OccEnv HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default).

Instance Default__SimpleNodeDetails : HsToCoq.Err.Default SimpleNodeDetails :=
  HsToCoq.Err.Build_Default _ (SND HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default).

#[global] Definition lo_int_cxt (arg_0__ : LocalOcc) :=
  match arg_0__ with
  | OneOccL _ _ lo_int_cxt => lo_int_cxt
  | ManyOccL _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `lo_int_cxt' has no match in constructor `ManyOccL' of type `LocalOcc'")
  end.

#[global] Definition lo_n_br (arg_0__ : LocalOcc) :=
  match arg_0__ with
  | OneOccL lo_n_br _ _ => lo_n_br
  | ManyOccL _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `lo_n_br' has no match in constructor `ManyOccL' of type `LocalOcc'")
  end.

#[global] Definition lo_tail (arg_0__ : LocalOcc) :=
  match arg_0__ with
  | OneOccL _ lo_tail _ => lo_tail
  | ManyOccL _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `lo_tail' has no match in constructor `ManyOccL' of type `LocalOcc'")
  end.

#[global] Definition ud_env (arg_0__ : UsageDetails) :=
  let 'UD ud_env _ _ _ := arg_0__ in
  ud_env.

#[global] Definition ud_z_in_lam (arg_0__ : UsageDetails) :=
  let 'UD _ _ ud_z_in_lam _ := arg_0__ in
  ud_z_in_lam.

#[global] Definition ud_z_many (arg_0__ : UsageDetails) :=
  let 'UD _ ud_z_many _ _ := arg_0__ in
  ud_z_many.

#[global] Definition ud_z_tail (arg_0__ : UsageDetails) :=
  let 'UD _ _ _ ud_z_tail := arg_0__ in
  ud_z_tail.

#[global] Definition nd_active_rule_fvs (arg_0__ : NodeDetails) :=
  let 'ND _ _ _ _ _ nd_active_rule_fvs := arg_0__ in
  nd_active_rule_fvs.

#[global] Definition nd_bndr (arg_0__ : NodeDetails) :=
  let 'ND nd_bndr _ _ _ _ _ := arg_0__ in
  nd_bndr.

#[global] Definition nd_inl (arg_0__ : NodeDetails) :=
  let 'ND _ _ nd_inl _ _ _ := arg_0__ in
  nd_inl.

#[global] Definition nd_rhs (arg_0__ : NodeDetails) :=
  let 'ND _ nd_rhs _ _ _ _ := arg_0__ in
  nd_rhs.

#[global] Definition nd_simple (arg_0__ : NodeDetails) :=
  let 'ND _ _ _ nd_simple _ _ := arg_0__ in
  nd_simple.

#[global] Definition nd_weak_fvs (arg_0__ : NodeDetails) :=
  let 'ND _ _ _ _ nd_weak_fvs _ := arg_0__ in
  nd_weak_fvs.

#[global] Definition occ_bs_env (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv _ _ _ _ occ_bs_env _ _ := arg_0__ in
  occ_bs_env.

#[global] Definition occ_bs_rng (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv _ _ _ _ _ occ_bs_rng _ := arg_0__ in
  occ_bs_rng.

#[global] Definition occ_encl (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv occ_encl _ _ _ _ _ _ := arg_0__ in
  occ_encl.

#[global] Definition occ_join_points (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv _ _ _ _ _ _ occ_join_points := arg_0__ in
  occ_join_points.

#[global] Definition occ_one_shots (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv _ occ_one_shots _ _ _ _ _ := arg_0__ in
  occ_one_shots.

#[global] Definition occ_rule_act (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv _ _ _ occ_rule_act _ _ _ := arg_0__ in
  occ_rule_act.

#[global] Definition occ_unf_act (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv _ _ occ_unf_act _ _ _ _ := arg_0__ in
  occ_unf_act.

#[global] Definition snd_bndr (arg_0__ : SimpleNodeDetails) :=
  let 'SND snd_bndr _ _ := arg_0__ in
  snd_bndr.

#[global] Definition snd_rhs (arg_0__ : SimpleNodeDetails) :=
  let 'SND _ snd_rhs _ := arg_0__ in
  snd_rhs.

#[global] Definition snd_score (arg_0__ : SimpleNodeDetails) :=
  let 'SND _ _ snd_score := arg_0__ in
  snd_score.

(* Midamble *)

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

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccurAnal.Outputable__NodeDetails' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccurAnal.Outputable__SimpleNodeDetails' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccurAnal.Outputable__OccEncl' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccurAnal.Outputable__LocalOcc' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccurAnal.Outputable__UsageDetails' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccurAnal.Outputable__TailUsageDetails' *)

Axiom occurAnalyseExpr : Core.CoreExpr -> Core.CoreExpr.

Axiom occurAnalysePgm : Module.Module ->
                        (Core.Id -> bool) ->
                        (BasicTypes.Activation -> bool) ->
                        list Core.CoreRule -> Core.CoreProgram -> Core.CoreProgram.

Axiom noImpRuleEdges : ImpRuleEdges.

Axiom lookupImpRules : ImpRuleEdges ->
                       Core.Id -> list (BasicTypes.Activation * Core.VarSet)%type.

Axiom impRulesScopeUsage : list (BasicTypes.Activation * Core.VarSet)%type ->
                           UsageDetails.

Axiom impRulesActiveFvs : (BasicTypes.Activation -> bool) ->
                          Core.VarSet -> list (BasicTypes.Activation * Core.VarSet)%type -> Core.VarSet.

Axiom occAnalBind : forall {r},
                    OccEnv ->
                    BasicTypes.TopLevelFlag ->
                    ImpRuleEdges ->
                    Core.CoreBind ->
                    (OccEnv -> WithUsageDetails r) ->
                    (list Core.CoreBind -> r -> r) -> WithUsageDetails r.

Axiom occAnalNonRecBody : forall {r},
                          OccEnv ->
                          Core.Id ->
                          (OccEnv -> WithUsageDetails r) ->
                          (WithUsageDetails (BasicTypes.OccInfo * r)%type).

Axiom occAnalNonRecRhs : OccEnv ->
                         ImpRuleEdges ->
                         Outputable.JoinPointHood ->
                         Core.Id -> Core.CoreExpr -> (list UsageDetails * Core.Id * Core.CoreExpr)%type.

Axiom mkNonRecRhsCtxt : Core.Id -> Core.Unfolding -> OccEncl.

Axiom occAnalRecBind : OccEnv ->
                       BasicTypes.TopLevelFlag ->
                       ImpRuleEdges ->
                       list (Core.Var * Core.CoreExpr)%type ->
                       UsageDetails -> WithUsageDetails (list Core.CoreBind).

(* Skipping definition `OccurAnal.occAnalRec' *)

Axiom loopBreakNodes : nat ->
                       Core.VarSet -> list LoopBreakerNode -> list Binding -> list Binding.

Axiom reOrderNodes : nat ->
                     Core.VarSet -> list LoopBreakerNode -> list Binding -> list Binding.

Axiom nodeBinding : (Core.Id -> Core.Id) -> LoopBreakerNode -> Binding.

Axiom mk_loop_breaker : Core.Id -> Core.Id.

Axiom mk_non_loop_breaker : Core.VarSet -> Core.Id -> Core.Id.

Axiom chooseLoopBreaker : bool ->
                          NodeScore ->
                          list LoopBreakerNode ->
                          list LoopBreakerNode ->
                          list LoopBreakerNode -> (list LoopBreakerNode * list LoopBreakerNode)%type.

Axiom rank : NodeScore -> nat.

Axiom makeNode : OccEnv ->
                 ImpRuleEdges -> Core.VarSet -> (Core.Var * Core.CoreExpr)%type -> LetrecNode.

Axiom mkLoopBreakerNodes : OccEnv ->
                           BasicTypes.TopLevelFlag ->
                           UsageDetails -> list NodeDetails -> WithUsageDetails (list LoopBreakerNode).

Axiom nodeScore : OccEnv -> Core.Id -> Core.VarSet -> NodeDetails -> NodeScore.

Axiom maxExprSize : nat.

Axiom cheapExprSize : Core.CoreExpr -> nat.

Axiom betterLB : NodeScore -> NodeScore -> bool.

Axiom isOneShotFun : Core.CoreExpr -> bool.

Axiom zapLambdaBndrs : Core.CoreExpr ->
                       BasicTypes.FullArgCount -> Core.CoreExpr.

Axiom occAnalLamTail : OccEnv ->
                       Core.CoreExpr -> WithTailUsageDetails Core.CoreExpr.

Axiom occ_anal_lam_tail : OccEnv ->
                          Core.CoreExpr -> WithUsageDetails Core.CoreExpr.

Axiom occAnalUnfolding : OccEnv ->
                         Core.Unfolding -> WithTailUsageDetails Core.Unfolding.

Axiom occAnalRule : OccEnv ->
                    Core.CoreRule -> (Core.CoreRule * UsageDetails * TailUsageDetails)%type.

Axiom occAnalList : OccEnv ->
                    list Core.CoreExpr -> WithUsageDetails (list Core.CoreExpr).

Axiom occAnal : OccEnv -> Core.CoreExpr -> WithUsageDetails Core.CoreExpr.

Axiom occAnalArgs : OccEnv ->
                    Core.CoreExpr ->
                    list Core.CoreExpr -> list OneShots -> WithUsageDetails Core.CoreExpr.

Axiom occAnalApp : OccEnv ->
                   (Core.Expr Core.CoreBndr * list (Core.Arg Core.CoreBndr) *
                    list GHC.Types.Tickish.CoreTickish)%type ->
                   WithUsageDetails (Core.Expr Core.CoreBndr).

Axiom addAppCtxt : OccEnv -> list (Core.Arg Core.CoreBndr) -> OccEnv.

Axiom initOccEnv : OccEnv.

Axiom noBinderSwaps : OccEnv -> bool.

Axiom setScrutCtxt : OccEnv -> list Core.CoreAlt -> OccEnv.

Axiom setNonTailCtxt : OccEncl -> OccEnv -> OccEnv.

Axiom setTailCtxt : OccEnv -> OccEnv.

Axiom mkRhsOccEnv : OccEnv ->
                    BasicTypes.RecFlag ->
                    OccEncl -> Outputable.JoinPointHood -> Core.Id -> Core.CoreExpr -> OccEnv.

Axiom zapJoinPointInfo : JoinPointInfo -> JoinPointInfo.

Axiom extendOneShotsForJoinPoint : BasicTypes.RecFlag ->
                                   BasicTypes.JoinArity ->
                                   Core.CoreExpr -> list BasicTypes.OneShotInfo -> list BasicTypes.OneShotInfo.

Axiom setOneShots : OneShots -> OccEnv -> OccEnv.

Axiom isRhsEnv : OccEnv -> bool.

Axiom addInScopeList : forall {a},
                       OccEnv -> list Core.Var -> (OccEnv -> WithUsageDetails a) -> WithUsageDetails a.

Axiom addInScopeOne : forall {a},
                      OccEnv -> Core.Id -> (OccEnv -> WithUsageDetails a) -> WithUsageDetails a.

Axiom addInScope : forall {a},
                   OccEnv -> list Core.Var -> (OccEnv -> WithUsageDetails a) -> WithUsageDetails a.

Axiom preprocess_env : OccEnv -> Core.VarSet -> (OccEnv * JoinPointInfo)%type.

Axiom postprocess_uds : list Core.Var ->
                        JoinPointInfo -> UsageDetails -> UsageDetails.

Axiom addJoinPoint : OccEnv -> Core.Id -> UsageDetails -> OccEnv.

Axiom mkZeroedForm : UsageDetails -> OccInfoEnv.

Axiom transClosureFV : Core.VarEnv Core.VarSet -> Core.VarEnv Core.VarSet.

Axiom extendFvs_ : Core.VarEnv Core.VarSet -> Core.VarSet -> Core.VarSet.

Axiom extendFvs : Core.VarEnv Core.VarSet ->
                  Core.VarSet -> (Core.VarSet * bool)%type.

Axiom addBndrSwap : Core.OutExpr -> Core.Id -> OccEnv -> OccEnv.

Axiom scrutBinderSwap_maybe : Core.OutExpr ->
                              option (Core.OutVar * Core.MCoercion)%type.

Axiom lookupBndrSwap : OccEnv -> Core.Id -> (Core.CoreExpr * Core.Id)%type.

Axiom localTailCallInfo : LocalOcc -> BasicTypes.TailCallInfo.

Axiom andUDs : UsageDetails -> UsageDetails -> UsageDetails.

Axiom orUDs : UsageDetails -> UsageDetails -> UsageDetails.

Axiom mkOneOcc : OccEnv ->
                 Core.Id -> BasicTypes.InterestingCxt -> BasicTypes.JoinArity -> UsageDetails.

Axiom add_many_occ : Core.Var -> OccInfoEnv -> OccInfoEnv.

Axiom addManyOccs : UsageDetails -> Core.VarSet -> UsageDetails.

Axiom addLamCoVarOccs : UsageDetails -> list Core.Var -> UsageDetails.

Axiom emptyDetails : UsageDetails.

Axiom isEmptyDetails : UsageDetails -> bool.

Axiom mkSimpleDetails : OccInfoEnv -> UsageDetails.

Axiom modifyUDEnv : (OccInfoEnv -> OccInfoEnv) -> UsageDetails -> UsageDetails.

Axiom delBndrsFromUDs : list Core.Var -> UsageDetails -> UsageDetails.

Axiom markAllMany : UsageDetails -> UsageDetails.

Axiom markAllInsideLam : UsageDetails -> UsageDetails.

Axiom markAllNonTail : UsageDetails -> UsageDetails.

Axiom markAllManyNonTail : UsageDetails -> UsageDetails.

Axiom markAllInsideLamIf : bool -> UsageDetails -> UsageDetails.

Axiom markAllNonTailIf : bool -> UsageDetails -> UsageDetails.

Axiom lookupTailCallInfo : UsageDetails -> Core.Id -> BasicTypes.TailCallInfo.

Axiom udFreeVars : Core.VarSet -> UsageDetails -> Core.VarSet.

Axiom restrictFreeVars : Core.VarSet -> OccInfoEnv -> Core.VarSet.

Axiom combineUsageDetailsWith : (LocalOcc -> LocalOcc -> LocalOcc) ->
                                UsageDetails -> UsageDetails -> UsageDetails.

Axiom lookupLetOccInfo : UsageDetails -> Core.Id -> BasicTypes.OccInfo.

Axiom lookupOccInfo : UsageDetails -> Core.Id -> BasicTypes.OccInfo.

Axiom lookupOccInfoByUnique : UsageDetails ->
                              Unique.Unique -> BasicTypes.OccInfo.

Axiom adjustNonRecRhs : Outputable.JoinPointHood ->
                        WithTailUsageDetails Core.CoreExpr -> WithUsageDetails Core.CoreExpr.

Axiom adjustTailUsage : Outputable.JoinPointHood ->
                        WithTailUsageDetails Core.CoreExpr -> UsageDetails.

Axiom adjustTailArity : Outputable.JoinPointHood ->
                        TailUsageDetails -> UsageDetails.

Axiom tagLamBinders : UsageDetails -> list Core.Id -> list IdWithOccInfo.

Axiom tagLamBinder : UsageDetails -> Core.Id -> IdWithOccInfo.

Axiom tagNonRecBinder : BasicTypes.TopLevelFlag ->
                        BasicTypes.OccInfo ->
                        Core.CoreBndr -> (IdWithOccInfo * Outputable.JoinPointHood)%type.

Axiom tagRecBinders : BasicTypes.TopLevelFlag ->
                      UsageDetails -> list NodeDetails -> WithUsageDetails (list IdWithOccInfo).

Axiom setBinderOcc : BasicTypes.OccInfo -> Core.CoreBndr -> Core.CoreBndr.

Axiom decideRecJoinPointHood : BasicTypes.TopLevelFlag ->
                               UsageDetails -> list Core.CoreBndr -> bool.

Axiom okForJoinPoint : BasicTypes.TopLevelFlag ->
                       Core.Id -> BasicTypes.TailCallInfo -> bool.

Axiom markNonTail : BasicTypes.OccInfo -> BasicTypes.OccInfo.

Axiom andLocalOcc : LocalOcc -> LocalOcc -> LocalOcc.

Axiom orLocalOcc : LocalOcc -> LocalOcc -> LocalOcc.

Axiom andTailCallInfo : BasicTypes.TailCallInfo ->
                        BasicTypes.TailCallInfo -> BasicTypes.TailCallInfo.

(* External variables:
     bool list nat op_zt__ option BasicTypes.Activation BasicTypes.BranchCount
     BasicTypes.FullArgCount BasicTypes.InterestingCxt BasicTypes.JoinArity
     BasicTypes.OccInfo BasicTypes.OneShotInfo BasicTypes.RecFlag
     BasicTypes.TailCallInfo BasicTypes.TopLevelFlag Core.Arg Core.CoreAlt
     Core.CoreBind Core.CoreBndr Core.CoreExpr Core.CoreProgram Core.CoreRule
     Core.Expr Core.Id Core.IdEnv Core.IdSet Core.MCoercion Core.OutExpr Core.OutId
     Core.OutVar Core.Unfolding Core.Var Core.VarEnv Core.VarSet Digraph.Node
     GHC.Err.error GHC.Types.Tickish.CoreTickish HsToCoq.Err.Build_Default
     HsToCoq.Err.Default HsToCoq.Err.default Module.Module Outputable.JoinPointHood
     Unique.Unique
*)
