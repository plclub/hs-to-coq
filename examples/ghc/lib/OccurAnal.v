(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require CoreArity.
Require CoreFVs.
Require CoreUtils.
Require Data.Foldable.
Require Data.Tuple.
Require Digraph.
Require GHC.Base.
Require GHC.Core.Predicate.
Require GHC.Core.TyCo.FVs.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Types.Tickish.
Require GHC.Utils.Trace.
Require HsToCoq.Err.
Require Id.
Require Maybes.
Require Module.
Require Panic.
Require PrelNames.
Require UniqFM.
Require UniqSet.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

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

#[global] Instance Default__OccEncl : HsToCoq.Err.Default OccEncl :=
  HsToCoq.Err.Build_Default _ OccRhs.

#[global] Instance Default__LocalOcc : HsToCoq.Err.Default LocalOcc :=
  HsToCoq.Err.Build_Default _ (OneOccL HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default).

#[global] Instance Default__UsageDetails : HsToCoq.Err.Default UsageDetails :=
  HsToCoq.Err.Build_Default _ (UD HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default).

#[global] Instance Default__TailUsageDetails : HsToCoq.Err.Default TailUsageDetails :=
  HsToCoq.Err.Build_Default _ (TUD HsToCoq.Err.default HsToCoq.Err.default).

#[global] Instance Default__WithTailUsageDetails {a} `{HsToCoq.Err.Default a} : HsToCoq.Err.Default (WithTailUsageDetails a) :=
  HsToCoq.Err.Build_Default _ (WTUD HsToCoq.Err.default HsToCoq.Err.default).

#[global] Instance Default__NodeDetails : HsToCoq.Err.Default NodeDetails :=
  HsToCoq.Err.Build_Default _ (ND HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default).

#[global] Instance Default__OccEnv : HsToCoq.Err.Default OccEnv :=
  HsToCoq.Err.Build_Default _ (Mk_OccEnv HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default).

#[global] Instance Default__SimpleNodeDetails : HsToCoq.Err.Default SimpleNodeDetails :=
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

#[global] Definition initOccEnv : OccEnv :=
  Mk_OccEnv OccVanilla nil (fun arg_0__ => true) (fun arg_1__ => true)
            Core.emptyVarEnv Core.emptyVarSet Core.emptyVarEnv.

Axiom occAnal : OccEnv -> Core.CoreExpr -> WithUsageDetails Core.CoreExpr.

#[global] Definition occurAnalyseExpr : Core.CoreExpr -> Core.CoreExpr :=
  fun expr => let 'WUD _ expr' := occAnal initOccEnv expr in expr'.

Axiom occurAnalysePgm : Module.Module ->
                        (Core.Id -> bool) ->
                        (BasicTypes.Activation -> bool) ->
                        list Core.CoreRule -> Core.CoreProgram -> Core.CoreProgram.

#[global] Definition noImpRuleEdges : ImpRuleEdges :=
  Core.emptyVarEnv.

#[global] Definition lookupImpRules
   : ImpRuleEdges -> Core.Id -> list (BasicTypes.Activation * Core.VarSet)%type :=
  fun imp_rule_edges bndr =>
    match Core.lookupVarEnv imp_rule_edges bndr with
    | None => nil
    | Some vs => vs
    end.

#[global] Definition add_many_occ : Core.Var -> OccInfoEnv -> OccInfoEnv :=
  fun v env =>
    if Core.isId v : bool
    then Core.extendVarEnv env v (ManyOccL BasicTypes.NoTailCallInfo) else
    env.

#[global] Definition addManyOccs
   : UsageDetails -> Core.VarSet -> UsageDetails :=
  fun uds var_set =>
    let add_to :=
      fun env => UniqSet.nonDetStrictFoldUniqSet add_many_occ env var_set in
    if Core.isEmptyVarSet var_set : bool then uds else
    let 'UD ud_env_1__ ud_z_many_2__ ud_z_in_lam_3__ ud_z_tail_4__ := uds in
    UD (add_to (ud_env uds)) ud_z_many_2__ ud_z_in_lam_3__ ud_z_tail_4__.

#[global] Definition mkSimpleDetails : OccInfoEnv -> UsageDetails :=
  fun env => UD env Core.emptyVarEnv Core.emptyVarEnv Core.emptyVarEnv.

#[global] Definition emptyDetails : UsageDetails :=
  mkSimpleDetails Core.emptyVarEnv.

#[global] Definition impRulesScopeUsage
   : list (BasicTypes.Activation * Core.VarSet)%type -> UsageDetails :=
  fun imp_rules_info =>
    let add :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair _ vs, usage => addManyOccs usage vs
        end in
    Data.Foldable.foldr add emptyDetails imp_rules_info.

#[global] Definition impRulesActiveFvs
   : (BasicTypes.Activation -> bool) ->
     Core.VarSet -> list (BasicTypes.Activation * Core.VarSet)%type -> Core.VarSet :=
  fun is_active bndr_set vs =>
    let add :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair act vs, acc =>
            if is_active act : bool then Core.unionVarSet vs acc else
            acc
        end in
    Core.intersectVarSet (Data.Foldable.foldr add Core.emptyVarSet vs) bndr_set.

Axiom occAnalBind : forall {r},
                    OccEnv ->
                    BasicTypes.TopLevelFlag ->
                    ImpRuleEdges ->
                    Core.CoreBind ->
                    (OccEnv -> WithUsageDetails r) ->
                    (list Core.CoreBind -> r -> r) -> WithUsageDetails r.

#[global] Definition delBndrsFromUDs
   : list Core.Var -> UsageDetails -> UsageDetails :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | bndrs, UD env z_many z_in_lam z_tail =>
        UD (Core.delVarEnvList env bndrs) (Core.delVarEnvList z_many bndrs)
           (Core.delVarEnvList z_in_lam bndrs) (Core.delVarEnvList z_tail bndrs)
    end.

#[global] Definition andTailCallInfo
   : BasicTypes.TailCallInfo ->
     BasicTypes.TailCallInfo -> BasicTypes.TailCallInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (BasicTypes.AlwaysTailCalled arity1 as info)
    , BasicTypes.AlwaysTailCalled arity2 =>
        if arity1 GHC.Base.== arity2 : bool then info else
        BasicTypes.NoTailCallInfo
    | _, _ => BasicTypes.NoTailCallInfo
    end.

#[global] Definition localTailCallInfo : LocalOcc -> BasicTypes.TailCallInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | OneOccL _ tci _ => tci
    | ManyOccL tci => tci
    end.

#[global] Definition andLocalOcc : LocalOcc -> LocalOcc -> LocalOcc :=
  fun occ1 occ2 =>
    let tci2 := localTailCallInfo occ2 in
    let tci1 := localTailCallInfo occ1 in ManyOccL (andTailCallInfo tci1 tci2).

#[global] Definition modifyUDEnv
   : (OccInfoEnv -> OccInfoEnv) -> UsageDetails -> UsageDetails :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, (UD env _ _ _ as uds) =>
        let 'UD ud_env_2__ ud_z_many_3__ ud_z_in_lam_4__ ud_z_tail_5__ := uds in
        UD (f env) ud_z_many_3__ ud_z_in_lam_4__ ud_z_tail_5__
    end.

#[global] Definition postprocess_uds
   : list Core.Var -> JoinPointInfo -> UsageDetails -> UsageDetails :=
  fun bndrs bad_joins uds =>
    let add_bad_join : Unique.Unique -> OccInfoEnv -> OccInfoEnv -> OccInfoEnv :=
      fun uniq join_env env =>
        if Core.elemVarEnvByKey uniq env : bool
        then Core.plusVarEnv_C andLocalOcc env join_env else
        env in
    let extend_with_bad_joins : OccInfoEnv -> OccInfoEnv :=
      fun env => UniqFM.nonDetStrictFoldUFM_Directly add_bad_join env bad_joins in
    let add_bad_joins : UsageDetails -> UsageDetails :=
      fun uds =>
        if Core.isEmptyVarEnv bad_joins : bool then uds else
        modifyUDEnv extend_with_bad_joins uds in
    add_bad_joins (delBndrsFromUDs bndrs uds).

#[global] Definition preprocess_env
   : OccEnv -> Core.VarSet -> (OccEnv * JoinPointInfo)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_OccEnv _ _ _ _ _ bs_rng_vars join_points as env), bndr_set =>
        let bndr_fm : UniqFM.UniqFM Core.Var Core.Var := UniqSet.getUniqSet bndr_set in
        let is_bad : Unique.Unique -> OccInfoEnv -> bool -> bool :=
          fun uniq join_uds rest =>
            orb (UniqSet.elemUniqSet_Directly uniq bndr_set) (orb (negb (UniqFM.disjointUFM
                                                                         bndr_fm join_uds)) rest) in
        let bad_joins : bool :=
          Core.nonDetStrictFoldVarEnv_Directly is_bad false join_points in
        let drop_shadowed_joins : OccEnv -> OccEnv :=
          fun '(Mk_OccEnv occ_encl_5__ occ_one_shots_6__ occ_unf_act_7__ occ_rule_act_8__
          occ_bs_env_9__ occ_bs_rng_10__ occ_join_points_11__) =>
            Mk_OccEnv occ_encl_5__ occ_one_shots_6__ occ_unf_act_7__ occ_rule_act_8__
                      occ_bs_env_9__ occ_bs_rng_10__ Core.emptyVarEnv in
        let drop_shadowed_swaps : OccEnv -> OccEnv :=
          fun '((Mk_OccEnv _ _ _ _ swap_env _ _ as env)) =>
            if Core.isEmptyVarEnv swap_env : bool then env else
            if Core.intersectsVarSet bs_rng_vars bndr_set : bool
            then let 'Mk_OccEnv occ_encl_16__ occ_one_shots_17__ occ_unf_act_18__
                    occ_rule_act_19__ occ_bs_env_20__ occ_bs_rng_21__ occ_join_points_22__ := env in
                 Mk_OccEnv occ_encl_16__ occ_one_shots_17__ occ_unf_act_18__ occ_rule_act_19__
                           Core.emptyVarEnv Core.emptyVarSet occ_join_points_22__ else
            let 'Mk_OccEnv occ_encl_25__ occ_one_shots_26__ occ_unf_act_27__
               occ_rule_act_28__ occ_bs_env_29__ occ_bs_rng_30__ occ_join_points_31__ := env in
            Mk_OccEnv occ_encl_25__ occ_one_shots_26__ occ_unf_act_27__ occ_rule_act_28__
                      (UniqFM.minusUFM swap_env bndr_fm) occ_bs_rng_30__ occ_join_points_31__ in
        if bad_joins : bool
        then pair (drop_shadowed_swaps (drop_shadowed_joins env)) join_points else
        pair (drop_shadowed_swaps env) Core.emptyVarEnv
    end.

#[global] Definition addInScope {a}
   : OccEnv ->
     list Core.Var -> (OccEnv -> WithUsageDetails a) -> WithUsageDetails a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | env, bndrs, thing_inside =>
        let j_8__ :=
          match arg_0__, arg_1__, arg_2__ with
          | env, bndrs, thing_inside =>
              let bndr_set := Core.mkVarSet bndrs in
              let 'pair env' bad_joins := preprocess_env env bndr_set in
              let 'WUD uds res := thing_inside env' in
              let uds' := postprocess_uds bndrs bad_joins uds in WUD uds' res
          end in
        if andb (Core.isEmptyVarEnv (occ_bs_env env)) (Core.isEmptyVarEnv
                 (occ_join_points env)) : bool
        then match thing_inside env with
             | WUD uds res => WUD (delBndrsFromUDs bndrs uds) res
             end else
        j_8__
    end.

#[global] Definition addInScopeOne {a}
   : OccEnv -> Core.Id -> (OccEnv -> WithUsageDetails a) -> WithUsageDetails a :=
  fun env bndr => addInScope env (cons bndr nil).

#[global] Definition lookupOccInfoByUnique
   : UsageDetails -> Unique.Unique -> BasicTypes.OccInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UD env z_many z_in_lam z_tail, uniq =>
        let mk_tail_info :=
          fun ti =>
            if Core.elemVarEnvByKey uniq z_tail : bool then BasicTypes.NoTailCallInfo else
            ti in
        match Core.lookupVarEnv_Directly env uniq with
        | None => BasicTypes.IAmDead
        | Some (OneOccL n_br tail_info int_cxt) =>
            let in_lam :=
              if Core.elemVarEnvByKey uniq z_in_lam : bool then BasicTypes.IsInsideLam else
              BasicTypes.NotInsideLam in
            if Core.elemVarEnvByKey uniq z_many : bool
            then BasicTypes.ManyOccs (mk_tail_info tail_info) else
            BasicTypes.OneOcc in_lam n_br int_cxt (mk_tail_info tail_info)
        | Some (ManyOccL tail_info) => BasicTypes.ManyOccs (mk_tail_info tail_info)
        end
    end.

#[global] Definition lookupLetOccInfo
   : UsageDetails -> Core.Id -> BasicTypes.OccInfo :=
  fun ud id =>
    if Core.isExportedId id : bool then BasicTypes.noOccInfo else
    lookupOccInfoByUnique ud (Id.idUnique id).

#[global] Definition occAnalNonRecBody {r}
   : OccEnv ->
     Core.Id ->
     (OccEnv -> WithUsageDetails r) ->
     (WithUsageDetails (BasicTypes.OccInfo * r)%type) :=
  fun env bndr thing_inside =>
    addInScopeOne env bndr (fun env =>
                              let 'WUD inner_uds res := thing_inside env in
                              let occ := lookupLetOccInfo inner_uds bndr in WUD inner_uds (pair occ res)).

Fixpoint isOneShotFun (arg_0__ : Core.CoreExpr) : bool
  := match arg_0__ with
     | Core.Lam b e => andb (CoreArity.isOneShotBndr b) (isOneShotFun e)
     | Core.Cast e _ => isOneShotFun e
     | _ => true
     end.

#[global] Definition markAllInsideLam : UsageDetails -> UsageDetails :=
  fun '((UD env _ _ _ as ud)) =>
    let 'UD ud_env_1__ ud_z_many_2__ ud_z_in_lam_3__ ud_z_tail_4__ := ud in
    UD ud_env_1__ ud_z_many_2__ env ud_z_tail_4__.

#[global] Definition markAllInsideLamIf
   : bool -> UsageDetails -> UsageDetails :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | true, ud => markAllInsideLam ud
    | false, ud => ud
    end.

#[global] Definition markAllNonTail : UsageDetails -> UsageDetails :=
  fun '((UD env _ _ _ as ud)) =>
    let 'UD ud_env_1__ ud_z_many_2__ ud_z_in_lam_3__ ud_z_tail_4__ := ud in
    UD ud_env_1__ ud_z_many_2__ ud_z_in_lam_3__ env.

#[global] Definition markAllNonTailIf : bool -> UsageDetails -> UsageDetails :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | true, ud => markAllNonTail ud
    | false, ud => ud
    end.

#[global] Definition adjustTailUsage
   : Outputable.JoinPointHood ->
     WithTailUsageDetails Core.CoreExpr -> UsageDetails :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | mb_join_arity, WTUD (TUD rhs_ja uds) rhs =>
        let exact_join := mb_join_arity GHC.Base.== Outputable.JoinPoint rhs_ja in
        let one_shot := isOneShotFun rhs in
        markAllInsideLamIf (negb one_shot) (markAllNonTailIf (negb exact_join) uds)
    end.

#[global] Definition adjustNonRecRhs
   : Outputable.JoinPointHood ->
     WithTailUsageDetails Core.CoreExpr -> WithUsageDetails Core.CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | mb_join_arity, (WTUD _ rhs as rhs_wuds) =>
        WUD (adjustTailUsage mb_join_arity rhs_wuds) rhs
    end.

#[global] Definition adjustTailArity
   : Outputable.JoinPointHood -> TailUsageDetails -> UsageDetails :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | mb_rhs_ja, TUD ja usage =>
        markAllNonTailIf (mb_rhs_ja GHC.Base./= Outputable.JoinPoint ja) usage
    end.

#[global] Definition combineUsageDetailsWith
   : (LocalOcc -> LocalOcc -> LocalOcc) ->
     UsageDetails -> UsageDetails -> UsageDetails :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | plus_occ_info
    , (UD env1 z_many1 z_in_lam1 z_tail1 as uds1)
    , (UD env2 z_many2 z_in_lam2 z_tail2 as uds2) =>
        if Core.isEmptyVarEnv env1 : bool then uds2 else
        if Core.isEmptyVarEnv env2 : bool then uds1 else
        UD (Core.plusVarEnv_C plus_occ_info env1 env2) (Core.plusVarEnv z_many1 z_many2)
           (Core.plusVarEnv z_in_lam1 z_in_lam2) (Core.plusVarEnv z_tail1 z_tail2)
    end.

#[global] Definition andUDs : UsageDetails -> UsageDetails -> UsageDetails :=
  combineUsageDetailsWith andLocalOcc.

#[global] Definition mkNonRecRhsCtxt : Core.Id -> Core.Unfolding -> OccEncl :=
  fun bndr unf =>
    let not_stable := negb (Core.isStableUnfolding unf) in
    let active := BasicTypes.isAlwaysActive (Id.idInlineActivation bndr) in
    let certainly_inline :=
      match Id.idOccInfo bndr with
      | BasicTypes.OneOcc BasicTypes.NotInsideLam num_3__ _ _ =>
          if num_3__ GHC.Base.== #1 : bool then andb active not_stable else
          false
      | _ => false
      end in
    if certainly_inline : bool then OccVanilla else
    OccRhs.

#[global] Definition extendOneShotsForJoinPoint
   : BasicTypes.RecFlag ->
     BasicTypes.JoinArity ->
     Core.CoreExpr -> list BasicTypes.OneShotInfo -> list BasicTypes.OneShotInfo :=
  fun is_rec join_arity rhs ctxt_one_shots =>
    let os :=
      match is_rec with
      | BasicTypes.NonRecursive => BasicTypes.OneShotLam
      | BasicTypes.Recursive => BasicTypes.NoOneShotInfo
      end in
    let fix go arg_2__ arg_3__
      := match arg_2__, arg_3__ with
         | num_4__, _ =>
             if num_4__ GHC.Base.== #0 : bool then ctxt_one_shots else
             match arg_2__, arg_3__ with
             | n, Core.Lam b rhs =>
                 if Core.isId b : bool then cons os (go (n GHC.Num.- #1) rhs) else
                 go (n GHC.Num.- #1) rhs
             | _, _ => nil
             end
         end in
    go join_arity rhs.

#[global] Definition zapJoinPointInfo : JoinPointInfo -> JoinPointInfo :=
  fun arg_0__ => Core.emptyVarEnv.

#[global] Definition mkRhsOccEnv
   : OccEnv ->
     BasicTypes.RecFlag ->
     OccEncl -> Outputable.JoinPointHood -> Core.Id -> Core.CoreExpr -> OccEnv :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
    | (Mk_OccEnv _ ctxt_one_shots _ _ _ _ ctxt_join_points as env)
    , is_rec
    , encl
    , jp_hood
    , bndr
    , rhs =>
        match jp_hood with
        | Outputable.JoinPoint join_arity =>
            let 'Mk_OccEnv occ_encl_6__ occ_one_shots_7__ occ_unf_act_8__ occ_rule_act_9__
               occ_bs_env_10__ occ_bs_rng_11__ occ_join_points_12__ := env in
            Mk_OccEnv OccVanilla (extendOneShotsForJoinPoint is_rec join_arity rhs
                       ctxt_one_shots) occ_unf_act_8__ occ_rule_act_9__ occ_bs_env_10__ occ_bs_rng_11__
                      ctxt_join_points
        | _ =>
            let 'Mk_OccEnv occ_encl_15__ occ_one_shots_16__ occ_unf_act_17__
               occ_rule_act_18__ occ_bs_env_19__ occ_bs_rng_20__ occ_join_points_21__ := env in
            Mk_OccEnv encl (Core.argOneShots (Id.idDemandInfo bndr)) occ_unf_act_17__
                      occ_rule_act_18__ occ_bs_env_19__ occ_bs_rng_20__ (zapJoinPointInfo
                       ctxt_join_points)
        end
    end.

#[global] Definition noBinderSwaps : OccEnv -> bool :=
  fun '(Mk_OccEnv _ _ _ _ bs_env _ _) => Core.isEmptyVarEnv bs_env.

#[global] Definition addLamCoVarOccs
   : UsageDetails -> list Core.Var -> UsageDetails :=
  fun uds bndrs =>
    let add :=
      fun bndr uds =>
        addManyOccs uds (GHC.Core.TyCo.FVs.coVarsOfType (Core.varType bndr)) in
    Data.Foldable.foldr add uds bndrs.

#[global] Definition isRhsEnv : OccEnv -> bool :=
  fun '(Mk_OccEnv cxt _ _ _ _ _ _) =>
    match cxt with
    | OccRhs => true
    | _ => false
    end.

#[global] Definition markAllMany : UsageDetails -> UsageDetails :=
  fun '((UD env _ _ _ as ud)) =>
    let 'UD ud_env_1__ ud_z_many_2__ ud_z_in_lam_3__ ud_z_tail_4__ := ud in
    UD ud_env_1__ env ud_z_in_lam_3__ ud_z_tail_4__.

#[global] Definition lookupOccInfo
   : UsageDetails -> Core.Id -> BasicTypes.OccInfo :=
  fun ud id => lookupOccInfoByUnique ud (Id.idUnique id).

#[global] Definition markNonTail : BasicTypes.OccInfo -> BasicTypes.OccInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | BasicTypes.IAmDead => BasicTypes.IAmDead
    | occ =>
        match occ with
        | BasicTypes.ManyOccs occ_tail_1__ =>
            BasicTypes.ManyOccs BasicTypes.NoTailCallInfo
        | BasicTypes.IAmDead =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | BasicTypes.OneOcc occ_in_lam_2__ occ_n_br_3__ occ_int_cxt_4__ occ_tail_5__ =>
            BasicTypes.OneOcc occ_in_lam_2__ occ_n_br_3__ occ_int_cxt_4__
                              BasicTypes.NoTailCallInfo
        | BasicTypes.IAmALoopBreaker occ_rules_only_6__ occ_tail_7__ =>
            BasicTypes.IAmALoopBreaker occ_rules_only_6__ BasicTypes.NoTailCallInfo
        end
    end.

#[global] Definition setBinderOcc
   : BasicTypes.OccInfo -> Core.CoreBndr -> Core.CoreBndr :=
  fun occ_info bndr =>
    if Core.isTyVar bndr : bool then bndr else
    if occ_info GHC.Base.== Id.idOccInfo bndr : bool then bndr else
    Id.setIdOccInfo bndr occ_info.

#[global] Definition tagLamBinder : UsageDetails -> Core.Id -> IdWithOccInfo :=
  fun usage bndr =>
    let occ := lookupOccInfo usage bndr in setBinderOcc (markNonTail occ) bndr.

Axiom occ_anal_lam_tail : OccEnv -> Core.CoreExpr -> WithUsageDetails Core.CoreExpr.

#[global] Definition occAnalLamTail
   : OccEnv -> Core.CoreExpr -> WithTailUsageDetails Core.CoreExpr :=
  fun env expr =>
    let 'WUD usage expr' := occ_anal_lam_tail env expr in
    WTUD (TUD (CoreArity.joinRhsArity expr) usage) expr'.

#[global] Definition addInScopeList {a}
   : OccEnv ->
     list Core.Var -> (OccEnv -> WithUsageDetails a) -> WithUsageDetails a :=
  fun env bndrs thing_inside =>
    if Data.Foldable.null bndrs : bool then thing_inside env else
    addInScope env bndrs thing_inside.

#[global] Definition markAllManyNonTail : UsageDetails -> UsageDetails :=
  markAllMany GHC.Base.∘ markAllNonTail.

Fixpoint occAnalList (arg_0__ : OccEnv) (arg_1__ : list Core.CoreExpr)
  : WithUsageDetails (list Core.CoreExpr)
  := match arg_0__, arg_1__ with
     | _, nil => WUD emptyDetails nil
     | env, cons e es =>
         let 'WUD uds2 es' := occAnalList env es in
         let 'WUD uds1 e' := occAnal env e in
         WUD (andUDs uds1 uds2) (cons e' es')
     end.

#[global] Definition occAnalRule
   : OccEnv ->
     Core.CoreRule -> (Core.CoreRule * UsageDetails * TailUsageDetails)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | env, (Core.Rule _ _ _ _ bndrs args rhs _ _ _ _ as rule) =>
        let rhs_ja := Coq.Lists.List.length args in
        let 'WUD rhs_uds rhs' := addInScopeList env bndrs (fun env =>
                                                             occAnal env rhs) in
        let rhs_uds' := markAllMany rhs_uds in
        let 'WUD lhs_uds args' := addInScopeList env bndrs (fun env =>
                                                              occAnalList env args) in
        let lhs_uds' := markAllManyNonTail lhs_uds in
        let rule' :=
          match rule with
          | Core.Rule ru_name_9__ ru_act_10__ ru_fn_11__ ru_rough_12__ ru_bndrs_13__
          ru_args_14__ ru_rhs_15__ ru_auto_16__ ru_origin_17__ ru_orphan_18__
          ru_local_19__ =>
              Core.Rule ru_name_9__ ru_act_10__ ru_fn_11__ ru_rough_12__ ru_bndrs_13__ args'
                        rhs' ru_auto_16__ ru_origin_17__ ru_orphan_18__ ru_local_19__
          | Core.BuiltinRule _ _ _ _ =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          end in
        pair (pair rule' lhs_uds') (TUD rhs_ja rhs_uds')
    | _, other_rule => pair (pair other_rule emptyDetails) (TUD #0 emptyDetails)
    end.

#[global] Definition occAnalUnfolding
   : OccEnv -> Core.Unfolding -> WithTailUsageDetails Core.Unfolding :=
  fun env unf => let 'unf := unf in WTUD (TUD #0 emptyDetails) unf.

#[global] Definition occAnalNonRecRhs
   : OccEnv ->
     ImpRuleEdges ->
     Outputable.JoinPointHood ->
     Core.Id ->
     Core.CoreExpr -> (list UsageDetails * Core.Id * Core.CoreExpr)%type :=
  fun env imp_rule_edges mb_join bndr rhs =>
    let imp_rule_infos := lookupImpRules imp_rule_edges bndr in
    let imp_rule_uds := cons (impRulesScopeUsage imp_rule_infos) nil in
    let rules := Id.idCoreRules bndr in
    let unf := Id.idUnfolding bndr in
    let rhs_ctxt := mkNonRecRhsCtxt bndr unf in
    let rhs_env :=
      mkRhsOccEnv env BasicTypes.NonRecursive rhs_ctxt mb_join bndr rhs in
    let 'WUD adj_rhs_uds final_rhs := adjustNonRecRhs mb_join (occAnalLamTail
                                                               rhs_env rhs) in
    let 'WTUD unf_tuds unf1 := occAnalUnfolding rhs_env unf in
    let final_bndr_no_rules :=
      if noBinderSwaps env : bool then bndr else
      Id.setIdUnfolding bndr unf1 in
    let adj_unf_uds := adjustTailArity mb_join unf_tuds in
    let rules_w_uds := GHC.Base.map (occAnalRule rhs_env) rules in
    let rules' := GHC.Base.map Util.fstOf3 rules_w_uds in
    let final_bndr_with_rules :=
      if noBinderSwaps env : bool then bndr else
      Id.setIdUnfolding (Id.setIdSpecialisation bndr (CoreFVs.mkRuleInfo rules'))
                        unf1 in
    let adj_rule_uds : list UsageDetails :=
      Coq.Init.Datatypes.app imp_rule_uds (let cont_15__ arg_16__ :=
                                let 'pair (pair _ l) r := arg_16__ in
                                cons (andUDs l (adjustTailArity mb_join r)) nil in
                              Coq.Lists.List.flat_map cont_15__ rules_w_uds) in
    if andb (Data.Foldable.null rules) (Data.Foldable.null imp_rule_infos) : bool
    then pair (pair (cons adj_rhs_uds (cons adj_unf_uds nil)) final_bndr_no_rules)
              final_rhs else
    pair (pair (cons adj_rhs_uds (cons adj_unf_uds adj_rule_uds))
               final_bndr_with_rules) final_rhs.

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

#[global] Definition betterLB : NodeScore -> NodeScore -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair (pair rank1 size1) lb1, pair (pair rank2 size2) _ =>
        if rank1 GHC.Base.< rank2 : bool then true else
        if rank1 GHC.Base.> rank2 : bool then false else
        if size1 GHC.Base.< size2 : bool then false else
        if size1 GHC.Base.> size2 : bool then true else
        if lb1 : bool then true else
        false
    end.

#[global] Definition rank : NodeScore -> nat :=
  fun '(pair (pair r _) _) => r.

Fixpoint chooseLoopBreaker (arg_0__ : bool) (arg_1__ : NodeScore) (arg_2__
                            arg_3__ arg_4__
                             : list LoopBreakerNode) : (list LoopBreakerNode * list LoopBreakerNode)%type
  := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
     | _, _, loop_nodes, acc, nil => pair loop_nodes acc
     | approx_lb, loop_sc, loop_nodes, acc, cons node nodes =>
         let sc := snd_score (Digraph.node_payload node) in
         if andb approx_lb (rank sc GHC.Base.== rank loop_sc) : bool
         then chooseLoopBreaker approx_lb loop_sc (cons node loop_nodes) acc nodes else
         if betterLB sc loop_sc : bool
         then chooseLoopBreaker approx_lb sc (cons node nil) (Coq.Init.Datatypes.app
                                                              loop_nodes acc) nodes else
         chooseLoopBreaker approx_lb loop_sc loop_nodes (cons node acc) nodes
     end.

#[global] Definition restrictFreeVars
   : Core.VarSet -> OccInfoEnv -> Core.VarSet :=
  fun bndrs fvs => UniqSet.restrictUniqSetToUFM bndrs fvs.

#[global] Definition udFreeVars : Core.VarSet -> UsageDetails -> Core.VarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | bndrs, UD env _ _ _ => restrictFreeVars bndrs env
    end.

#[global] Definition makeNode
   : OccEnv ->
     ImpRuleEdges -> Core.VarSet -> (Core.Var * Core.CoreExpr)%type -> LetrecNode :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | env, imp_rule_edges, bndr_set, pair bndr rhs =>
        let add_rule :=
          fun arg_4__ arg_5__ =>
            match arg_4__, arg_5__ with
            | pair (pair _ _) rhs_uds, fvs =>
                Core.unionVarSet (udFreeVars bndr_set rhs_uds) fvs
            end in
        let add_rule_uds :=
          fun arg_8__ arg_9__ =>
            match arg_8__, arg_9__ with
            | pair (pair _ l) r, uds => andUDs (andUDs l r) uds
            end in
        let imp_rule_info := lookupImpRules imp_rule_edges bndr in
        let imp_rule_uds := impRulesScopeUsage imp_rule_info in
        let is_active := occ_rule_act env : BasicTypes.Activation -> bool in
        let imp_rule_fvs := impRulesActiveFvs is_active bndr_set imp_rule_info in
        let add_active_rule :=
          fun arg_16__ arg_17__ =>
            match arg_16__, arg_17__ with
            | pair (pair rule _) rhs_uds, fvs =>
                if is_active (Core.ruleActivation rule) : bool
                then Core.unionVarSet (udFreeVars bndr_set rhs_uds) fvs else
                fvs
            end in
        let unf := Id.realIdUnfolding bndr in
        let rhs_env :=
          mkRhsOccEnv env BasicTypes.Recursive OccRhs (Id.idJoinPointHood bndr) bndr
          rhs in
        let 'WTUD (TUD rhs_ja unadj_rhs_uds) rhs' := occAnalLamTail rhs_env rhs in
        let 'WTUD unf_tuds unf' := occAnalUnfolding rhs_env unf in
        let adj_unf_uds := adjustTailArity (Outputable.JoinPoint rhs_ja) unf_tuds in
        let rules_w_uds : list (Core.CoreRule * UsageDetails * UsageDetails)%type :=
          Coq.Lists.List.flat_map (fun rule =>
                                     let 'pair (pair r l) rhs_wuds := occAnalRule rhs_env rule in
                                     cons (pair (pair r l) (adjustTailArity (Outputable.JoinPoint rhs_ja) rhs_wuds))
                                          nil) (Id.idCoreRules bndr) in
        let rules' := GHC.Base.map Util.fstOf3 rules_w_uds in
        let adj_rule_uds := Data.Foldable.foldr add_rule_uds imp_rule_uds rules_w_uds in
        let active_rule_fvs :=
          Data.Foldable.foldr add_active_rule imp_rule_fvs rules_w_uds in
        let weak_fvs := Data.Foldable.foldr add_rule Core.emptyVarSet rules_w_uds in
        let unadj_inl_uds := andUDs unadj_rhs_uds adj_unf_uds in
        let unadj_scope_uds := andUDs unadj_inl_uds adj_rule_uds in
        let scope_fvs := udFreeVars bndr_set unadj_scope_uds in
        let inl_fvs := udFreeVars bndr_set unadj_inl_uds in
        let bndr' :=
          if noBinderSwaps env : bool then bndr else
          Id.setIdSpecialisation (Id.setIdUnfolding bndr unf') (CoreFVs.mkRuleInfo
                                  rules') in
        let details :=
          ND bndr' (WTUD (TUD rhs_ja unadj_scope_uds) rhs') inl_fvs (andb
              (Data.Foldable.null rules_w_uds) (Data.Foldable.null imp_rule_info)) weak_fvs
             active_rule_fvs in
        Digraph.DigraphNode details (Core.varUnique bndr) (UniqSet.nonDetKeysUniqSet
                             scope_fvs)
    end.

#[global] Definition extendFvs
   : Core.VarEnv Core.VarSet -> Core.VarSet -> (Core.VarSet * bool)%type :=
  fun env s =>
    let extras : Core.VarSet :=
      UniqFM.nonDetStrictFoldUFM Core.unionVarSet Core.emptyVarSet
      (UniqFM.intersectUFM_C (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | x, _ => x
                                end) env (UniqSet.getUniqSet s)) in
    if UniqFM.isNullUFM env : bool then pair s true else
    pair (Core.unionVarSet s extras) (Core.subVarSet extras s).

#[global] Definition extendFvs_
   : Core.VarEnv Core.VarSet -> Core.VarSet -> Core.VarSet :=
  fun env s => Data.Tuple.fst (extendFvs env s).

Axiom cheapExprSize : Core.CoreExpr -> nat.

#[global] Definition nodeScore
   : OccEnv -> Core.Id -> Core.VarSet -> NodeDetails -> NodeScore :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | env, new_bndr, lb_deps, ND old_bndr (WTUD _ bind_rhs) _ _ _ _ =>
        let fix is_con_app arg_4__
          := match arg_4__ with
             | Core.Mk_Var v => Id.isConLikeId v
             | Core.App f _ => is_con_app f
             | Core.Lam _ e => is_con_app e
             | Core.Let _ e => is_con_app e
             | _ => false
             end in
        let old_unf := Id.realIdUnfolding old_bndr in
        let can_unfold := Core.canUnfold old_unf in
        let rhs := bind_rhs in
        let rhs_size := cheapExprSize rhs in
        let is_lb := BasicTypes.isStrongLoopBreaker (Id.idOccInfo old_bndr) in
        let mk_score : nat -> NodeScore :=
          fun rank => pair (pair rank rhs_size) is_lb in
        if negb (Core.isId old_bndr) : bool then pair (pair #100 #0) false else
        if Core.elemVarSet old_bndr lb_deps : bool then pair (pair #0 #0) true else
        if negb (occ_unf_act env old_bndr) : bool then pair (pair #0 #0) true else
        if CoreUtils.exprIsTrivial rhs : bool then mk_score #10 else
        if is_con_app rhs : bool then mk_score #5 else
        if andb (Core.isStableUnfolding old_unf) can_unfold : bool then mk_score #3 else
        if BasicTypes.isOneOcc (Id.idOccInfo new_bndr) : bool then mk_score #2 else
        if can_unfold : bool then mk_score #1 else
        pair (pair #0 #0) is_lb
    end.

#[global] Definition lookupTailCallInfo
   : UsageDetails -> Core.Id -> BasicTypes.TailCallInfo :=
  fun uds id =>
    match uds with
    | UD env _ _ z_tail =>
        if negb (Core.elemVarEnv id z_tail) : bool
        then match Core.lookupVarEnv env id with
             | Some occ => localTailCallInfo occ
             | _ => BasicTypes.NoTailCallInfo
             end else
        BasicTypes.NoTailCallInfo
    end.

#[global] Definition okForJoinPoint
   : BasicTypes.TopLevelFlag -> Core.Id -> BasicTypes.TailCallInfo -> bool :=
  fun lvl bndr tail_call_info =>
    let ok_unfolding := fun arg_0__ arg_1__ => true in
    let lost_join_doc := Panic.someSDoc in
    let ok_rule :=
      fun arg_3__ arg_4__ =>
        match arg_3__, arg_4__ with
        | _, Core.BuiltinRule _ _ _ _ => false
        | join_arity, Core.Rule _ _ _ _ _ args _ _ _ _ _ =>
            Util.lengthIs args join_arity
        end in
    let valid_join :=
      match lvl with
      | BasicTypes.NotTopLevel =>
          match tail_call_info with
          | BasicTypes.AlwaysTailCalled arity =>
              if andb (Data.Foldable.all (ok_rule arity) (Id.idCoreRules bndr)) (andb
                       (ok_unfolding arity (Id.realIdUnfolding bndr)) (Core.isValidJoinPointType arity
                        (Id.idType bndr))) : bool
              then true else
              false
          | _ => false
          end
      | _ => false
      end in
    let lost_join :=
      match Id.idJoinPointHood bndr with
      | Outputable.JoinPoint ja =>
          orb (negb valid_join) (match tail_call_info with
               | BasicTypes.AlwaysTailCalled ja' => ja GHC.Base./= ja'
               | _ => false
               end)
      | _ => false
      end in
    if Id.isJoinId bndr : bool
    then GHC.Utils.Trace.warnPprTrace lost_join (GHC.Base.hs_string__
                                       "Lost join point") lost_join_doc true else
    if valid_join : bool then true else
    false.

#[global] Definition decideRecJoinPointHood
   : BasicTypes.TopLevelFlag -> UsageDetails -> list Core.CoreBndr -> bool :=
  fun lvl usage bndrs =>
    let ok := fun bndr => okForJoinPoint lvl bndr (lookupTailCallInfo usage bndr) in
    Data.Foldable.all ok bndrs.

#[global] Definition tagRecBinders
   : BasicTypes.TopLevelFlag ->
     UsageDetails -> list NodeDetails -> WithUsageDetails (list IdWithOccInfo) :=
  fun lvl body_uds details_s =>
    let test_manifest_arity :=
      fun '(ND _ (WTUD tuds rhs) _ _ _ _) =>
        adjustTailArity (Outputable.JoinPoint (CoreArity.joinRhsArity rhs)) tuds in
    let unadj_uds :=
      Data.Foldable.foldr (andUDs GHC.Base.∘ test_manifest_arity) body_uds
      details_s in
    let bndrs := GHC.Base.map nd_bndr details_s in
    let will_be_joins := decideRecJoinPointHood lvl unadj_uds bndrs in
    let mb_join_arity : Core.Id -> Outputable.JoinPointHood :=
      fun bndr =>
        if will_be_joins : bool
        then match lookupTailCallInfo unadj_uds bndr with
             | BasicTypes.AlwaysTailCalled arity => Outputable.JoinPoint arity
             | _ => Outputable.NotJoinPoint
             end else
        Outputable.NotJoinPoint in
    let rhs_udss' :=
      let cont_7__ arg_8__ :=
        let 'ND bndr rhs_wuds _ _ _ _ := arg_8__ in
        cons (adjustTailUsage (mb_join_arity bndr) rhs_wuds) nil in
      Coq.Lists.List.flat_map cont_7__ details_s in
    let adj_uds := Data.Foldable.foldr andUDs body_uds rhs_udss' in
    let bndrs' :=
      Coq.Lists.List.flat_map (fun bndr =>
                                 cons (setBinderOcc (lookupLetOccInfo adj_uds bndr) bndr) nil) bndrs in
    WUD adj_uds bndrs'.

Axiom transClosureFV : Core.VarEnv Core.VarSet -> Core.VarEnv Core.VarSet.

#[global] Definition mkLoopBreakerNodes
   : OccEnv ->
     BasicTypes.TopLevelFlag ->
     UsageDetails -> list NodeDetails -> WithUsageDetails (list LoopBreakerNode) :=
  fun env lvl body_uds details_s =>
    let rule_fv_env : Core.IdEnv Core.IdSet :=
      transClosureFV (Core.mkVarEnv (let cont_0__ arg_1__ :=
                                       let 'ND b _ _ _ _ rule_fvs := arg_1__ in
                                       if negb (Core.isEmptyVarSet rule_fvs) : bool
                                       then cons (pair b rule_fvs) nil else
                                       nil in
                                     Coq.Lists.List.flat_map cont_0__ details_s)) in
    let mk_lb_node :=
      fun arg_3__ arg_4__ =>
        match arg_3__, arg_4__ with
        | (ND old_bndr (WTUD _ rhs) inl_fvs _ _ _ as nd), new_bndr =>
            let lb_deps := extendFvs_ rule_fv_env inl_fvs in
            let score := nodeScore env new_bndr lb_deps nd in
            let simple_nd := SND new_bndr rhs score in
            Digraph.DigraphNode simple_nd (Core.varUnique old_bndr)
                                (UniqSet.nonDetKeysUniqSet lb_deps)
        end in
    let 'WUD final_uds bndrs' := tagRecBinders lvl body_uds details_s in
    WUD final_uds (Util.zipWithEqual (GHC.Base.hs_string__ "mkLoopBreakerNodes")
                   mk_lb_node details_s bndrs').

#[global] Definition maxExprSize : nat :=
  #20.

#[global] Definition zapLambdaBndrs
   : Core.CoreExpr -> BasicTypes.FullArgCount -> Core.CoreExpr :=
  fun fun_ arg_count =>
    let zap_bndr :=
      fun b => if Core.isTyVar b : bool then b else Id.zapLamIdInfo b in
    let zap : BasicTypes.FullArgCount -> Core.CoreExpr -> option Core.CoreExpr :=
      fix zap (arg_2__ : BasicTypes.FullArgCount) (arg_3__ : Core.CoreExpr) : option
                                                                              Core.CoreExpr
        := match arg_2__, arg_3__ with
           | num_4__, e =>
               let j_7__ :=
                 match arg_2__, arg_3__ with
                 | n, Core.Cast e co =>
                     zap n e GHC.Base.>>= (fun e' => GHC.Base.return_ (Core.Cast e' co))
                 | n, Core.Lam b e =>
                     zap (n GHC.Num.- #1) e GHC.Base.>>=
                     (fun e' => GHC.Base.return_ (Core.Lam (zap_bndr b) e'))
                 | _, _ => None
                 end in
               let j_8__ := if num_4__ GHC.Base.== #0 : bool then Some e else j_7__ in
               if num_4__ GHC.Base.== #0 : bool
               then if isOneShotFun e : bool then None else
                    j_8__ else
               j_8__
           end in
    Maybes.orElse (zap arg_count fun_) fun_.

Axiom occAnalArgs : OccEnv ->
                    Core.CoreExpr ->
                    list Core.CoreExpr -> list OneShots -> WithUsageDetails Core.CoreExpr.

#[global] Definition addAppCtxt
   : OccEnv -> list (Core.Arg Core.CoreBndr) -> OccEnv :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_OccEnv _ ctxt _ _ _ _ _ as env), args =>
        let n_val_args := Core.valArgCount args in
        if n_val_args GHC.Base.> #0 : bool
        then let 'Mk_OccEnv occ_encl_3__ occ_one_shots_4__ occ_unf_act_5__
                occ_rule_act_6__ occ_bs_env_7__ occ_bs_rng_8__ occ_join_points_9__ := env in
             Mk_OccEnv OccVanilla (Coq.Init.Datatypes.app (Coq.Lists.List.repeat
                                                           BasicTypes.OneShotLam n_val_args) ctxt) occ_unf_act_5__
                       occ_rule_act_6__ occ_bs_env_7__ occ_bs_rng_8__ occ_join_points_9__ else
        env
    end.

Axiom lookupBndrSwap : OccEnv -> Core.Id -> (Core.CoreExpr * Core.Id)%type.

#[global] Definition mkOneOcc
   : OccEnv ->
     Core.Id -> BasicTypes.InterestingCxt -> BasicTypes.JoinArity -> UsageDetails :=
  fun env id int_cxt arity =>
    let occ := OneOccL #1 (BasicTypes.AlwaysTailCalled arity) int_cxt in
    if negb (Core.isLocalId id) : bool then emptyDetails else
    match Core.lookupVarEnv (occ_join_points env) id with
    | Some join_uds =>
        Panic.assertPpr (negb (Core.isEmptyVarEnv join_uds)) (Panic.someSDoc)
        (mkSimpleDetails (Core.extendVarEnv join_uds id occ))
    | _ => mkSimpleDetails (Core.unitVarEnv id occ)
    end.

#[global] Definition occAnalApp
   : OccEnv ->
     (Core.Expr Core.CoreBndr * list (Core.Arg Core.CoreBndr) *
      list GHC.Types.Tickish.CoreTickish)%type ->
     WithUsageDetails (Core.Expr Core.CoreBndr) :=
  fun arg_0__ arg_1__ =>
    let j_20__ :=
      match arg_0__, arg_1__ with
      | env, pair (pair (Core.Mk_Var fun_id) args) ticks =>
          let n_args := Coq.Lists.List.length args in
          let n_val_args := Core.valArgCount args in
          let int_cxt :=
            match occ_encl env with
            | OccScrut => BasicTypes.IsInteresting
            | _other =>
                if n_val_args GHC.Base.> #0 : bool then BasicTypes.IsInteresting else
                BasicTypes.NotInteresting
            end in
          let is_exp := CoreUtils.isExpandableApp fun_id n_val_args in
          let guaranteed_val_args :=
            n_val_args GHC.Num.+
            Coq.Lists.List.length (GHC.List.takeWhile BasicTypes.isOneShotInfo
                                   (occ_one_shots env)) in
          let one_shots := Core.argsOneShots (Id.idDmdSig fun_id) guaranteed_val_args in
          let 'pair fun' fun_id' := lookupBndrSwap env fun_id in
          let 'WUD args_uds app' := occAnalArgs env fun' args one_shots in
          let final_args_uds :=
            markAllNonTail (markAllInsideLamIf (andb (isRhsEnv env) is_exp) args_uds) in
          let fun_uds := mkOneOcc env fun_id' int_cxt n_args in
          let all_uds := andUDs fun_uds final_args_uds in WUD all_uds (app')
      | env, pair (pair fun_ args) ticks =>
          let 'WUD fun_uds fun' := occAnal (addAppCtxt env args) fun_ in
          let 'WUD args_uds app' := occAnalArgs env fun' args nil in
          WUD (markAllNonTail (andUDs fun_uds args_uds)) (app')
      end in
    match arg_0__, arg_1__ with
    | env, pair (pair (Core.Mk_Var fun_) args) ticks =>
        if Unique.hasKey fun_ PrelNames.runRWKey : bool
        then match args with
             | cons t1 (cons t2 (cons arg nil)) =>
                 match adjustNonRecRhs (Outputable.JoinPoint #1) (occAnalLamTail env arg) with
                 | WUD usage arg' =>
                     WUD usage (Core.mkApps (Core.Mk_Var fun_) (cons t1 (cons t2 (cons arg' nil))))
                 end
             | _ => j_20__
             end else
        j_20__
    | _, _ => j_20__
    end.

#[global] Definition setNonTailCtxt : OccEncl -> OccEnv -> OccEnv :=
  fun ctxt env =>
    let 'Mk_OccEnv occ_encl_0__ occ_one_shots_1__ occ_unf_act_2__ occ_rule_act_3__
       occ_bs_env_4__ occ_bs_rng_5__ occ_join_points_6__ := env in
    Mk_OccEnv ctxt nil occ_unf_act_2__ occ_rule_act_3__ occ_bs_env_4__
              occ_bs_rng_5__ (zapJoinPointInfo (occ_join_points env)).

#[global] Definition setScrutCtxt : OccEnv -> list Core.CoreAlt -> OccEnv :=
  fun env alts =>
    let interesting_alts :=
      match alts with
      | nil => false
      | cons alt nil => negb (CoreUtils.isDefaultAlt alt)
      | _ => true
      end in
    let encl := if interesting_alts : bool then OccScrut else OccVanilla in
    setNonTailCtxt encl env.

#[global] Definition setTailCtxt : OccEnv -> OccEnv :=
  fun '(Mk_OccEnv occ_encl_0__ occ_one_shots_1__ occ_unf_act_2__ occ_rule_act_3__
  occ_bs_env_4__ occ_bs_rng_5__ occ_join_points_6__) =>
    Mk_OccEnv OccVanilla occ_one_shots_1__ occ_unf_act_2__ occ_rule_act_3__
              occ_bs_env_4__ occ_bs_rng_5__ occ_join_points_6__.

#[global] Definition setOneShots : OneShots -> OccEnv -> OccEnv :=
  fun os env =>
    if Data.Foldable.null os : bool then env else
    let 'Mk_OccEnv occ_encl_0__ occ_one_shots_1__ occ_unf_act_2__ occ_rule_act_3__
       occ_bs_env_4__ occ_bs_rng_5__ occ_join_points_6__ := env in
    Mk_OccEnv occ_encl_0__ os occ_unf_act_2__ occ_rule_act_3__ occ_bs_env_4__
              occ_bs_rng_5__ occ_join_points_6__.

#[global] Definition mkZeroedForm : UsageDetails -> OccInfoEnv :=
  fun '(UD rhs_occs _ _ _) =>
    let do_one : LocalOcc -> option LocalOcc :=
      fun arg_1__ =>
        match arg_1__ with
        | ManyOccL _ => None
        | (OneOccL _ _ _ as occ) =>
            Some (match occ with
                  | OneOccL lo_n_br_2__ lo_tail_3__ lo_int_cxt_4__ =>
                      OneOccL #0 lo_tail_3__ lo_int_cxt_4__
                  | ManyOccL _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
                  end)
        end in
    UniqFM.mapMaybeUFM do_one rhs_occs.

#[global] Definition addJoinPoint
   : OccEnv -> Core.Id -> UsageDetails -> OccEnv :=
  fun env bndr rhs_uds =>
    let zeroed_form := mkZeroedForm rhs_uds in
    if Core.isEmptyVarEnv zeroed_form : bool then env else
    let 'Mk_OccEnv occ_encl_1__ occ_one_shots_2__ occ_unf_act_3__ occ_rule_act_4__
       occ_bs_env_5__ occ_bs_rng_6__ occ_join_points_7__ := env in
    Mk_OccEnv occ_encl_1__ occ_one_shots_2__ occ_unf_act_3__ occ_rule_act_4__
              occ_bs_env_5__ occ_bs_rng_6__ (Core.extendVarEnv (occ_join_points env) bndr
               zeroed_form).

#[global] Definition scrutBinderSwap_maybe
   : Core.OutExpr -> option (Core.OutVar * Core.MCoercion)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.Mk_Var v => Some (pair v Core.MRefl)
    | Core.Cast (Core.Mk_Var v) co =>
        if negb (GHC.Core.Predicate.isDictId v) : bool
        then Some (pair v (Core.MCo (Core.mkSymCo co))) else
        None
    | _ => None
    end.

#[global] Definition addBndrSwap
   : Core.OutExpr -> Core.Id -> OccEnv -> OccEnv :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | scrut, case_bndr, (Mk_OccEnv _ _ _ _ swap_env rng_vars _ as env) =>
        let case_bndr' := Id.zapIdOccInfo case_bndr in
        match scrutBinderSwap_maybe scrut with
        | Some (pair scrut_var mco) =>
            if scrut_var GHC.Base./= case_bndr : bool
            then let 'Mk_OccEnv occ_encl_4__ occ_one_shots_5__ occ_unf_act_6__
                    occ_rule_act_7__ occ_bs_env_8__ occ_bs_rng_9__ occ_join_points_10__ := env in
                 Mk_OccEnv occ_encl_4__ occ_one_shots_5__ occ_unf_act_6__ occ_rule_act_7__
                           (Core.extendVarEnv swap_env scrut_var (pair case_bndr' mco)) (Core.unionVarSet
                            (Core.extendVarSet rng_vars case_bndr') (GHC.Core.TyCo.FVs.tyCoVarsOfMCo mco))
                           occ_join_points_10__ else
            env
        | _ => env
        end
    end.

#[global] Definition orLocalOcc : LocalOcc -> LocalOcc -> LocalOcc :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | OneOccL nbr1 tci1 int_cxt1, OneOccL nbr2 tci2 int_cxt2 =>
        OneOccL (nbr1 GHC.Num.+ nbr2) (andTailCallInfo tci1 tci2) (GHC.Base.mappend
                 int_cxt1 int_cxt2)
    | occ1, occ2 => andLocalOcc occ1 occ2
    end.

#[global] Definition orUDs : UsageDetails -> UsageDetails -> UsageDetails :=
  combineUsageDetailsWith orLocalOcc.

#[global] Definition isEmptyDetails : UsageDetails -> bool :=
  fun '(UD env _ _ _) => Core.isEmptyVarEnv env.

#[global] Definition tagLamBinders
   : UsageDetails -> list Core.Id -> list IdWithOccInfo :=
  fun usage binders => GHC.Base.map (tagLamBinder usage) binders.

#[global] Definition tagNonRecBinder
   : BasicTypes.TopLevelFlag ->
     BasicTypes.OccInfo ->
     Core.CoreBndr -> (IdWithOccInfo * Outputable.JoinPointHood)%type :=
  fun lvl occ bndr =>
    let zapped_occ := markNonTail occ in
    let tail_call_info := BasicTypes.tailCallInfo occ in
    let j_2__ := pair (setBinderOcc zapped_occ bndr) Outputable.NotJoinPoint in
    if okForJoinPoint lvl bndr tail_call_info : bool
    then match tail_call_info with
         | BasicTypes.AlwaysTailCalled ar =>
             pair (setBinderOcc occ bndr) (Outputable.JoinPoint ar)
         | _ => j_2__
         end else
    j_2__.

(* External variables:
     None Some andb bool cons false list nat negb nil op_zt__ option orb pair true
     BasicTypes.Activation BasicTypes.AlwaysTailCalled BasicTypes.BranchCount
     BasicTypes.FullArgCount BasicTypes.IAmALoopBreaker BasicTypes.IAmDead
     BasicTypes.InterestingCxt BasicTypes.IsInsideLam BasicTypes.IsInteresting
     BasicTypes.JoinArity BasicTypes.ManyOccs BasicTypes.NoOneShotInfo
     BasicTypes.NoTailCallInfo BasicTypes.NonRecursive BasicTypes.NotInsideLam
     BasicTypes.NotInteresting BasicTypes.NotTopLevel BasicTypes.OccInfo
     BasicTypes.OneOcc BasicTypes.OneShotInfo BasicTypes.OneShotLam
     BasicTypes.RecFlag BasicTypes.Recursive BasicTypes.TailCallInfo
     BasicTypes.TopLevelFlag BasicTypes.isAlwaysActive BasicTypes.isOneOcc
     BasicTypes.isOneShotInfo BasicTypes.isStrongLoopBreaker BasicTypes.noOccInfo
     BasicTypes.tailCallInfo Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     Coq.Lists.List.length Coq.Lists.List.repeat Core.App Core.Arg Core.BuiltinRule
     Core.Cast Core.CoreAlt Core.CoreBind Core.CoreBndr Core.CoreExpr
     Core.CoreProgram Core.CoreRule Core.Expr Core.Id Core.IdEnv Core.IdSet Core.Lam
     Core.Let Core.MCo Core.MCoercion Core.MRefl Core.Mk_Var Core.OutExpr Core.OutId
     Core.OutVar Core.Rule Core.Unfolding Core.Var Core.VarEnv Core.VarSet
     Core.argOneShots Core.argsOneShots Core.canUnfold Core.delVarEnvList
     Core.elemVarEnv Core.elemVarEnvByKey Core.elemVarSet Core.emptyVarEnv
     Core.emptyVarSet Core.extendVarEnv Core.extendVarSet Core.intersectVarSet
     Core.intersectsVarSet Core.isEmptyVarEnv Core.isEmptyVarSet Core.isExportedId
     Core.isId Core.isLocalId Core.isStableUnfolding Core.isTyVar
     Core.isValidJoinPointType Core.lookupVarEnv Core.lookupVarEnv_Directly
     Core.mkApps Core.mkSymCo Core.mkVarEnv Core.mkVarSet
     Core.nonDetStrictFoldVarEnv_Directly Core.plusVarEnv Core.plusVarEnv_C
     Core.ruleActivation Core.subVarSet Core.unionVarSet Core.unitVarEnv
     Core.valArgCount Core.varType Core.varUnique CoreArity.isOneShotBndr
     CoreArity.joinRhsArity CoreFVs.mkRuleInfo CoreUtils.exprIsTrivial
     CoreUtils.isDefaultAlt CoreUtils.isExpandableApp CoreUtils.mkCastMCo
     Data.Foldable.all Data.Foldable.foldl' Data.Foldable.foldr Data.Foldable.null
     Data.Tuple.fst Digraph.DigraphNode Digraph.Node Digraph.node_payload
     GHC.Base.map GHC.Base.mappend GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zg__ GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zsze__
     GHC.Base.return_ GHC.Core.Predicate.isDictId GHC.Core.TyCo.FVs.coVarsOfCo
     GHC.Core.TyCo.FVs.coVarsOfType GHC.Core.TyCo.FVs.tyCoVarsOfMCo GHC.Err.error
     GHC.List.takeWhile GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__
     GHC.Types.Tickish.CoreTickish GHC.Utils.Trace.warnPprTrace
     HsToCoq.Err.Build_Default HsToCoq.Err.Default HsToCoq.Err.default Id.idCoreRules
     Id.idDemandInfo Id.idDmdSig Id.idInlineActivation Id.idJoinPointHood
     Id.idOccInfo Id.idType Id.idUnfolding Id.idUnique Id.isConLikeId Id.isJoinId
     Id.realIdUnfolding Id.setIdOccInfo Id.setIdSpecialisation Id.setIdUnfolding
     Id.updOneShotInfo Id.zapIdOccInfo Id.zapLamIdInfo Maybes.orElse Module.Module
     Outputable.JoinPoint Outputable.JoinPointHood Outputable.NotJoinPoint
     Panic.assertPpr Panic.someSDoc PrelNames.runRWKey UniqFM.UniqFM
     UniqFM.disjointUFM UniqFM.intersectUFM_C UniqFM.isNullUFM UniqFM.mapMaybeUFM
     UniqFM.minusUFM UniqFM.nonDetStrictFoldUFM UniqFM.nonDetStrictFoldUFM_Directly
     UniqSet.elemUniqSet_Directly UniqSet.getUniqSet UniqSet.nonDetKeysUniqSet
     UniqSet.nonDetStrictFoldUniqSet UniqSet.restrictUniqSetToUFM Unique.Unique
     Unique.hasKey Util.fstOf3 Util.lengthIs Util.zipWithEqual
*)
