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
Require Core.
Require CoreUtils.
Require Data.Foldable.
Require Data.Maybe.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Core.TyCo.Tidy.
Require GHC.List.
Require GHC.Prim.
Require GHC.Types.Tickish.
Require HsToCoq.Err.
Require Id.
Require Maybes.
Require Name.
Require NameSet.
Require OccName.
Require Panic.
Require SrcLoc.
Require UniqFM.
Require Unique.
Require Util.

(* No type declarations to convert. *)

(* Converted value declarations: *)

#[global] Definition op_zeZC__ {a} {b} : a -> (a -> b) -> b :=
  fun m k => GHC.Prim.seq m (k m).

Notation "'_=:_'" := (op_zeZC__).

Infix "=:" := (_=:_) (at level 99).

#[global] Definition tidyIdBndr
   : Core.TidyEnv -> Core.Id -> (Core.TidyEnv * Core.Id)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (pair tidy_env var_env as env), id =>
        let 'pair tidy_env' occ' := OccName.tidyOccName tidy_env (Name.getOccName id) in
        let old_info := Core.idInfo id in
        let old_unf := Core.realUnfoldingInfo old_info in
        let new_unf := Core.trimUnfolding old_unf in
        let new_info :=
          Core.setOneShotInfo (Core.setUnfoldingInfo (Core.setOccInfo Core.vanillaIdInfo
                                                                      (Core.occInfo old_info)) new_unf)
                              (Core.oneShotInfo old_info) in
        let name' := Name.mkInternalName (Id.idUnique id) occ' SrcLoc.noSrcSpan in
        let mult' := GHC.Core.TyCo.Tidy.tidyType env (Id.idMult id) in
        let ty' := GHC.Core.TyCo.Tidy.tidyType env (Id.idType id) in
        let id' := Id.mkLocalIdWithInfo name' mult' ty' new_info in
        let var_env' := Core.extendVarEnv var_env id id' in
        pair (pair tidy_env' var_env') id'
    end.

#[global] Definition tidyBndr
   : Core.TidyEnv -> Core.Var -> (Core.TidyEnv * Core.Var)%type :=
  fun env var =>
    if Core.isTyCoVar var : bool then GHC.Core.TyCo.Tidy.tidyVarBndr env var else
    tidyIdBndr env var.

#[global] Definition tidyBndrs
   : Core.TidyEnv -> list Core.Var -> (Core.TidyEnv * list Core.Var)%type :=
  fun env vars => Data.Traversable.mapAccumL tidyBndr env vars.

#[global] Definition computeCbvInfo `{GHC.Prim.HasCallStack}
   : Core.Id -> Core.CoreExpr -> Core.Id :=
  fun fun_id rhs =>
    let mkMark :=
      fun arg =>
        if negb (CoreUtils.shouldUseCbvForId arg) : bool
        then BasicTypes.NotMarkedCbv else
        if andb (Core.isStrUsedDmd (Id.idDemandInfo arg)) (negb (Id.isDeadEndId
                                                                 fun_id)) : bool
        then BasicTypes.MarkedCbv else
        BasicTypes.NotMarkedCbv in
    let isSingleUnarisedArg :=
      fun v =>
        let isSimplePrimRep :=
          fun arg_2__ =>
            match arg_2__ with
            | nil => true
            | cons _ nil => true
            | _ => false
            end in
        let ty := Id.idType v in
        if Core.isUnboxedSumType ty : bool then false else
        if Core.isUnboxedTupleType ty : bool
        then isSimplePrimRep (RepType.typePrimRep ty) else
        isSimplePrimRep (RepType.typePrimRep ty) in
    let valid_unlifted_worker :=
      fun args => Data.Foldable.all isSingleUnarisedArg args in
    let is_wkr_like := Id.isWorkerLikeId fun_id in
    let mb_join_id := Id.idJoinPointHood fun_id in
    let lam_bndrs :=
      match mb_join_id with
      | Outputable.JoinPoint join_arity =>
          Data.Tuple.fst (Core.collectNBinders join_arity rhs)
      | _ => Data.Tuple.fst (Core.collectBinders rhs)
      end in
    let val_args := GHC.List.filter Core.isId lam_bndrs in
    let cbv_marks :=
      Panic.assertPpr (Data.Maybe.maybe true Data.Foldable.null (Id.idCbvMarks_maybe
                                                                 fun_id)) (GHC.Base.mappend Panic.someSDoc
                                                                                            (Panic.someSDoc))
      (GHC.Base.map mkMark val_args) in
    let cbv_bndr :=
      if Data.Foldable.any BasicTypes.isMarkedCbv cbv_marks : bool
      then Util.seqList cbv_marks (Id.setIdCbvMarks fun_id cbv_marks) else
      Id.asNonWorkerLikeId fun_id in
    if andb (orb is_wkr_like (Outputable.isJoinPoint mb_join_id))
            (valid_unlifted_worker val_args) : bool
    then cbv_bndr else
    fun_id.

#[global] Definition tidyCbvInfoLocal `{Util.HasDebugCallStack}
   : Core.Id -> Core.CoreExpr -> Core.Id :=
  fun id rhs => computeCbvInfo id rhs.

#[global] Definition tidyNestedUnfolding
   : Core.TidyEnv -> Core.Unfolding -> Core.Unfolding :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Core.NoUnfolding => Core.NoUnfolding
    end.

#[global] Definition tidyLetBndr
   : Core.TidyEnv -> Core.TidyEnv -> Core.Id -> (Core.TidyEnv * Core.Id)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | rec_tidy_env, (pair tidy_env var_env as env), id =>
        let 'pair tidy_env' occ' := OccName.tidyOccName tidy_env (Name.getOccName id) in
        let old_info := Core.idInfo id in
        let old_unf := Core.realUnfoldingInfo old_info in
        let new_unf := tidyNestedUnfolding rec_tidy_env old_unf in
        let new_info :=
          Core.setUnfoldingInfo (Core.setInlinePragInfo (Core.setDemandInfo
                                                         (Core.setDmdSigInfo (Core.setArityInfo (Core.setOccInfo
                                                                                                 Core.vanillaIdInfo
                                                                                                 (Core.occInfo
                                                                                                  old_info))
                                                                                                (Core.arityInfo
                                                                                                 old_info))
                                                                             (Core.zapDmdEnvSig (Core.dmdSigInfo
                                                                                                 old_info)))
                                                         (Core.demandInfo old_info)) (Core.inlinePragInfo old_info))
                                new_unf in
        let details := Core.idDetails id in
        let name' := Name.mkInternalName (Id.idUnique id) occ' SrcLoc.noSrcSpan in
        let mult' := GHC.Core.TyCo.Tidy.tidyType env (Id.idMult id) in
        let ty' := GHC.Core.TyCo.Tidy.tidyType env (Id.idType id) in
        let id' := Core.mkLocalVar details name' mult' ty' new_info in
        let var_env' := Core.extendVarEnv var_env id id' in
        pair (pair tidy_env' var_env') id'
    end.

#[global] Definition tidyVarOcc : Core.TidyEnv -> Core.Var -> Core.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair _ var_env, v => Maybes.orElse (Core.lookupVarEnv var_env v) v
    end.

Axiom tidyBind
   : Core.TidyEnv -> Core.CoreBind -> (Core.TidyEnv * Core.CoreBind)%type.

#[global] Definition tidyCbvInfoTop `{Util.HasDebugCallStack}
   : NameSet.NameSet -> Core.Id -> Core.CoreExpr -> Core.Id :=
  fun boot_exports id rhs =>
    if NameSet.elemNameSet (Id.idName id) boot_exports : bool then id else
    computeCbvInfo id rhs.

Axiom tidyExpr
   : Core.TidyEnv -> Core.CoreExpr -> Core.CoreExpr.

#[global] Definition tidyAlt : Core.TidyEnv -> Core.CoreAlt -> Core.CoreAlt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | env, Core.Mk_Alt con vs rhs =>
        tidyBndrs env vs =:
        (fun '(pair env' vs) => (Core.Mk_Alt con vs (tidyExpr env' rhs)))
    end.

Axiom tidyTickish
   : Core.TidyEnv ->
     GHC.Types.Tickish.CoreTickish -> GHC.Types.Tickish.CoreTickish.

(* Skipping definition `CoreTidy.tidyRules' *)

(* Skipping definition `CoreTidy.tidyRule' *)

#[global] Definition tidyNameOcc : Core.TidyEnv -> Name.Name -> Name.Name :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair _ var_env, n =>
        match UniqFM.lookupUFM_Directly var_env (Unique.getUnique n) with
        | None => n
        | Some v => Id.idName v
        end
    end.

Module Notations.
Notation "'_CoreTidy.=:_'" := (op_zeZC__).
Infix "CoreTidy.=:" := (_=:_) (at level 99).
End Notations.

(* External variables:
     None Some andb bool cons false list negb nil op_zt__ orb pair true
     BasicTypes.MarkedCbv BasicTypes.NotMarkedCbv BasicTypes.isMarkedCbv Core.Alt
     Core.App Core.Case Core.Cast Core.CoreAlt Core.CoreBind Core.CoreExpr Core.Id
     Core.Lam Core.Let Core.Lit Core.Mk_Coercion Core.Mk_Type Core.Mk_Var
     Core.NoUnfolding Core.NonRec Core.Rec Core.TidyEnv Core.Unfolding Core.Var
     Core.arityInfo Core.collectBinders Core.collectNBinders Core.demandInfo
     Core.dmdSigInfo Core.extendVarEnv Core.idDetails Core.idInfo Core.inlinePragInfo
     Core.isId Core.isStrUsedDmd Core.isTyCoVar Core.isUnboxedSumType
     Core.isUnboxedTupleType Core.lookupVarEnv Core.mkLocalVar Core.occInfo
     Core.oneShotInfo Core.realUnfoldingInfo Core.setArityInfo Core.setDemandInfo
     Core.setDmdSigInfo Core.setInlinePragInfo Core.setOccInfo Core.setOneShotInfo
     Core.setUnfoldingInfo Core.trimUnfolding Core.vanillaIdInfo Core.zapDmdEnvSig
     CoreUtils.shouldUseCbvForId Data.Foldable.all Data.Foldable.any
     Data.Foldable.null Data.Maybe.maybe Data.Traversable.mapAccumL Data.Tuple.fst
     GHC.Base.map GHC.Base.mappend GHC.Core.TyCo.Tidy.tidyCo
     GHC.Core.TyCo.Tidy.tidyType GHC.Core.TyCo.Tidy.tidyVarBndr GHC.List.filter
     GHC.List.unzip GHC.List.zip GHC.Prim.HasCallStack GHC.Prim.seq
     GHC.Types.Tickish.Breakpoint GHC.Types.Tickish.CoreTickish HsToCoq.Err.default
     Id.asNonWorkerLikeId Id.idCbvMarks_maybe Id.idDemandInfo Id.idJoinPointHood
     Id.idMult Id.idName Id.idType Id.idUnique Id.isDeadEndId Id.isWorkerLikeId
     Id.mkLocalIdWithInfo Id.setIdCbvMarks Maybes.orElse Name.Name Name.getOccName
     Name.mkInternalName NameSet.NameSet NameSet.elemNameSet OccName.tidyOccName
     Outputable.JoinPoint Outputable.isJoinPoint Panic.assertPpr Panic.someSDoc
     RepType.typePrimRep SrcLoc.noSrcSpan UniqFM.lookupUFM_Directly Unique.getUnique
     Util.HasDebugCallStack Util.seqList
*)
