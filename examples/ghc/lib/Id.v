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
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require Data.Foldable.
Require Data.Maybe.
Require Datatypes.
Require FastString.
Require GHC.Base.
Require GHC.Core.Multiplicity.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Stg.InferTags.TagSig.
Require GHC.StgToCmm.Types.
Require GHC.Types.Cpr.
Require Maybes.
Require Module.
Require Name.
Require OccName.
Require Panic.
Require SrcLoc.
Require UniqSupply.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Midamble *)

(* GHC 9.10: Panic.panic needs Default instances for IdDetails *)
Import Core.

(* GHC 9.10: some functions use GHC.Utils.Trace for debug tracing *)
Require Import GHC.Utils.Trace.

(* GHC 9.10: These functions are skipped because they use Outputable.JoinPointHood
   from GHC.Types.Basic (a module we don't translate). We define them manually
   using Core.idDetails and the Mk_JoinId constructor. *)

Require Import Outputable.

Definition idJoinPointHood : Core.Var -> Outputable.JoinPointHood :=
  fun id =>
    if Core.isId id then
      match Core.idDetails id with
      | Core.Mk_JoinId arity _ => Outputable.JoinPoint arity
      | _ => Outputable.NotJoinPoint
      end
    else Outputable.NotJoinPoint.

Definition idJoinArity : Core.JoinId -> BasicTypes.JoinArity :=
  fun id =>
    match Core.idDetails id with
    | Core.Mk_JoinId arity _ => arity
    | _ => Panic.panic (GHC.Base.hs_string__ "idJoinArity")
    end.

Definition asJoinId : Core.Id -> BasicTypes.JoinArity -> Core.JoinId :=
  fun id arity => Core.setIdDetails id (Core.Mk_JoinId arity None).

(* Converted value declarations: *)

#[global] Definition idName : Core.Id -> Name.Name :=
  Core.varName.

#[global] Definition idUnique : Core.Id -> Unique.Unique :=
  Core.varUnique.

#[global] Definition idType : Core.Id -> AxiomatizedTypes.Kind :=
  Core.varType.

#[global] Definition idMult : Core.Id -> Core.Mult :=
  Core.varMult.

#[global] Definition idScaledType
   : Core.Id -> Core.Scaled AxiomatizedTypes.Type_ :=
  fun id => Core.Mk_Scaled (idMult id) (idType id).

#[global] Definition scaleIdBy : Core.Mult -> Core.Id -> Core.Id :=
  fun m id => Core.setIdMult id (GHC.Core.Multiplicity.mkMultMul m (idMult id)).

#[global] Definition scaleVarBy : Core.Mult -> Core.Var -> Core.Var :=
  fun m id => if Core.isId id : bool then scaleIdBy m id else id.

#[global] Definition setIdName : Core.Id -> Name.Name -> Core.Id :=
  Core.setVarName.

#[global] Definition setIdUnique : Core.Id -> Unique.Unique -> Core.Id :=
  Core.setVarUnique.

#[global] Definition setIdType : Core.Id -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun id ty => Core.setVarType id ty.

(* Skipping definition `Id.setIdExported' *)

(* Skipping definition `Id.setIdNotExported' *)

#[global] Definition localiseId : Core.Id -> Core.Id :=
  fun id =>
    let name := idName id in
    if andb (Core.isLocalId id) (Name.isInternalName name) : bool then id else
    Core.mkLocalVar (Core.idDetails id) (Name.localiseName name) (Core.varMult id)
    (idType id) (Core.idInfo id).

#[global] Definition lazySetIdInfo : Core.Id -> Core.IdInfo -> Core.Id :=
  Core.lazySetIdInfo.

#[global] Definition setIdInfo : Core.Id -> Core.IdInfo -> Core.Id :=
  fun id info => GHC.Prim.seq info (lazySetIdInfo id info).

#[global] Definition modifyIdInfo `{Util.HasDebugCallStack}
   : (Core.IdInfo -> Core.IdInfo) -> Core.Id -> Core.Id :=
  fun fn id => setIdInfo id (fn (Core.idInfo id)).

#[global] Definition maybeModifyIdInfo
   : option Core.IdInfo -> Core.Id -> Core.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Some new_info, id => lazySetIdInfo id new_info
    | None, id => id
    end.

#[global] Definition maybeModifyIdDetails
   : option Core.IdDetails -> Core.Id -> Core.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Some new_details, id => Core.setIdDetails id new_details
    | None, id => id
    end.

#[global] Definition mkGlobalId
   : Core.IdDetails ->
     Name.Name -> AxiomatizedTypes.Type_ -> Core.IdInfo -> Core.Id :=
  Core.mkGlobalVar.

#[global] Definition mkVanillaGlobalWithInfo `{Util.HasDebugCallStack}
   : Name.Name -> AxiomatizedTypes.Type_ -> Core.IdInfo -> Core.Id :=
  fun nm =>
    Panic.assertPpr (negb (OccName.isFieldNameSpace (Name.nameNameSpace nm)))
                    (GHC.Base.mappend (Datatypes.id (GHC.Base.hs_string__
                                                     "mkVanillaGlobalWithInfo called on record field:")) Panic.someSDoc)
    (mkGlobalId Core.VanillaId nm).

#[global] Definition mkVanillaGlobal `{Util.HasDebugCallStack}
   : Name.Name -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun name ty => mkVanillaGlobalWithInfo name ty Core.vanillaIdInfo.

#[global] Definition mkLocalIdWithInfo `{Util.HasDebugCallStack}
   : Name.Name -> Core.Mult -> AxiomatizedTypes.Type_ -> Core.IdInfo -> Core.Id :=
  fun name w ty info => Core.mkLocalVar Core.VanillaId name w (ty) info.

#[global] Definition mkLocalId `{Util.HasDebugCallStack}
   : Name.Name -> Core.Mult -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun name w ty => mkLocalIdWithInfo name w (ty) Core.vanillaIdInfo.

(* Skipping definition `Id.mkLocalCoVar' *)

(* Skipping definition `Id.mkLocalIdOrCoVar' *)

#[global] Definition mkExportedLocalId
   : Core.IdDetails -> Name.Name -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun details name ty =>
    Core.mkExportedLocalVar details name ty Core.vanillaIdInfo.

#[global] Definition mkExportedVanillaId
   : Name.Name -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun name ty =>
    Panic.assertPpr (negb (OccName.isFieldNameSpace (Name.nameNameSpace name)))
                    (GHC.Base.mappend (Datatypes.id (GHC.Base.hs_string__
                                                     "mkExportedVanillaId called on record field:")) Panic.someSDoc)
    (Core.mkExportedLocalVar Core.VanillaId name ty Core.vanillaIdInfo).

#[global] Definition mkSysLocal
   : FastString.FastString ->
     Unique.Unique -> Core.Mult -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun fs uniq w ty => mkLocalId (Name.mkSystemVarName uniq fs) w ty.

(* Skipping definition `Id.mkSysLocalOrCoVar' *)

#[global] Definition mkSysLocalM {m : Type -> Type} `{UniqSupply.MonadUnique m}
   : FastString.FastString -> Core.Mult -> AxiomatizedTypes.Type_ -> m Core.Id :=
  fun fs w ty =>
    UniqSupply.getUniqueM GHC.Base.>>=
    (fun uniq => GHC.Base.return_ (mkSysLocal fs uniq w ty)).

(* Skipping definition `Id.mkSysLocalOrCoVarM' *)

#[global] Definition mkUserLocal
   : OccName.OccName ->
     Unique.Unique ->
     Core.Mult -> AxiomatizedTypes.Type_ -> SrcLoc.SrcSpan -> Core.Id :=
  fun occ uniq w ty loc => mkLocalId (Name.mkInternalName uniq occ loc) w ty.

(* Skipping definition `Id.mkUserLocalOrCoVar' *)

Axiom mkWorkerId : Unique.Unique ->
                   Core.Id -> AxiomatizedTypes.Type_ -> Core.Id.

Axiom mkTemplateLocal : nat -> AxiomatizedTypes.Type_ -> Core.Id.

(* Skipping definition `Id.mkScaledTemplateLocal' *)

Axiom mkTemplateLocals : list AxiomatizedTypes.Type_ -> list Core.Id.

Axiom mkTemplateLocalsNum : nat -> list AxiomatizedTypes.Type_ -> list Core.Id.

#[global] Definition recordSelectorTyCon_maybe
   : Core.Id -> option Core.RecSelParent :=
  fun id =>
    match Core.idDetails id with
    | Core.RecSelId parent _ _ _ => Some parent
    | _ => None
    end.

#[global] Definition recordSelectorTyCon : Core.Id -> Core.RecSelParent :=
  fun id =>
    match recordSelectorTyCon_maybe id with
    | Some parent => parent
    | _ => Panic.panic (GHC.Base.hs_string__ "recordSelectorTyCon")
    end.

#[global] Definition isRecordSelector : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.RecSelId _ _ _ _ => true
    | _ => false
    end.

#[global] Definition isDataConRecordSelector : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.RecSelId (Core.RecSelData _) _ _ _ => true
    | _ => false
    end.

#[global] Definition isPatSynRecordSelector : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.RecSelId (Core.RecSelPatSyn _) _ _ _ => true
    | _ => false
    end.

#[global] Definition isNaughtyRecordSelector : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.RecSelId _ _ n _ => n
    | _ => false
    end.

#[global] Definition isClassOpId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.ClassOpId _ _ => true
    | _other => false
    end.

#[global] Definition isClassOpId_maybe : Core.Id -> option Core.Class :=
  fun id =>
    match Core.idDetails id with
    | Core.ClassOpId cls _ => Some cls
    | _other => None
    end.

#[global] Definition isPrimOpId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.PrimOpId _ _ => true
    | _ => false
    end.

#[global] Definition isDFunId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.Mk_DFunId _ => true
    | _ => false
    end.

#[global] Definition isPrimOpId_maybe
   : Core.Id -> option AxiomatizedTypes.PrimOp :=
  fun id =>
    match Core.idDetails id with
    | Core.PrimOpId op _ => Some op
    | _ => None
    end.

#[global] Definition isFCallId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.FCallId _ => true
    | _ => false
    end.

#[global] Definition isFCallId_maybe
   : Core.Id -> option AxiomatizedTypes.ForeignCall :=
  fun id =>
    match Core.idDetails id with
    | Core.FCallId call => Some call
    | _ => None
    end.

#[global] Definition isDataConWorkId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.DataConWorkId _ => true
    | _ => false
    end.

#[global] Definition isDataConWorkId_maybe : Core.Id -> option Core.DataCon :=
  fun id =>
    match Core.idDetails id with
    | Core.DataConWorkId con => Some con
    | _ => None
    end.

#[global] Definition isDataConWrapId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.DataConWrapId _ => true
    | _ => false
    end.

#[global] Definition isDataConWrapId_maybe : Core.Id -> option Core.DataCon :=
  fun id =>
    match Core.idDetails id with
    | Core.DataConWrapId con => Some con
    | _ => None
    end.

#[global] Definition isDataConId_maybe : Core.Id -> option Core.DataCon :=
  fun id =>
    match Core.idDetails id with
    | Core.DataConWorkId con => Some con
    | Core.DataConWrapId con => Some con
    | _ => None
    end.

#[global] Definition isWorkerLikeId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.WorkerLikeId _ => true
    | Core.Mk_JoinId _ (Some _) => true
    | _ => false
    end.

#[global] Definition isJoinId : Core.Var -> bool :=
  fun id =>
    if Core.isId id : bool
    then match Core.idDetails id with
         | Core.Mk_JoinId _ _ => true
         | _ => false
         end else
    false.

(* Skipping definition `Id.idJoinPointHood' *)

#[global] Definition idDataCon : Core.Id -> Core.DataCon :=
  fun id =>
    Maybes.orElse (isDataConId_maybe id) (Panic.pprPanic (GHC.Base.hs_string__
                                                          "idDataCon") (Panic.someSDoc)).

#[global] Definition realIdUnfolding : Core.Id -> Core.Unfolding :=
  fun id => Core.realUnfoldingInfo (Core.idInfo id).

#[global] Definition hasNoBinding : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.PrimOpId _ _ => true
    | Core.FCallId _ => true
    | Core.DataConWorkId dc =>
        orb (Core.isUnboxedTupleDataCon dc) (Core.isUnboxedSumDataCon dc)
    | _ => Core.isCompulsoryUnfolding (realIdUnfolding id)
    end.

#[global] Definition isImplicitId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.FCallId _ => true
    | Core.ClassOpId _ _ => true
    | Core.PrimOpId _ _ => true
    | Core.DataConWorkId _ => true
    | Core.DataConWrapId _ => true
    | _ => false
    end.

#[global] Definition idIsFrom : Module.Module -> Core.Id -> bool :=
  fun mod_ id => Name.nameIsLocalOrFrom mod_ (idName id).

#[global] Definition idOccInfo : Core.Id -> BasicTypes.OccInfo :=
  fun id => Core.occInfo (Core.idInfo id).

#[global] Definition isDeadBinder : Core.Id -> bool :=
  fun bndr =>
    if Core.isId bndr : bool then BasicTypes.isDeadOcc (idOccInfo bndr) else
    false.

(* Skipping definition `Id.idJoinArity' *)

(* Skipping definition `Id.asJoinId' *)

#[global] Definition zapInfo
   : (Core.IdInfo -> option Core.IdInfo) -> Core.Id -> Core.Id :=
  fun zapper id => maybeModifyIdInfo (zapper (Core.idInfo id)) id.

#[global] Definition zapIdTailCallInfo : Core.Id -> Core.Id :=
  zapInfo Core.zapTailCallInfo.

#[global] Definition zapJoinId : Core.Id -> Core.Id :=
  fun jid =>
    let newIdDetails :=
      match Core.idDetails jid with
      | Core.Mk_JoinId _ (Some marks) => Core.WorkerLikeId marks
      | Core.Mk_JoinId _ None => Core.WorkerLikeId nil
      | _ =>
          Panic.panic (GHC.Base.hs_string__
                       "zapJoinId: newIdDetails can only be used if Id was a join Id.")
      end in
    if isJoinId jid : bool
    then zapIdTailCallInfo (GHC.Prim.seq newIdDetails (Core.setIdDetails jid
                                                                         newIdDetails)) else
    jid.

(* Skipping definition `Id.asJoinId_maybe' *)

#[global] Definition idArity : Core.Id -> BasicTypes.Arity :=
  fun id => Core.arityInfo (Core.idInfo id).

#[global] Definition setIdArity : Core.Id -> BasicTypes.Arity -> Core.Id :=
  fun id arity => modifyIdInfo (GHC.Prim.rightSection Core.setArityInfo arity) id.

#[global] Definition idCallArity : Core.Id -> BasicTypes.Arity :=
  fun id => Core.callArityInfo (Core.idInfo id).

#[global] Definition setIdCallArity : Core.Id -> BasicTypes.Arity -> Core.Id :=
  fun id arity =>
    modifyIdInfo (GHC.Prim.rightSection Core.setCallArityInfo arity) id.

(* Skipping definition `Id.idFunRepArity' *)

#[global] Definition idDmdSig : Core.Id -> Core.DmdSig :=
  fun id => Core.dmdSigInfo (Core.idInfo id).

#[global] Definition isDeadEndId : Core.Var -> bool :=
  fun v => if Core.isId v : bool then Core.isDeadEndSig (idDmdSig v) else false.

#[global] Definition setIdDmdSig : Core.Id -> Core.DmdSig -> Core.Id :=
  fun id sig => modifyIdInfo (GHC.Prim.rightSection Core.setDmdSigInfo sig) id.

#[global] Definition idCprSig : Core.Id -> GHC.Types.Cpr.CprSig :=
  fun id => Core.cprSigInfo (Core.idInfo id).

#[global] Definition setIdCprSig : Core.Id -> GHC.Types.Cpr.CprSig -> Core.Id :=
  fun id sig => modifyIdInfo (fun info => Core.setCprSigInfo info sig) id.

#[global] Definition zapIdDmdSig : Core.Id -> Core.Id :=
  fun id =>
    modifyIdInfo (GHC.Prim.rightSection Core.setDmdSigInfo Core.nopSig) id.

#[global] Definition idDemandInfo : Core.Id -> Core.Demand :=
  fun id => Core.demandInfo (Core.idInfo id).

#[global] Definition isStrictId : Core.Id -> bool :=
  fun id =>
    if Panic.assertPpr (Core.isId id) (GHC.Base.mappend (Datatypes.id
                                                         (GHC.Base.hs_string__ "isStrictId: not an id: "))
                                                        Panic.someSDoc) (isJoinId id) : bool
    then false else
    orb (Core.isStrictType (idType id)) (Core.isStrUsedDmd (idDemandInfo id)).

#[global] Definition idTagSig_maybe
   : Core.Id -> option GHC.Stg.InferTags.TagSig.TagSig :=
  Core.tagSig GHC.Base.∘ Core.idInfo.

#[global] Definition idUnfolding : Core.IdUnfoldingFun :=
  fun id => Core.unfoldingInfo (Core.idInfo id).

#[global] Definition noUnfoldingFun : Core.IdUnfoldingFun :=
  fun _id => Core.noUnfolding.

#[global] Definition idInlinePragma : Core.Id -> BasicTypes.InlinePragma :=
  fun id => Core.inlinePragInfo (Core.idInfo id).

#[global] Definition idInlineActivation : Core.Id -> BasicTypes.Activation :=
  fun id => BasicTypes.inlinePragmaActivation (idInlinePragma id).

#[global] Definition alwaysActiveUnfoldingFun : Core.IdUnfoldingFun :=
  fun id =>
    if BasicTypes.isAlwaysActive (idInlineActivation id) : bool
    then idUnfolding id else
    Core.noUnfolding.

#[global] Definition whenActiveUnfoldingFun
   : (BasicTypes.Activation -> bool) -> Core.IdUnfoldingFun :=
  fun is_active id =>
    if is_active (idInlineActivation id) : bool then idUnfolding id else
    Core.NoUnfolding.

#[global] Definition setIdUnfolding : Core.Id -> Core.Unfolding -> Core.Id :=
  fun id unfolding =>
    modifyIdInfo (GHC.Prim.rightSection Core.setUnfoldingInfo unfolding) id.

#[global] Definition setIdDemandInfo : Core.Id -> Core.Demand -> Core.Id :=
  fun id dmd => modifyIdInfo (GHC.Prim.rightSection Core.setDemandInfo dmd) id.

#[global] Definition setIdTagSig
   : Core.Id -> GHC.Stg.InferTags.TagSig.TagSig -> Core.Id :=
  fun id sig => modifyIdInfo (GHC.Prim.rightSection Core.setTagSig sig) id.

#[global] Definition setIdCbvMarks
   : Core.Id -> list BasicTypes.CbvMark -> Core.Id :=
  fun id marks =>
    let trimmedMarks :=
      Util.dropWhileEndLE (negb GHC.Base.∘ BasicTypes.isMarkedCbv)
      (Coq.Lists.List.firstn (idArity id) marks) in
    if negb (Data.Foldable.any BasicTypes.isMarkedCbv marks) : bool then id else
    match Core.idDetails id with
    | Core.VanillaId => Core.setIdDetails id (Core.WorkerLikeId trimmedMarks)
    | Core.Mk_JoinId arity _ =>
        Core.setIdDetails id (Core.Mk_JoinId arity (Some trimmedMarks))
    | Core.WorkerLikeId _ => Core.setIdDetails id (Core.WorkerLikeId trimmedMarks)
    | Core.RecSelId _ _ _ _ => id
    | Core.Mk_DFunId _ => id
    | _ =>
        GHC.Utils.Trace.pprTrace (GHC.Base.hs_string__
                                  "setIdCbvMarks: Unable to set cbv marks for") (GHC.Base.mappend
                                                                                 (GHC.Base.mappend Panic.someSDoc
                                                                                                   Panic.someSDoc)
                                                                                 Panic.someSDoc) id
    end.

#[global] Definition idCbvMarks_maybe
   : Core.Id -> option (list BasicTypes.CbvMark) :=
  fun id =>
    match Core.idDetails id with
    | Core.WorkerLikeId marks => Some marks
    | Core.Mk_JoinId _arity marks => marks
    | _ => None
    end.

Axiom idCbvMarkArity : Core.Id -> BasicTypes.Arity.

#[global] Definition asNonWorkerLikeId : Core.Id -> Core.Id :=
  fun id =>
    let details :=
      match Core.idDetails id with
      | Core.WorkerLikeId _ => Some Core.VanillaId
      | Core.Mk_JoinId arity (Some _) => Some (Core.Mk_JoinId arity None)
      | _ => None
      end in
    maybeModifyIdDetails details id.

#[global] Definition asWorkerLikeId : Core.Id -> Core.Id :=
  fun id =>
    let details :=
      match Core.idDetails id with
      | Core.WorkerLikeId _ => None
      | Core.Mk_JoinId _arity (Some _) => None
      | Core.Mk_JoinId arity None => Some (Core.Mk_JoinId arity (Some nil))
      | Core.VanillaId => Some (Core.WorkerLikeId nil)
      | _ => None
      end in
    maybeModifyIdDetails details id.

(* Skipping definition `Id.setCaseBndrEvald' *)

#[global] Definition zapIdUnfolding : Core.Id -> Core.Id :=
  fun v =>
    if andb (Core.isId v) (Core.hasSomeUnfolding (idUnfolding v)) : bool
    then setIdUnfolding v Core.noUnfolding else
    v.

#[global] Definition idSpecialisation : Core.Id -> Core.RuleInfo :=
  fun id => Core.ruleInfo (Core.idInfo id).

#[global] Definition idCoreRules : Core.Id -> list Core.CoreRule :=
  fun x => nil.

#[global] Definition idHasRules : Core.Id -> bool :=
  fun id => negb (Core.isEmptyRuleInfo (idSpecialisation id)).

#[global] Definition setIdSpecialisation
   : Core.Id -> Core.RuleInfo -> Core.Id :=
  fun id spec_info =>
    modifyIdInfo (GHC.Prim.rightSection Core.setRuleInfo spec_info) id.

#[global] Definition idCafInfo : Core.Id -> Core.CafInfo :=
  fun id => Core.cafInfo (Core.idInfo id).

#[global] Definition setIdCafInfo : Core.Id -> Core.CafInfo -> Core.Id :=
  fun id caf_info =>
    modifyIdInfo (GHC.Prim.rightSection Core.setCafInfo caf_info) id.

#[global] Definition idLFInfo_maybe
   : Core.Id -> option GHC.StgToCmm.Types.LambdaFormInfo :=
  Core.lfInfo GHC.Base.∘ Core.idInfo.

#[global] Definition setIdLFInfo
   : Core.Id -> GHC.StgToCmm.Types.LambdaFormInfo -> Core.Id :=
  fun id lf => modifyIdInfo (GHC.Prim.rightSection Core.setLFInfo lf) id.

#[global] Definition setIdOccInfo : Core.Id -> BasicTypes.OccInfo -> Core.Id :=
  fun id occ_info =>
    modifyIdInfo (GHC.Prim.rightSection Core.setOccInfo occ_info) id.

#[global] Definition zapIdOccInfo : Core.Id -> Core.Id :=
  fun b => setIdOccInfo b BasicTypes.noOccInfo.

#[global] Definition setInlinePragma
   : Core.Id -> BasicTypes.InlinePragma -> Core.Id :=
  fun id prag =>
    modifyIdInfo (GHC.Prim.rightSection Core.setInlinePragInfo prag) id.

#[global] Definition modifyInlinePragma
   : Core.Id -> (BasicTypes.InlinePragma -> BasicTypes.InlinePragma) -> Core.Id :=
  fun id fn =>
    modifyIdInfo (fun info =>
                    Core.setInlinePragInfo info (fn (Core.inlinePragInfo info))) id.

#[global] Definition setInlineActivation
   : Core.Id -> BasicTypes.Activation -> Core.Id :=
  fun id act =>
    modifyInlinePragma id (fun prag =>
                             BasicTypes.setInlinePragmaActivation prag act).

#[global] Definition idRuleMatchInfo : Core.Id -> BasicTypes.RuleMatchInfo :=
  fun id => BasicTypes.inlinePragmaRuleMatchInfo (idInlinePragma id).

#[global] Definition isConLikeId : Core.Id -> bool :=
  fun id => BasicTypes.isConLike (idRuleMatchInfo id).

#[global] Definition idOneShotInfo : Core.Id -> BasicTypes.OneShotInfo :=
  fun id => Core.oneShotInfo (Core.idInfo id).

#[global] Definition setOneShotLambda : Core.Id -> Core.Id :=
  fun id =>
    modifyIdInfo (GHC.Prim.rightSection Core.setOneShotInfo BasicTypes.OneShotLam)
    id.

#[global] Definition clearOneShotLambda : Core.Id -> Core.Id :=
  fun id =>
    modifyIdInfo (GHC.Prim.rightSection Core.setOneShotInfo
                  BasicTypes.NoOneShotInfo) id.

#[global] Definition setIdOneShotInfo
   : Core.Id -> BasicTypes.OneShotInfo -> Core.Id :=
  fun id one_shot =>
    modifyIdInfo (GHC.Prim.rightSection Core.setOneShotInfo one_shot) id.

#[global] Definition updOneShotInfo
   : Core.Id -> BasicTypes.OneShotInfo -> Core.Id :=
  fun id one_shot =>
    match one_shot with
    | BasicTypes.OneShotLam =>
        match idOneShotInfo id with
        | BasicTypes.NoOneShotInfo => setIdOneShotInfo id BasicTypes.OneShotLam
        | _ => id
        end
    | _ => id
    end.

#[global] Definition zapLamIdInfo : Core.Id -> Core.Id :=
  zapInfo Core.zapLamInfo.

#[global] Definition zapFragileIdInfo : Core.Id -> Core.Id :=
  zapInfo Core.zapFragileInfo.

#[global] Definition floatifyIdDemandInfo : Core.Id -> Core.Id :=
  zapInfo Core.floatifyDemandInfo.

#[global] Definition zapIdUsageInfo : Core.Id -> Core.Id :=
  zapInfo Core.zapUsageInfo.

#[global] Definition zapIdUsageEnvInfo : Core.Id -> Core.Id :=
  zapInfo Core.zapUsageEnvInfo.

#[global] Definition zapIdUsedOnceInfo : Core.Id -> Core.Id :=
  zapInfo Core.zapUsedOnceInfo.

#[global] Definition zapStableUnfolding : Core.Id -> Core.Id :=
  fun id =>
    if Core.isStableUnfolding (realIdUnfolding id) : bool
    then setIdUnfolding id Core.NoUnfolding else
    id.

#[global] Definition transferPolyIdInfo
   : Core.Id -> list Core.Var -> Core.Id -> Core.Id :=
  fun old_id abstract_wrt new_id =>
    let getMark :=
      fun v =>
        if negb (Core.isId v) : bool then None else
        if andb (Core.isId v) (andb (Core.isEvaldUnfolding (idUnfolding v))
                                    (Core.mightBeLiftedType (idType v))) : bool
        then Some BasicTypes.MarkedCbv else
        Some BasicTypes.NotMarkedCbv in
    let abstr_cbv_marks := Data.Maybe.mapMaybe getMark abstract_wrt in
    let old_info := Core.idInfo old_id in
    let old_arity := Core.arityInfo old_info in
    let old_cbv_marks :=
      Data.Maybe.fromMaybe (Coq.Lists.List.repeat BasicTypes.NotMarkedCbv old_arity)
      (idCbvMarks_maybe old_id) in
    let new_cbv_marks := Coq.Init.Datatypes.app abstr_cbv_marks old_cbv_marks in
    let old_inline_prag := Core.inlinePragInfo old_info in
    let old_occ_info := Core.occInfo old_info in
    let new_occ_info := BasicTypes.zapOccTailCallInfo old_occ_info in
    let old_strictness := Core.dmdSigInfo old_info in
    let old_cpr := Core.cprSigInfo old_info in
    let arity_increase := Util.count Core.isId abstract_wrt in
    let new_arity := old_arity GHC.Num.+ arity_increase in
    let new_strictness := Core.prependArgsDmdSig arity_increase old_strictness in
    let new_cpr := GHC.Types.Cpr.prependArgsCprSig arity_increase old_cpr in
    let transfer :=
      fun new_info =>
        Core.setCprSigInfo (Core.setDmdSigInfo (Core.setOccInfo (Core.setInlinePragInfo
                                                                 (Core.setArityInfo new_info new_arity) old_inline_prag)
                                                                new_occ_info) new_strictness) new_cpr in
    setIdCbvMarks (modifyIdInfo transfer new_id) new_cbv_marks.

(* External variables:
     None Some Type andb bool false list nat negb nil option orb true
     AxiomatizedTypes.ForeignCall AxiomatizedTypes.Kind AxiomatizedTypes.PrimOp
     AxiomatizedTypes.Type_ BasicTypes.Activation BasicTypes.Arity BasicTypes.CbvMark
     BasicTypes.InlinePragma BasicTypes.MarkedCbv BasicTypes.NoOneShotInfo
     BasicTypes.NotMarkedCbv BasicTypes.OccInfo BasicTypes.OneShotInfo
     BasicTypes.OneShotLam BasicTypes.RuleMatchInfo BasicTypes.inlinePragmaActivation
     BasicTypes.inlinePragmaRuleMatchInfo BasicTypes.isAlwaysActive
     BasicTypes.isConLike BasicTypes.isDeadOcc BasicTypes.isMarkedCbv
     BasicTypes.noOccInfo BasicTypes.setInlinePragmaActivation
     BasicTypes.zapOccTailCallInfo Coq.Init.Datatypes.app Coq.Lists.List.firstn
     Coq.Lists.List.repeat Core.CafInfo Core.Class Core.ClassOpId Core.CoreRule
     Core.DataCon Core.DataConWorkId Core.DataConWrapId Core.Demand Core.DmdSig
     Core.FCallId Core.Id Core.IdDetails Core.IdInfo Core.IdUnfoldingFun
     Core.Mk_DFunId Core.Mk_JoinId Core.Mk_Scaled Core.Mult Core.NoUnfolding
     Core.PrimOpId Core.RecSelData Core.RecSelId Core.RecSelParent Core.RecSelPatSyn
     Core.RuleInfo Core.Scaled Core.Unfolding Core.VanillaId Core.Var
     Core.WorkerLikeId Core.arityInfo Core.cafInfo Core.callArityInfo Core.cprSigInfo
     Core.demandInfo Core.dmdSigInfo Core.floatifyDemandInfo Core.hasSomeUnfolding
     Core.idDetails Core.idInfo Core.inlinePragInfo Core.isCompulsoryUnfolding
     Core.isDeadEndSig Core.isEmptyRuleInfo Core.isEvaldUnfolding Core.isId
     Core.isLocalId Core.isStableUnfolding Core.isStrUsedDmd Core.isStrictType
     Core.isUnboxedSumDataCon Core.isUnboxedTupleDataCon Core.lazySetIdInfo
     Core.lfInfo Core.mightBeLiftedType Core.mkExportedLocalVar Core.mkGlobalVar
     Core.mkLocalVar Core.noUnfolding Core.nopSig Core.occInfo Core.oneShotInfo
     Core.prependArgsDmdSig Core.realUnfoldingInfo Core.ruleInfo Core.setArityInfo
     Core.setCafInfo Core.setCallArityInfo Core.setCprSigInfo Core.setDemandInfo
     Core.setDmdSigInfo Core.setIdDetails Core.setIdMult Core.setInlinePragInfo
     Core.setLFInfo Core.setOccInfo Core.setOneShotInfo Core.setRuleInfo
     Core.setTagSig Core.setUnfoldingInfo Core.setVarName Core.setVarType
     Core.setVarUnique Core.tagSig Core.unfoldingInfo Core.vanillaIdInfo Core.varMult
     Core.varName Core.varType Core.varUnique Core.zapFragileInfo Core.zapLamInfo
     Core.zapTailCallInfo Core.zapUsageEnvInfo Core.zapUsageInfo Core.zapUsedOnceInfo
     Data.Foldable.any Data.Maybe.fromMaybe Data.Maybe.mapMaybe Datatypes.id
     FastString.FastString GHC.Base.mappend GHC.Base.op_z2218U__ GHC.Base.op_zgzgze__
     GHC.Base.return_ GHC.Core.Multiplicity.mkMultMul GHC.Num.op_zp__
     GHC.Prim.rightSection GHC.Prim.seq GHC.Stg.InferTags.TagSig.TagSig
     GHC.StgToCmm.Types.LambdaFormInfo GHC.Types.Cpr.CprSig
     GHC.Types.Cpr.prependArgsCprSig GHC.Utils.Trace.pprTrace Maybes.orElse
     Module.Module Name.Name Name.isInternalName Name.localiseName
     Name.mkInternalName Name.mkSystemVarName Name.nameIsLocalOrFrom
     Name.nameNameSpace OccName.OccName OccName.isFieldNameSpace Panic.assertPpr
     Panic.panic Panic.pprPanic Panic.someSDoc SrcLoc.SrcSpan UniqSupply.MonadUnique
     UniqSupply.getUniqueM Unique.Unique Util.HasDebugCallStack Util.count
     Util.dropWhileEndLE
*)
