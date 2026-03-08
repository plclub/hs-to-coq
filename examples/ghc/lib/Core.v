(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.

(* Preamble *)

Require Import TcType.

(* Converted imports: *)

Require Import AxiomatizedTypes.
Require Import BasicTypes.
Require Import FastString.
Require Import FieldLabel.
Require Import GHC.Base.
Require Import GHC.Char.
Require Import GHC.Core.TyCo.Subst.
Require Import GHC.Data.List.Infinite.
Require Import GHC.Num.
Require Import GHC.Prim.
Require Import GHC.Types.TyThing.
Require Import HsSyn.
Require Import Module.
Require Import Name.
Require Import NameEnv.
Require Import OccName.
Require Import Pair.
Require Import UniqSet.
Require Import Unique.
Require Import Util.
Require Import BinNums.
Require Import BooleanFormula.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Peano.
Require Import Coq.Lists.List.
Require Import Data.Bits.
Require Import Data.Foldable.
Require Import Data.Function.
Require Import Data.IntMap.Internal.
Require Import Data.Tuple.
Require Import GHC.Core.Rules.Config.
Require Import GHC.Core.TyCon.RecWalk.
Require Import GHC.Err.
Require Import GHC.List.
Require Import GHC.Real.
Require Import GHC.Stg.InferTags.TagSig.
Require Import GHC.StgToCmm.Types.
Require Import GHC.Types.Cpr.
Require Import GHC.Types.Tickish.
Require Import HsToCoq.DeferredFix.
Require Import HsToCoq.Err.
Require Import HsToCoq.Wf.
Require Import Literal.
Require Import Maybes.
Require Import Panic.
Require Import SrcLoc.
Require Import UniqDFM.
Require Import UniqDSet.
Require Import UniqFM.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive VarBndr var argf : Type := | Bndr : var -> argf -> VarBndr var argf.

Inductive UnfoldingGuidance : Type :=
  | UnfWhen (ug_arity : BasicTypes.Arity) (ug_unsat_ok : bool) (ug_boring_ok
    : bool)
   : UnfoldingGuidance
  | UnfIfGoodArgs (ug_args : list nat) (ug_size : nat) (ug_res : nat)
   : UnfoldingGuidance
  | UnfNever : UnfoldingGuidance.

Inductive UnfoldingCache : Type :=
  | Mk_UnfoldingCache (uf_is_value : bool) (uf_is_conlike : bool) (uf_is_work_free
    : bool) (uf_expandable : bool)
   : UnfoldingCache.

Inductive Unfolding : Type := | NoUnfolding : Unfolding.

Inductive TypeShape : Type :=
  | TsFun : TypeShape -> TypeShape
  | TsProd : list TypeShape -> TypeShape
  | TsUnk : TypeShape.

Inductive TyLit : Type :=
  | NumTyLit : GHC.Num.Integer -> TyLit
  | StrTyLit : FastString.FastString -> TyLit
  | CharTyLit : GHC.Char.Char -> TyLit.

#[global] Definition TyConRepName :=
  Name.Name%type.

#[global] Definition TickBoxId :=
  nat%type.

Inductive TickBoxOp : Type :=
  | TickBox : Module.Module -> TickBoxId -> TickBoxOp.

Inductive StrictnessMark : Type :=
  | MarkedStrict : StrictnessMark
  | NotMarkedStrict : StrictnessMark.

Inductive Specificity : Type :=
  | InferredSpec : Specificity
  | SpecifiedSpec : Specificity.

#[global] Definition RuntimeRepType :=
  Type_%type.

Inductive RuleInfo : Type := | EmptyRuleInfo.

Inductive PrimElemRep : Type :=
  | Int8ElemRep : PrimElemRep
  | Int16ElemRep : PrimElemRep
  | Int32ElemRep : PrimElemRep
  | Int64ElemRep : PrimElemRep
  | Word8ElemRep : PrimElemRep
  | Word16ElemRep : PrimElemRep
  | Word32ElemRep : PrimElemRep
  | Word64ElemRep : PrimElemRep
  | FloatElemRep : PrimElemRep
  | DoubleElemRep : PrimElemRep.

Inductive PrimRep : Type :=
  | BoxedRep : (option BasicTypes.Levity) -> PrimRep
  | Int8Rep : PrimRep
  | Int16Rep : PrimRep
  | Int32Rep : PrimRep
  | Int64Rep : PrimRep
  | IntRep : PrimRep
  | Word8Rep : PrimRep
  | Word16Rep : PrimRep
  | Word32Rep : PrimRep
  | Word64Rep : PrimRep
  | WordRep : PrimRep
  | AddrRep : PrimRep
  | FloatRep : PrimRep
  | DoubleRep : PrimRep
  | VecRep : nat -> PrimElemRep -> PrimRep.

Inductive PrimOrVoidRep : Type :=
  | VoidRep : PrimOrVoidRep
  | NVRep : PrimRep -> PrimOrVoidRep.

Inductive PromDataConInfo : Type :=
  | NoPromInfo : PromDataConInfo
  | RuntimeRep : (list Type_ -> list PrimRep) -> PromDataConInfo
  | VecCount : nat -> PromDataConInfo
  | VecElem : PrimElemRep -> PromDataConInfo
  | Levity : BasicTypes.Levity -> PromDataConInfo.

#[global] Definition PatSynMatcher :=
  (Name.Name * Type_ * bool)%type%type.

#[global] Definition PatSynBuilder :=
  (option (Name.Name * Type_ * bool)%type)%type.

#[global] Definition OutType :=
  Type_%type.

#[global] Definition OutKind :=
  Kind%type.

#[global] Definition OutCoercion :=
  Coercion%type.

Inductive NormaliseStepResult ev : Type :=
  | NS_Done : NormaliseStepResult ev
  | NS_Abort : NormaliseStepResult ev
  | NS_Step
   : GHC.Core.TyCon.RecWalk.RecTcChecker -> Type_ -> ev -> NormaliseStepResult ev.

#[global] Definition Mult :=
  Type_%type.

Inductive Scaled a : Type := | Mk_Scaled : Mult -> a -> Scaled a.

Inductive MCoercion : Type := | MRefl : MCoercion | MCo : Coercion -> MCoercion.

#[global] Definition MCoercionN :=
  MCoercion%type.

#[global] Definition MCoercionR :=
  MCoercion%type.

#[global] Definition MOutCoercion :=
  MCoercion%type.

#[global] Definition LevityType :=
  Type_%type.

#[global] Definition KnotTied (ty : Type) :=
  ty.

#[global] Definition KindOrType :=
  Type_%type.

Inductive KillFlags : Type :=
  | Mk_KillFlags (kf_abs : bool) (kf_used_once : bool) (kf_called_once : bool)
   : KillFlags.

Inductive IsOrphan : Type :=
  | Mk_IsOrphan : IsOrphan
  | NotOrphan : OccName.OccName -> IsOrphan.

#[global] Definition InlinePragInfo :=
  BasicTypes.InlinePragma%type.

Inductive Injectivity : Type :=
  | NotInjective : Injectivity
  | Injective : list bool -> Injectivity.

#[global] Definition InType :=
  Type_%type.

#[global] Definition InKind :=
  Kind%type.

#[global] Definition InCoercion :=
  Coercion%type.

Inductive HsSrcBang : Type :=
  | Mk_HsSrcBang
   : BasicTypes.SourceText ->
     HsSyn.SrcUnpackedness -> HsSyn.SrcStrictness -> HsSrcBang.

Inductive HsImplBang : Type :=
  | HsLazy : HsImplBang
  | HsStrict : bool -> HsImplBang
  | HsUnpack : (option Coercion) -> HsImplBang.

Inductive FunTyFlag : Type :=
  | FTF_T_T : FunTyFlag
  | FTF_T_C : FunTyFlag
  | FTF_C_T : FunTyFlag
  | FTF_C_C : FunTyFlag.

Inductive FunSel : Type :=
  | SelMult : FunSel
  | SelArg : FunSel
  | SelRes : FunSel.

#[global] Definition FunDep a :=
  (list a * list a)%type%type.

Inductive ForAllTyFlag : Type :=
  | Invisible : Specificity -> ForAllTyFlag
  | Required : ForAllTyFlag.

Inductive TyConBndrVis : Type :=
  | NamedTCB : ForAllTyFlag -> TyConBndrVis
  | AnonTCB : TyConBndrVis.

Inductive FamTyConFlav : Type :=
  | DataFamilyTyCon : TyConRepName -> FamTyConFlav
  | OpenSynFamilyTyCon : FamTyConFlav
  | ClosedSynFamilyTyCon : (option (CoAxiom Branched)) -> FamTyConFlav
  | AbstractClosedSynFamilyTyCon : FamTyConFlav
  | BuiltInSynFamTyCon : BuiltInSynFamily -> FamTyConFlav.

#[global] Definition FRRType :=
  Type_%type.

Inductive ExportFlag : Type :=
  | NotExported : ExportFlag
  | Exported : ExportFlag.

Inductive IdScope : Type :=
  | GlobalId : IdScope
  | LocalId : ExportFlag -> IdScope.

#[global] Definition ErrorMsgType :=
  Type_%type.

Inductive Divergence : Type :=
  | Diverges : Divergence
  | ExnOrDiv : Divergence
  | Dunno : Divergence.

#[global] Definition DefMethInfo :=
  (option (Name.Name * BasicTypes.DefMethSpec Type_)%type)%type.

#[global] Definition CoercionR :=
  Coercion%type.

#[global] Definition CoercionP :=
  Coercion%type.

#[global] Definition CoercionN :=
  Coercion%type.

#[global] Definition KindCoercion :=
  CoercionN%type.

Inductive UnivCoProvenance : Type :=
  | PhantomProv : KindCoercion -> UnivCoProvenance
  | ProofIrrelProv : KindCoercion -> UnivCoProvenance
  | PluginProv : GHC.Base.String -> UnivCoProvenance.

Axiom CoercionHole : Type.

Inductive CoSel : Type :=
  | SelTyCon : nat -> HsSyn.Role -> CoSel
  | SelFun : FunSel -> CoSel
  | SelForAll : CoSel.

#[global] Definition ClassMinimalDef :=
  (BooleanFormula.BooleanFormula Name.Name)%type.

Inductive Card : Type := | Mk_Card : nat -> Card.

#[global] Definition CardNonAbs :=
  Card%type.

#[global] Definition CardNonOnce :=
  Card%type.

Inductive SubDemand : Type :=
  | Poly : HsSyn.Boxity -> CardNonOnce -> SubDemand
  | Call : CardNonAbs -> SubDemand -> SubDemand
  | Prod : HsSyn.Boxity -> list Demand -> SubDemand
with Demand : Type :=
  | BotDmd : Demand
  | AbsDmd : Demand
  | D : CardNonAbs -> SubDemand -> Demand.

Inductive CafInfo : Type := | MayHaveCafRefs : CafInfo | NoCafRefs : CafInfo.

Inductive BitField : Type := | Mk_BitField : BinNums.N -> BitField.

#[global] Definition ArityInfo :=
  BasicTypes.Arity%type.

Inductive AlgTyConFlav : Type :=
  | VanillaAlgTyCon : TyConRepName -> AlgTyConFlav
  | UnboxedSumTyCon : AlgTyConFlav
  | ClassTyCon : Class -> TyConRepName -> AlgTyConFlav
  | DataFamInstTyCon : (CoAxiom Unbranched) -> TyCon -> list Type_ -> AlgTyConFlav
with Class : Type :=
  | Mk_Class (classTyCon : TyCon) (className : Name.Name) (classKey
    : Unique.Unique) (classTyVars : list Var%type) (classFunDeps
    : list (FunDep Var%type)) (classBody : ClassBody)
   : Class
with ClassBody : Type :=
  | AbstractClass : ClassBody
  | ConcreteClass (cls_sc_theta : list PredType) (cls_sc_sel_ids : list Var%type)
  (cls_ats : list ClassATItem) (cls_ops : list (Var%type * DefMethInfo)%type%type)
  (cls_min_def : ClassMinimalDef)
   : ClassBody
with ClassATItem : Type :=
  | ATI : TyCon -> (option (Type_ * TyFamEqnValidityInfo)%type) -> ClassATItem
with TyCon : Type :=
  | Mk_TyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name) (tyConBinders
    : list (VarBndr Var%type TyConBndrVis)%type) (tyConResKind : Kind)
  (tyConHasClosedResKind : bool) (tyConTyVars : list Var%type) (tyConKind : Kind)
  (tyConArity : BasicTypes.Arity) (tyConNullaryTy : Type_) (tyConRoles
    : list HsSyn.Role) (tyConDetails : TyConDetails)
   : TyCon
with Var : Type :=
  | Mk_Id (varName : Name.Name) (realUnique : Unique.Unique) (varType : Type_)
  (varMult : Mult) (idScope : IdScope) (id_details : IdDetails) (id_info : IdInfo)
   : Var
with IdDetails : Type :=
  | VanillaId : IdDetails
  | RecSelId (sel_tycon : RecSelParent) (sel_fieldLabel : FieldLabel.FieldLabel)
  (sel_naughty : bool) (sel_cons
    : (list ConLike * list ConLike)%type)
   : IdDetails
  | DataConWorkId : DataCon -> IdDetails
  | DataConWrapId : DataCon -> IdDetails
  | ClassOpId : Class -> bool -> IdDetails
  | RepPolyId (id_concrete_tvs : TcType.ConcreteTyVars) : IdDetails
  | PrimOpId (id_primop : PrimOp) (id_concrete_tvs : TcType.ConcreteTyVars)
   : IdDetails
  | FCallId : ForeignCall -> IdDetails
  | TickBoxOpId : TickBoxOp -> IdDetails
  | Mk_DFunId : bool -> IdDetails
  | Mk_JoinId
   : BasicTypes.JoinArity -> (option (list BasicTypes.CbvMark)) -> IdDetails
  | WorkerLikeId : list BasicTypes.CbvMark -> IdDetails
with DataCon : Type :=
  | MkData (dcName : Name.Name) (dcUnique : Unique.Unique) (dcTag : HsSyn.ConTag)
  (dcVanilla : bool) (dcUnivTyVars : list Var%type) (dcExTyCoVars
    : list Var%type%type) (dcConcreteTyVars : TcType.ConcreteTyVars)
  (dcUserTyVarBinders : list (VarBndr Var%type Specificity)%type) (dcEqSpec
    : list EqSpec) (dcOtherTheta : ThetaType) (dcStupidTheta : ThetaType)
  (dcOrigArgTys : list (Scaled Type_)) (dcOrigResTy : Type_) (dcSrcBangs
    : list HsSrcBang) (dcFields : list FieldLabel.FieldLabel) (dcWorkId : Var%type)
  (dcRep : DataConRep) (dcRepArity : BasicTypes.Arity) (dcSourceArity
    : BasicTypes.Arity) (dcRepTyCon : TyCon) (dcRepType : Type_) (dcInfix : bool)
  (dcPromoted : TyCon)
   : DataCon
with DataConRep : Type :=
  | NoDataConRep : DataConRep
  | DCR (dcr_wrap_id : Var%type) (dcr_boxer : DataConBoxer) (dcr_arg_tys
    : list (Scaled Type_)) (dcr_stricts : list StrictnessMark) (dcr_bangs
    : list HsImplBang)
   : DataConRep
with EqSpec : Type := | Mk_EqSpec : Var%type -> Type_ -> EqSpec
with RecSelParent : Type :=
  | RecSelData : TyCon -> RecSelParent
  | RecSelPatSyn : PatSyn -> RecSelParent
with PatSyn : Type :=
  | MkPatSyn (psName : Name.Name) (psUnique : Unique.Unique) (psArgs
    : list FRRType) (psArity : BasicTypes.Arity) (psInfix : bool) (psFieldLabels
    : list FieldLabel.FieldLabel) (psUnivTyVars
    : list (VarBndr Var%type Specificity)%type) (psReqTheta : ThetaType)
  (psExTyVars : list (VarBndr Var%type Specificity)%type) (psProvTheta
    : ThetaType) (psResultTy : Type_) (psMatcher : PatSynMatcher) (psBuilder
    : PatSynBuilder)
   : PatSyn
with ConLike : Type :=
  | RealDataCon : DataCon -> ConLike
  | PatSynCon : PatSyn -> ConLike
with IdInfo : Type :=
  | Mk_IdInfo (ruleInfo : RuleInfo) (realUnfoldingInfo : Unfolding)
  (inlinePragInfo : BasicTypes.InlinePragma) (occInfo : BasicTypes.OccInfo)
  (dmdSigInfo : DmdSig) (cprSigInfo : GHC.Types.Cpr.CprSig) (demandInfo : Demand)
  (bitfield : BitField) (lfInfo : (option GHC.StgToCmm.Types.LambdaFormInfo))
  (tagSig : (option GHC.Stg.InferTags.TagSig.TagSig))
   : IdInfo
with DmdSig : Type := | Mk_DmdSig : DmdType -> DmdSig
with DmdType : Type :=
  | Mk_DmdType (dt_env : DmdEnv) (dt_args : list Demand) : DmdType
with DmdEnv : Type :=
  | DE (de_fvs : ((UniqFM.UniqFM Var)%type Demand)) (de_div : Divergence) : DmdEnv
with TyConDetails : Type :=
  | AlgTyCon (tyConCType : option CType) (algTcGadtSyntax : bool)
  (algTcStupidTheta : list PredType) (algTcRhs : AlgTyConRhs) (algTcFields
    : FieldLabel.FieldLabelEnv) (algTcFlavour : AlgTyConFlav)
   : TyConDetails
  | SynonymTyCon (synTcRhs : Type_) (synIsTau : bool) (synIsFamFree : bool)
  (synIsForgetful : bool) (synIsConcrete : bool)
   : TyConDetails
  | FamilyTyCon (famTcResVar : option Name.Name) (famTcFlav : FamTyConFlav)
  (famTcParent : option TyCon) (famTcInj : Injectivity)
   : TyConDetails
  | PrimTyCon (primRepName : TyConRepName) : TyConDetails
  | PromotedDataCon (dataCon : DataCon) (tcRepName : TyConRepName) (promDcInfo
    : PromDataConInfo)
   : TyConDetails
  | TcTyCon (tctc_scoped_tvs : list (Name.Name * Var%type)%type) (tctc_is_poly
    : bool) (tctc_flavour : BasicTypes.TyConFlavour TyCon)
   : TyConDetails
with AlgTyConRhs : Type :=
  | AbstractTyCon : AlgTyConRhs
  | DataTyCon (data_cons : list DataCon) (data_cons_size : nat) (is_enum : bool)
  (is_type_data : bool) (data_fixed_lev : bool)
   : AlgTyConRhs
  | TupleTyCon (data_con : DataCon) (tup_sort : BasicTypes.TupleSort)
   : AlgTyConRhs
  | SumTyCon (data_cons : list DataCon) (data_cons_size : nat) : AlgTyConRhs
  | NewTyCon (data_con : DataCon) (nt_rhs : Type_) (nt_etad_rhs
    : (list Var%type * Type_)%type) (nt_co : CoAxiom Unbranched) (nt_fixed_rep
    : bool)
   : AlgTyConRhs
with TyFamEqnValidityInfo : Type :=
  | NoVI : TyFamEqnValidityInfo
  | VI (vi_loc : SrcLoc.SrcSpan) (vi_qtvs : list Var%type) (vi_non_user_tvs
    : (UniqSet.UniqSet Var%type)%type) (vi_pats : list Type_) (vi_rhs : Type_)
   : TyFamEqnValidityInfo.

#[global] Definition VarEnv :=
  (UniqFM.UniqFM Var)%type.

#[global] Definition TyVar :=
  Var%type.

#[global] Definition TyVarSet :=
  (UniqSet.UniqSet TyVar)%type.

#[global] Definition TyConBinder :=
  (VarBndr TyVar TyConBndrVis)%type.

#[global] Definition TcTyVar :=
  Var%type.

#[global] Definition InvisTVBinder :=
  (VarBndr TyVar Specificity)%type.

#[global] Definition Id :=
  Var%type.

#[global] Definition TyCoVar :=
  Id%type.

#[global] Definition ClassOpItem :=
  (Id * DefMethInfo)%type%type.

#[global] Definition NormaliseStepper ev :=
  (GHC.Core.TyCon.RecWalk.RecTcChecker ->
   TyCon -> list Type_ -> NormaliseStepResult ev)%type.

#[global] Definition CoreBndr :=
  Var%type.

#[global] Definition InBndr :=
  CoreBndr%type.

#[global] Definition OutBndr :=
  CoreBndr%type.

Inductive TaggedBndr t : Type := | TB : CoreBndr -> t -> TaggedBndr t.

#[global] Definition DIdEnv :=
  (UniqFM.UniqFM Var)%type.

#[global] Definition DVarEnv :=
  (UniqFM.UniqFM Var)%type.

#[global] Definition DVarSet :=
  (UniqSet.UniqSet Var)%type.

#[global] Definition CoVar :=
  Id%type.

#[global] Definition CoVarEnv :=
  (UniqFM.UniqFM CoVar)%type.

#[global] Definition CoVarSet :=
  (UniqSet.UniqSet CoVar)%type.

#[global] Definition InCoVar :=
  CoVar%type.

#[global] Definition OutCoVar :=
  CoVar%type.

#[global] Definition DFunId :=
  Id%type.

#[global] Definition DIdSet :=
  (UniqSet.UniqSet Id)%type.

#[global] Definition EvId :=
  Id%type.

#[global] Definition DictId :=
  EvId%type.

#[global] Definition EqVar :=
  EvId%type.

#[global] Definition EvVar :=
  EvId%type.

#[global] Definition IpId :=
  EvId%type.

#[global] Definition IdEnv :=
  (UniqFM.UniqFM Id)%type.

#[global] Definition IdSet :=
  (UniqSet.UniqSet Id)%type.

#[global] Definition IdUnfoldingFun :=
  (Id -> Unfolding)%type.

#[global] Definition InId :=
  Id%type.

#[global] Definition JoinId :=
  Id%type.

#[global] Definition NcId :=
  Id%type.

#[global] Definition OutId :=
  Id%type.

#[global] Definition DTyCoVarSet :=
  (UniqSet.UniqSet TyCoVar)%type.

#[global] Definition ForAllTyBinder :=
  (VarBndr TyCoVar ForAllTyFlag)%type.

Inductive PiTyBinder : Type :=
  | Named : ForAllTyBinder -> PiTyBinder
  | Anon : (Scaled Type_) -> FunTyFlag -> PiTyBinder.

#[global] Definition PiTyVarBinder :=
  PiTyBinder%type.

#[global] Definition InvisTyBinder :=
  (VarBndr TyCoVar Specificity)%type.

#[global] Definition ReqTyBinder :=
  (VarBndr TyCoVar unit)%type.

#[global] Definition TyCoVarEnv :=
  (UniqFM.UniqFM TyCoVar)%type.

#[global] Definition TyCoVarSet :=
  (UniqSet.UniqSet TyCoVar)%type.

#[global] Definition InVar :=
  Var%type.

#[global] Definition KindVar :=
  Var%type.

#[global] Definition OutVar :=
  Var%type.

#[global] Definition TKVar :=
  Var%type.

#[global] Definition DTyVarEnv :=
  (UniqFM.UniqFM TyVar)%type.

#[global] Definition DTyVarSet :=
  (UniqSet.UniqSet TyVar)%type.

Inductive ExpandSynResult tyco : Type :=
  | NoExpansion : ExpandSynResult tyco
  | ExpandsSyn
   : list (TyVar * tyco)%type -> Type_ -> list tyco -> ExpandSynResult tyco.

#[global] Definition InTyVar :=
  TyVar%type.

Inductive AltCon : Type :=
  | DataAlt : DataCon -> AltCon
  | LitAlt : Literal -> AltCon
  | DEFAULT : AltCon.

Inductive Alt b : Type := | Mk_Alt : AltCon -> list b -> (Expr b) -> Alt b
with Expr b : Type :=
  | Mk_Var : Id -> Expr b
  | Lit : Literal -> Expr b
  | App : (Expr b) -> (Expr%type b) -> Expr b
  | Lam : b -> (Expr b) -> Expr b
  | Let : (Bind b) -> (Expr b) -> Expr b
  | Case : (Expr b) -> b -> Type_ -> list (Alt b) -> Expr b
  | Cast : (Expr b) -> CoercionR -> Expr b
  | Mk_Type : Type_ -> Expr b
  | Mk_Coercion : Coercion -> Expr b
with Bind b : Type :=
  | NonRec : b -> (Expr b) -> Bind b
  | Rec : list (b * (Expr b))%type -> Bind b.

#[global] Definition Arg :=
  Expr%type.

#[global] Definition CoreAlt :=
  (Alt CoreBndr)%type.

#[global] Definition InAlt :=
  CoreAlt%type.

#[global] Definition OutAlt :=
  CoreAlt%type.

#[global] Definition CoreArg :=
  (Arg CoreBndr)%type.

#[global] Definition InArg :=
  CoreArg%type.

#[global] Definition OutArg :=
  CoreArg%type.

#[global] Definition TaggedArg t :=
  (Arg (TaggedBndr t))%type.

#[global] Definition CoreBind :=
  (Bind CoreBndr)%type.

#[global] Definition CoreProgram :=
  (list CoreBind)%type.

#[global] Definition InBind :=
  CoreBind%type.

#[global] Definition OutBind :=
  CoreBind%type.

#[global] Definition TaggedBind t :=
  (Bind (TaggedBndr t))%type.

#[global] Definition CoreExpr :=
  (Expr CoreBndr)%type.

#[global] Definition InExpr :=
  CoreExpr%type.

#[global] Definition OutExpr :=
  CoreExpr%type.

#[global] Definition TaggedExpr t :=
  (Expr (TaggedBndr t))%type.

#[global] Definition TaggedAlt t :=
  (Alt (TaggedBndr t))%type.

Inductive AnnAlt bndr annot : Type :=
  | Mk_AnnAlt
   : AltCon ->
     list bndr ->
     ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr annot) ->
     AnnAlt bndr annot
with AnnExpr' bndr annot : Type :=
  | AnnVar : Id -> AnnExpr' bndr annot
  | AnnLit : Literal -> AnnExpr' bndr annot
  | AnnLam
   : bndr ->
     ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr annot) ->
     AnnExpr' bndr annot
  | AnnApp
   : ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr
      annot) ->
     ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr annot) ->
     AnnExpr' bndr annot
  | AnnCase
   : ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr
      annot) ->
     bndr -> Type_ -> list (AnnAlt bndr annot) -> AnnExpr' bndr annot
  | AnnLet
   : (AnnBind bndr annot) ->
     ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr annot) ->
     AnnExpr' bndr annot
  | AnnCast
   : ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr
      annot) ->
     (annot * Coercion)%type -> AnnExpr' bndr annot
  | AnnType : Type_ -> AnnExpr' bndr annot
  | AnnCoercion : Coercion -> AnnExpr' bndr annot
with AnnBind bndr annot : Type :=
  | AnnNonRec
   : bndr ->
     ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr annot) ->
     AnnBind bndr annot
  | AnnRec
   : list (bndr *
           (fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr
           annot)%type ->
     AnnBind bndr annot.

#[global] Definition AnnExpr :=
  fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type.

#[global] Definition DataConEnv :=
  (UniqFM.UniqFM DataCon)%type.

#[global] Definition OutTyVar :=
  TyVar%type.

#[global] Definition ReqTVBinder :=
  (VarBndr TyVar unit)%type.

Inductive TyCoFolder env a : Type :=
  | Mk_TyCoFolder (tcf_view : Type_ -> option Type_) (tcf_tyvar
    : env -> TyVar -> a) (tcf_covar : env -> CoVar -> a) (tcf_hole
    : env -> CoercionHole -> a) (tcf_tycobinder
    : env -> TyCoVar -> ForAllTyFlag -> env)
   : TyCoFolder env a.

#[global] Definition TyVarBinder :=
  (VarBndr TyVar ForAllTyFlag)%type.

#[global] Definition TyVarEnv :=
  (UniqFM.UniqFM Var)%type.

#[global] Definition TypeVar :=
  Var%type.

#[global] Definition DmdTransformer :=
  (SubDemand -> DmdType)%type.

#[global] Definition LiftCoEnv :=
  (VarEnv Coercion)%type.

Inductive LiftingContext : Type :=
  | LC : GHC.Core.TyCo.Subst.Subst -> LiftCoEnv -> LiftingContext.

#[global] Definition TidyEnv :=
  (OccName.TidyOccEnv * VarEnv Var)%type%type.

#[global] Definition VarSet :=
  (UniqSet.UniqSet Var)%type.

Inductive InScopeSet : Type := | InScope : VarSet -> InScopeSet.

Inductive InScopeEnv : Type :=
  | ISE : InScopeSet -> IdUnfoldingFun -> InScopeEnv.

#[global] Definition RuleFun :=
  (GHC.Core.Rules.Config.RuleOpts ->
   InScopeEnv -> Id -> list CoreExpr -> option CoreExpr)%type.

Inductive CoreRule : Type :=
  | Rule (ru_name : BasicTypes.RuleName) (ru_act : BasicTypes.Activation) (ru_fn
    : Name.Name) (ru_rough : list (option Name.Name)) (ru_bndrs : list CoreBndr)
  (ru_args : list CoreExpr) (ru_rhs : CoreExpr) (ru_auto : bool) (ru_origin
    : Module.Module) (ru_orphan : IsOrphan) (ru_local : bool)
   : CoreRule
  | BuiltinRule (ru_name : BasicTypes.RuleName) (ru_fn : Name.Name) (ru_nargs
    : nat) (ru_try : RuleFun)
   : CoreRule.

Inductive RnEnv2 : Type :=
  | RV2 (envL : VarEnv Var) (envR : VarEnv Var) (in_scope : InScopeSet) : RnEnv2.

Inductive TyCoMapper env m : Type :=
  | Mk_TyCoMapper (tcm_tyvar : env -> TyVar -> m Type_) (tcm_covar
    : env -> CoVar -> m Coercion) (tcm_hole : env -> CoercionHole -> m Coercion)
  (tcm_tycobinder
    : forall {r}, env -> TyCoVar -> ForAllTyFlag -> (env -> TyCoVar -> m r) -> m r)
  (tcm_tycon : TyCon -> m TyCon)
   : TyCoMapper env m.

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

Arguments Bndr {_} {_} _ _.

Arguments NS_Done {_}.

Arguments NS_Abort {_}.

Arguments NS_Step {_} _ _ _.

Arguments Mk_Scaled {_} _ _.

Arguments TB {_} _ _.

Arguments NoExpansion {_}.

Arguments ExpandsSyn {_} _ _ _.

Arguments Mk_Alt {_} _ _ _.

Arguments Mk_Var {_} _.

Arguments Lit {_} _.

Arguments App {_} _ _.

Arguments Lam {_} _ _.

Arguments Let {_} _ _.

Arguments Case {_} _ _ _ _.

Arguments Cast {_} _ _.

Arguments Mk_Type {_} _.

Arguments Mk_Coercion {_} _.

Arguments NonRec {_} _ _.

Arguments Rec {_} _.

Arguments Mk_AnnAlt {_} {_} _ _ _.

Arguments AnnVar {_} {_} _.

Arguments AnnLit {_} {_} _.

Arguments AnnLam {_} {_} _ _.

Arguments AnnApp {_} {_} _ _.

Arguments AnnCase {_} {_} _ _ _ _.

Arguments AnnLet {_} {_} _ _.

Arguments AnnCast {_} {_} _ _.

Arguments AnnType {_} {_} _.

Arguments AnnCoercion {_} {_} _.

Arguments AnnNonRec {_} {_} _ _.

Arguments AnnRec {_} {_} _.

Arguments Mk_TyCoFolder {_} {_} _ _ _ _ _.

Arguments Mk_TyCoMapper {_} {_} _ _ _ _ _.

Instance Default__UnfoldingGuidance : HsToCoq.Err.Default UnfoldingGuidance :=
  HsToCoq.Err.Build_Default _ (UnfWhen HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default).

Instance Default__UnfoldingCache : HsToCoq.Err.Default UnfoldingCache :=
  HsToCoq.Err.Build_Default _ (Mk_UnfoldingCache HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__Unfolding : HsToCoq.Err.Default Unfolding :=
  HsToCoq.Err.Build_Default _ NoUnfolding.

Instance Default__TypeShape : HsToCoq.Err.Default TypeShape :=
  HsToCoq.Err.Build_Default _ TsUnk.

Instance Default__StrictnessMark : HsToCoq.Err.Default StrictnessMark :=
  HsToCoq.Err.Build_Default _ MarkedStrict.

Instance Default__Specificity : HsToCoq.Err.Default Specificity :=
  HsToCoq.Err.Build_Default _ InferredSpec.

Instance Default__PrimElemRep : HsToCoq.Err.Default PrimElemRep :=
  HsToCoq.Err.Build_Default _ Int8ElemRep.

Instance Default__PrimRep : HsToCoq.Err.Default PrimRep :=
  HsToCoq.Err.Build_Default _ Int8Rep.

Instance Default__PrimOrVoidRep : HsToCoq.Err.Default PrimOrVoidRep :=
  HsToCoq.Err.Build_Default _ VoidRep.

Instance Default__PromDataConInfo : HsToCoq.Err.Default PromDataConInfo :=
  HsToCoq.Err.Build_Default _ NoPromInfo.

Instance Default__MCoercion : HsToCoq.Err.Default MCoercion :=
  HsToCoq.Err.Build_Default _ MRefl.

Instance Default__KillFlags : HsToCoq.Err.Default KillFlags :=
  HsToCoq.Err.Build_Default _ (Mk_KillFlags HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__IsOrphan : HsToCoq.Err.Default IsOrphan :=
  HsToCoq.Err.Build_Default _ Mk_IsOrphan.

Instance Default__Injectivity : HsToCoq.Err.Default Injectivity :=
  HsToCoq.Err.Build_Default _ NotInjective.

Instance Default__HsImplBang : HsToCoq.Err.Default HsImplBang :=
  HsToCoq.Err.Build_Default _ HsLazy.

Instance Default__FunTyFlag : HsToCoq.Err.Default FunTyFlag :=
  HsToCoq.Err.Build_Default _ FTF_T_T.

Instance Default__FunSel : HsToCoq.Err.Default FunSel :=
  HsToCoq.Err.Build_Default _ SelMult.

Instance Default__ForAllTyFlag : HsToCoq.Err.Default ForAllTyFlag :=
  HsToCoq.Err.Build_Default _ Required.

Instance Default__TyConBndrVis : HsToCoq.Err.Default TyConBndrVis :=
  HsToCoq.Err.Build_Default _ AnonTCB.

Instance Default__FamTyConFlav : HsToCoq.Err.Default FamTyConFlav :=
  HsToCoq.Err.Build_Default _ OpenSynFamilyTyCon.

Instance Default__ExportFlag : HsToCoq.Err.Default ExportFlag :=
  HsToCoq.Err.Build_Default _ NotExported.

Instance Default__IdScope : HsToCoq.Err.Default IdScope :=
  HsToCoq.Err.Build_Default _ GlobalId.

Instance Default__Divergence : HsToCoq.Err.Default Divergence :=
  HsToCoq.Err.Build_Default _ Diverges.

Instance Default__CoSel : HsToCoq.Err.Default CoSel :=
  HsToCoq.Err.Build_Default _ SelForAll.

Instance Default__Demand : HsToCoq.Err.Default Demand :=
  HsToCoq.Err.Build_Default _ BotDmd.

Instance Default__CafInfo : HsToCoq.Err.Default CafInfo :=
  HsToCoq.Err.Build_Default _ MayHaveCafRefs.

Instance Default__AlgTyConFlav : HsToCoq.Err.Default AlgTyConFlav :=
  HsToCoq.Err.Build_Default _ UnboxedSumTyCon.

Instance Default__ClassBody : HsToCoq.Err.Default ClassBody :=
  HsToCoq.Err.Build_Default _ AbstractClass.

Instance Default__IdDetails : HsToCoq.Err.Default IdDetails :=
  HsToCoq.Err.Build_Default _ VanillaId.

Instance Default__DataConRep : HsToCoq.Err.Default DataConRep :=
  HsToCoq.Err.Build_Default _ NoDataConRep.

Instance Default__DmdEnv : HsToCoq.Err.Default DmdEnv :=
  HsToCoq.Err.Build_Default _ (DE HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__AltCon : HsToCoq.Err.Default AltCon :=
  HsToCoq.Err.Build_Default _ DEFAULT.

#[global] Definition ug_args (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_args' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs ug_args _ _ => ug_args
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_args' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

#[global] Definition ug_arity (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen ug_arity _ _ => ug_arity
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_arity' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_arity' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

#[global] Definition ug_boring_ok (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ ug_boring_ok => ug_boring_ok
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_boring_ok' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_boring_ok' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

#[global] Definition ug_res (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_res' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs _ _ ug_res => ug_res
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_res' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

#[global] Definition ug_size (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_size' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs _ ug_size _ => ug_size
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_size' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

#[global] Definition ug_unsat_ok (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ ug_unsat_ok _ => ug_unsat_ok
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_unsat_ok' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_unsat_ok' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

#[global] Definition uf_expandable (arg_0__ : UnfoldingCache) :=
  let 'Mk_UnfoldingCache _ _ _ uf_expandable := arg_0__ in
  uf_expandable.

#[global] Definition uf_is_conlike (arg_0__ : UnfoldingCache) :=
  let 'Mk_UnfoldingCache _ uf_is_conlike _ _ := arg_0__ in
  uf_is_conlike.

#[global] Definition uf_is_value (arg_0__ : UnfoldingCache) :=
  let 'Mk_UnfoldingCache uf_is_value _ _ _ := arg_0__ in
  uf_is_value.

#[global] Definition uf_is_work_free (arg_0__ : UnfoldingCache) :=
  let 'Mk_UnfoldingCache _ _ uf_is_work_free _ := arg_0__ in
  uf_is_work_free.

#[global] Definition kf_abs (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags kf_abs _ _ := arg_0__ in
  kf_abs.

#[global] Definition kf_called_once (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags _ _ kf_called_once := arg_0__ in
  kf_called_once.

#[global] Definition kf_used_once (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags _ kf_used_once _ := arg_0__ in
  kf_used_once.

#[global] Definition classBody (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ _ _ classBody := arg_0__ in
  classBody.

#[global] Definition classFunDeps (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ _ classFunDeps _ := arg_0__ in
  classFunDeps.

#[global] Definition classKey (arg_0__ : Class) :=
  let 'Mk_Class _ _ classKey _ _ _ := arg_0__ in
  classKey.

#[global] Definition className (arg_0__ : Class) :=
  let 'Mk_Class _ className _ _ _ _ := arg_0__ in
  className.

#[global] Definition classTyCon (arg_0__ : Class) :=
  let 'Mk_Class classTyCon _ _ _ _ _ := arg_0__ in
  classTyCon.

#[global] Definition classTyVars (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ classTyVars _ _ := arg_0__ in
  classTyVars.

#[global] Definition cls_ats (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `cls_ats' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ cls_ats _ _ => cls_ats
  end.

#[global] Definition cls_min_def (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `cls_min_def' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ _ _ cls_min_def => cls_min_def
  end.

#[global] Definition cls_ops (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `cls_ops' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ _ cls_ops _ => cls_ops
  end.

#[global] Definition cls_sc_sel_ids (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `cls_sc_sel_ids' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ cls_sc_sel_ids _ _ _ => cls_sc_sel_ids
  end.

#[global] Definition cls_sc_theta (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `cls_sc_theta' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass cls_sc_theta _ _ _ _ => cls_sc_theta
  end.

#[global] Definition tyConArity (arg_0__ : TyCon) :=
  let 'Mk_TyCon _ _ _ _ _ _ _ tyConArity _ _ _ := arg_0__ in
  tyConArity.

#[global] Definition tyConBinders (arg_0__ : TyCon) :=
  let 'Mk_TyCon _ _ tyConBinders _ _ _ _ _ _ _ _ := arg_0__ in
  tyConBinders.

#[global] Definition tyConDetails (arg_0__ : TyCon) :=
  let 'Mk_TyCon _ _ _ _ _ _ _ _ _ _ tyConDetails := arg_0__ in
  tyConDetails.

#[global] Definition tyConHasClosedResKind (arg_0__ : TyCon) :=
  let 'Mk_TyCon _ _ _ _ tyConHasClosedResKind _ _ _ _ _ _ := arg_0__ in
  tyConHasClosedResKind.

#[global] Definition tyConKind (arg_0__ : TyCon) :=
  let 'Mk_TyCon _ _ _ _ _ _ tyConKind _ _ _ _ := arg_0__ in
  tyConKind.

#[global] Definition tyConName (arg_0__ : TyCon) :=
  let 'Mk_TyCon _ tyConName _ _ _ _ _ _ _ _ _ := arg_0__ in
  tyConName.

#[global] Definition tyConNullaryTy (arg_0__ : TyCon) :=
  let 'Mk_TyCon _ _ _ _ _ _ _ _ tyConNullaryTy _ _ := arg_0__ in
  tyConNullaryTy.

#[global] Definition tyConResKind (arg_0__ : TyCon) :=
  let 'Mk_TyCon _ _ _ tyConResKind _ _ _ _ _ _ _ := arg_0__ in
  tyConResKind.

#[global] Definition tyConRoles (arg_0__ : TyCon) :=
  let 'Mk_TyCon _ _ _ _ _ _ _ _ _ tyConRoles _ := arg_0__ in
  tyConRoles.

#[global] Definition tyConTyVars (arg_0__ : TyCon) :=
  let 'Mk_TyCon _ _ _ _ _ tyConTyVars _ _ _ _ _ := arg_0__ in
  tyConTyVars.

#[global] Definition tyConUnique (arg_0__ : TyCon) :=
  let 'Mk_TyCon tyConUnique _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  tyConUnique.

#[global] Definition idScope (arg_0__ : Var) :=
  let 'Mk_Id _ _ _ _ idScope _ _ := arg_0__ in
  idScope.

#[global] Definition id_details (arg_0__ : Var) :=
  let 'Mk_Id _ _ _ _ _ id_details _ := arg_0__ in
  id_details.

#[global] Definition realUnique (arg_0__ : Var) :=
  let 'Mk_Id _ realUnique _ _ _ _ _ := arg_0__ in
  realUnique.

#[global] Definition varMult (arg_0__ : Var) :=
  let 'Mk_Id _ _ _ varMult _ _ _ := arg_0__ in
  varMult.

#[global] Definition varName (arg_0__ : Var) :=
  let 'Mk_Id varName _ _ _ _ _ _ := arg_0__ in
  varName.

#[global] Definition varType (arg_0__ : Var) :=
  let 'Mk_Id _ _ varType _ _ _ _ := arg_0__ in
  varType.

#[global] Definition id_concrete_tvs (arg_0__ : IdDetails) :=
  match arg_0__ with
  | VanillaId =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_concrete_tvs' has no match in constructor `VanillaId' of type `IdDetails'")
  | RecSelId _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_concrete_tvs' has no match in constructor `RecSelId' of type `IdDetails'")
  | DataConWorkId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_concrete_tvs' has no match in constructor `DataConWorkId' of type `IdDetails'")
  | DataConWrapId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_concrete_tvs' has no match in constructor `DataConWrapId' of type `IdDetails'")
  | ClassOpId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_concrete_tvs' has no match in constructor `ClassOpId' of type `IdDetails'")
  | RepPolyId id_concrete_tvs => id_concrete_tvs
  | PrimOpId _ id_concrete_tvs => id_concrete_tvs
  | FCallId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_concrete_tvs' has no match in constructor `FCallId' of type `IdDetails'")
  | TickBoxOpId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_concrete_tvs' has no match in constructor `TickBoxOpId' of type `IdDetails'")
  | Mk_DFunId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_concrete_tvs' has no match in constructor `Mk_DFunId' of type `IdDetails'")
  | Mk_JoinId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_concrete_tvs' has no match in constructor `Mk_JoinId' of type `IdDetails'")
  | WorkerLikeId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_concrete_tvs' has no match in constructor `WorkerLikeId' of type `IdDetails'")
  end.

#[global] Definition id_primop (arg_0__ : IdDetails) :=
  match arg_0__ with
  | VanillaId =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_primop' has no match in constructor `VanillaId' of type `IdDetails'")
  | RecSelId _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_primop' has no match in constructor `RecSelId' of type `IdDetails'")
  | DataConWorkId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_primop' has no match in constructor `DataConWorkId' of type `IdDetails'")
  | DataConWrapId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_primop' has no match in constructor `DataConWrapId' of type `IdDetails'")
  | ClassOpId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_primop' has no match in constructor `ClassOpId' of type `IdDetails'")
  | RepPolyId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_primop' has no match in constructor `RepPolyId' of type `IdDetails'")
  | PrimOpId id_primop _ => id_primop
  | FCallId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_primop' has no match in constructor `FCallId' of type `IdDetails'")
  | TickBoxOpId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_primop' has no match in constructor `TickBoxOpId' of type `IdDetails'")
  | Mk_DFunId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_primop' has no match in constructor `Mk_DFunId' of type `IdDetails'")
  | Mk_JoinId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_primop' has no match in constructor `Mk_JoinId' of type `IdDetails'")
  | WorkerLikeId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_primop' has no match in constructor `WorkerLikeId' of type `IdDetails'")
  end.

#[global] Definition sel_cons (arg_0__ : IdDetails) :=
  match arg_0__ with
  | VanillaId =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_cons' has no match in constructor `VanillaId' of type `IdDetails'")
  | RecSelId _ _ _ sel_cons => sel_cons
  | DataConWorkId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_cons' has no match in constructor `DataConWorkId' of type `IdDetails'")
  | DataConWrapId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_cons' has no match in constructor `DataConWrapId' of type `IdDetails'")
  | ClassOpId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_cons' has no match in constructor `ClassOpId' of type `IdDetails'")
  | RepPolyId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_cons' has no match in constructor `RepPolyId' of type `IdDetails'")
  | PrimOpId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_cons' has no match in constructor `PrimOpId' of type `IdDetails'")
  | FCallId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_cons' has no match in constructor `FCallId' of type `IdDetails'")
  | TickBoxOpId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_cons' has no match in constructor `TickBoxOpId' of type `IdDetails'")
  | Mk_DFunId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_cons' has no match in constructor `Mk_DFunId' of type `IdDetails'")
  | Mk_JoinId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_cons' has no match in constructor `Mk_JoinId' of type `IdDetails'")
  | WorkerLikeId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_cons' has no match in constructor `WorkerLikeId' of type `IdDetails'")
  end.

#[global] Definition sel_fieldLabel (arg_0__ : IdDetails) :=
  match arg_0__ with
  | VanillaId =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_fieldLabel' has no match in constructor `VanillaId' of type `IdDetails'")
  | RecSelId _ sel_fieldLabel _ _ => sel_fieldLabel
  | DataConWorkId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_fieldLabel' has no match in constructor `DataConWorkId' of type `IdDetails'")
  | DataConWrapId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_fieldLabel' has no match in constructor `DataConWrapId' of type `IdDetails'")
  | ClassOpId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_fieldLabel' has no match in constructor `ClassOpId' of type `IdDetails'")
  | RepPolyId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_fieldLabel' has no match in constructor `RepPolyId' of type `IdDetails'")
  | PrimOpId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_fieldLabel' has no match in constructor `PrimOpId' of type `IdDetails'")
  | FCallId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_fieldLabel' has no match in constructor `FCallId' of type `IdDetails'")
  | TickBoxOpId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_fieldLabel' has no match in constructor `TickBoxOpId' of type `IdDetails'")
  | Mk_DFunId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_fieldLabel' has no match in constructor `Mk_DFunId' of type `IdDetails'")
  | Mk_JoinId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_fieldLabel' has no match in constructor `Mk_JoinId' of type `IdDetails'")
  | WorkerLikeId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_fieldLabel' has no match in constructor `WorkerLikeId' of type `IdDetails'")
  end.

#[global] Definition sel_naughty (arg_0__ : IdDetails) :=
  match arg_0__ with
  | VanillaId =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `VanillaId' of type `IdDetails'")
  | RecSelId _ _ sel_naughty _ => sel_naughty
  | DataConWorkId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `DataConWorkId' of type `IdDetails'")
  | DataConWrapId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `DataConWrapId' of type `IdDetails'")
  | ClassOpId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `ClassOpId' of type `IdDetails'")
  | RepPolyId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `RepPolyId' of type `IdDetails'")
  | PrimOpId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `PrimOpId' of type `IdDetails'")
  | FCallId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `FCallId' of type `IdDetails'")
  | TickBoxOpId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `TickBoxOpId' of type `IdDetails'")
  | Mk_DFunId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `Mk_DFunId' of type `IdDetails'")
  | Mk_JoinId _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `Mk_JoinId' of type `IdDetails'")
  | WorkerLikeId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `WorkerLikeId' of type `IdDetails'")
  end.

#[global] Definition dcConcreteTyVars (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ dcConcreteTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcConcreteTyVars.

#[global] Definition dcEqSpec (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ dcEqSpec _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcEqSpec.

#[global] Definition dcExTyCoVars (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ dcExTyCoVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcExTyCoVars.

#[global] Definition dcFields (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcFields _ _ _ _ _ _ _ _ := arg_0__ in
  dcFields.

#[global] Definition dcInfix (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcInfix _ := arg_0__ in
  dcInfix.

#[global] Definition dcName (arg_0__ : DataCon) :=
  let 'MkData dcName _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcName.

#[global] Definition dcOrigArgTys (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ dcOrigArgTys _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcOrigArgTys.

#[global] Definition dcOrigResTy (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ dcOrigResTy _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcOrigResTy.

#[global] Definition dcOtherTheta (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ dcOtherTheta _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcOtherTheta.

#[global] Definition dcPromoted (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcPromoted := arg_0__ in
  dcPromoted.

#[global] Definition dcRep (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRep _ _ _ _ _ _ := arg_0__ in
  dcRep.

#[global] Definition dcRepArity (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepArity _ _ _ _ _ := arg_0__ in
  dcRepArity.

#[global] Definition dcRepTyCon (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepTyCon _ _ _ := arg_0__ in
  dcRepTyCon.

#[global] Definition dcRepType (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepType _ _ := arg_0__ in
  dcRepType.

#[global] Definition dcSourceArity (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcSourceArity _ _ _ _ :=
    arg_0__ in
  dcSourceArity.

#[global] Definition dcSrcBangs (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ dcSrcBangs _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcSrcBangs.

#[global] Definition dcStupidTheta (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ dcStupidTheta _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcStupidTheta.

#[global] Definition dcTag (arg_0__ : DataCon) :=
  let 'MkData _ _ dcTag _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcTag.

#[global] Definition dcUnique (arg_0__ : DataCon) :=
  let 'MkData _ dcUnique _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcUnique.

#[global] Definition dcUnivTyVars (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ dcUnivTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcUnivTyVars.

#[global] Definition dcUserTyVarBinders (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ dcUserTyVarBinders _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcUserTyVarBinders.

#[global] Definition dcVanilla (arg_0__ : DataCon) :=
  let 'MkData _ _ _ dcVanilla _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcVanilla.

#[global] Definition dcWorkId (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcWorkId _ _ _ _ _ _ _ := arg_0__ in
  dcWorkId.

#[global] Definition dcr_arg_tys (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_arg_tys' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ dcr_arg_tys _ _ => dcr_arg_tys
  end.

#[global] Definition dcr_bangs (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_bangs' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ _ _ dcr_bangs => dcr_bangs
  end.

#[global] Definition dcr_boxer (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_boxer' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ dcr_boxer _ _ _ => dcr_boxer
  end.

#[global] Definition dcr_stricts (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_stricts' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ _ dcr_stricts _ => dcr_stricts
  end.

#[global] Definition psArgs (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ psArgs _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psArgs.

#[global] Definition psArity (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ psArity _ _ _ _ _ _ _ _ _ := arg_0__ in
  psArity.

#[global] Definition psBuilder (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ _ _ psBuilder := arg_0__ in
  psBuilder.

#[global] Definition psExTyVars (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ psExTyVars _ _ _ _ := arg_0__ in
  psExTyVars.

#[global] Definition psFieldLabels (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ psFieldLabels _ _ _ _ _ _ _ := arg_0__ in
  psFieldLabels.

#[global] Definition psInfix (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ psInfix _ _ _ _ _ _ _ _ := arg_0__ in
  psInfix.

#[global] Definition psMatcher (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ _ psMatcher _ := arg_0__ in
  psMatcher.

#[global] Definition psName (arg_0__ : PatSyn) :=
  let 'MkPatSyn psName _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psName.

#[global] Definition psProvTheta (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ psProvTheta _ _ _ := arg_0__ in
  psProvTheta.

#[global] Definition psReqTheta (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ psReqTheta _ _ _ _ _ := arg_0__ in
  psReqTheta.

#[global] Definition psResultTy (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ psResultTy _ _ := arg_0__ in
  psResultTy.

#[global] Definition psUnique (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ psUnique _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psUnique.

#[global] Definition psUnivTyVars (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ psUnivTyVars _ _ _ _ _ _ := arg_0__ in
  psUnivTyVars.

#[global] Definition bitfield (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ _ bitfield _ _ := arg_0__ in
  bitfield.

#[global] Definition cprSigInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ cprSigInfo _ _ _ _ := arg_0__ in
  cprSigInfo.

#[global] Definition demandInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ demandInfo _ _ _ := arg_0__ in
  demandInfo.

#[global] Definition dmdSigInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ dmdSigInfo _ _ _ _ _ := arg_0__ in
  dmdSigInfo.

#[global] Definition inlinePragInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ inlinePragInfo _ _ _ _ _ _ _ := arg_0__ in
  inlinePragInfo.

#[global] Definition lfInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ _ _ lfInfo _ := arg_0__ in
  lfInfo.

#[global] Definition occInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ occInfo _ _ _ _ _ _ := arg_0__ in
  occInfo.

#[global] Definition realUnfoldingInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ realUnfoldingInfo _ _ _ _ _ _ _ _ := arg_0__ in
  realUnfoldingInfo.

#[global] Definition ruleInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo ruleInfo _ _ _ _ _ _ _ _ _ := arg_0__ in
  ruleInfo.

#[global] Definition tagSig (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ _ _ _ tagSig := arg_0__ in
  tagSig.

#[global] Definition dt_args (arg_0__ : DmdType) :=
  let 'Mk_DmdType _ dt_args := arg_0__ in
  dt_args.

#[global] Definition dt_env (arg_0__ : DmdType) :=
  let 'Mk_DmdType dt_env _ := arg_0__ in
  dt_env.

#[global] Definition de_div (arg_0__ : DmdEnv) :=
  let 'DE _ de_div := arg_0__ in
  de_div.

#[global] Definition de_fvs (arg_0__ : DmdEnv) :=
  let 'DE de_fvs _ := arg_0__ in
  de_fvs.

#[global] Definition algTcFields (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ algTcFields _ => algTcFields
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition algTcFlavour (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ algTcFlavour => algTcFlavour
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFlavour' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFlavour' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFlavour' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFlavour' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFlavour' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition algTcGadtSyntax (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ algTcGadtSyntax _ _ _ _ => algTcGadtSyntax
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition algTcRhs (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ algTcRhs _ _ => algTcRhs
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition algTcStupidTheta (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ algTcStupidTheta _ _ _ => algTcStupidTheta
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition famTcFlav (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ famTcFlav _ _ => famTcFlav
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition famTcInj (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ famTcInj => famTcInj
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition famTcParent (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ famTcParent _ => famTcParent
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition famTcResVar (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon famTcResVar _ _ _ => famTcResVar
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition primRepName (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon primRepName => primRepName
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition promDcInfo (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `promDcInfo' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `promDcInfo' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `promDcInfo' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `promDcInfo' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ promDcInfo => promDcInfo
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `promDcInfo' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition synIsConcrete (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsConcrete' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ _ synIsConcrete => synIsConcrete
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsConcrete' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsConcrete' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsConcrete' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsConcrete' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition synIsFamFree (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ synIsFamFree _ _ => synIsFamFree
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition synIsForgetful (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsForgetful' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ synIsForgetful _ => synIsForgetful
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsForgetful' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsForgetful' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsForgetful' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsForgetful' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition synIsTau (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ synIsTau _ _ _ => synIsTau
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition synTcRhs (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon synTcRhs _ _ _ _ => synTcRhs
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition tcRepName (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ tcRepName _ => tcRepName
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition tctc_flavour (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_flavour' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_flavour' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_flavour' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_flavour' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_flavour' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ tctc_flavour => tctc_flavour
  end.

#[global] Definition tctc_is_poly (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_is_poly' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_is_poly' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_is_poly' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_is_poly' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_is_poly' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ tctc_is_poly _ => tctc_is_poly
  end.

#[global] Definition tctc_scoped_tvs (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_scoped_tvs' has no match in constructor `AlgTyCon' of type `TyConDetails'")
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_scoped_tvs' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_scoped_tvs' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_scoped_tvs' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tctc_scoped_tvs' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon tctc_scoped_tvs _ _ => tctc_scoped_tvs
  end.

#[global] Definition tyConCType (arg_0__ : TyConDetails) :=
  match arg_0__ with
  | AlgTyCon tyConCType _ _ _ _ _ => tyConCType
  | SynonymTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `SynonymTyCon' of type `TyConDetails'")
  | FamilyTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `FamilyTyCon' of type `TyConDetails'")
  | PrimTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `PrimTyCon' of type `TyConDetails'")
  | PromotedDataCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `PromotedDataCon' of type `TyConDetails'")
  | TcTyCon _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `TcTyCon' of type `TyConDetails'")
  end.

#[global] Definition data_cons (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon data_cons _ _ _ _ => data_cons
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon data_cons _ => data_cons
  | NewTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

#[global] Definition data_cons_size (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons_size' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ data_cons_size _ _ _ => data_cons_size
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons_size' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ data_cons_size => data_cons_size
  | NewTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons_size' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

#[global] Definition data_fixed_lev (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_fixed_lev' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ _ _ data_fixed_lev => data_fixed_lev
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_fixed_lev' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_fixed_lev' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_fixed_lev' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

#[global] Definition is_enum (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ is_enum _ _ => is_enum
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

#[global] Definition is_type_data (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_type_data' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ _ is_type_data _ => is_type_data
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_type_data' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_type_data' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_type_data' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

#[global] Definition nt_co (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ nt_co _ => nt_co
  end.

#[global] Definition nt_etad_rhs (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ nt_etad_rhs _ _ => nt_etad_rhs
  end.

#[global] Definition nt_fixed_rep (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_fixed_rep' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_fixed_rep' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_fixed_rep' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_fixed_rep' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ _ nt_fixed_rep => nt_fixed_rep
  end.

#[global] Definition nt_rhs (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ nt_rhs _ _ _ => nt_rhs
  end.

#[global] Definition tup_sort (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ tup_sort => tup_sort
  | SumTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

#[global] Definition vi_loc (arg_0__ : TyFamEqnValidityInfo) :=
  match arg_0__ with
  | NoVI =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `vi_loc' has no match in constructor `NoVI' of type `TyFamEqnValidityInfo'")
  | VI vi_loc _ _ _ _ => vi_loc
  end.

#[global] Definition vi_non_user_tvs (arg_0__ : TyFamEqnValidityInfo) :=
  match arg_0__ with
  | NoVI =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `vi_non_user_tvs' has no match in constructor `NoVI' of type `TyFamEqnValidityInfo'")
  | VI _ _ vi_non_user_tvs _ _ => vi_non_user_tvs
  end.

#[global] Definition vi_pats (arg_0__ : TyFamEqnValidityInfo) :=
  match arg_0__ with
  | NoVI =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `vi_pats' has no match in constructor `NoVI' of type `TyFamEqnValidityInfo'")
  | VI _ _ _ vi_pats _ => vi_pats
  end.

#[global] Definition vi_qtvs (arg_0__ : TyFamEqnValidityInfo) :=
  match arg_0__ with
  | NoVI =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `vi_qtvs' has no match in constructor `NoVI' of type `TyFamEqnValidityInfo'")
  | VI _ vi_qtvs _ _ _ => vi_qtvs
  end.

#[global] Definition vi_rhs (arg_0__ : TyFamEqnValidityInfo) :=
  match arg_0__ with
  | NoVI =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `vi_rhs' has no match in constructor `NoVI' of type `TyFamEqnValidityInfo'")
  | VI _ _ _ _ vi_rhs => vi_rhs
  end.

#[global] Definition tcf_covar {env} {a} (arg_0__ : TyCoFolder env a) :=
  let 'Mk_TyCoFolder _ _ tcf_covar _ _ := arg_0__ in
  tcf_covar.

#[global] Definition tcf_hole {env} {a} (arg_0__ : TyCoFolder env a) :=
  let 'Mk_TyCoFolder _ _ _ tcf_hole _ := arg_0__ in
  tcf_hole.

#[global] Definition tcf_tycobinder {env} {a} (arg_0__ : TyCoFolder env a) :=
  let 'Mk_TyCoFolder _ _ _ _ tcf_tycobinder := arg_0__ in
  tcf_tycobinder.

#[global] Definition tcf_tyvar {env} {a} (arg_0__ : TyCoFolder env a) :=
  let 'Mk_TyCoFolder _ tcf_tyvar _ _ _ := arg_0__ in
  tcf_tyvar.

#[global] Definition tcf_view {env} {a} (arg_0__ : TyCoFolder env a) :=
  let 'Mk_TyCoFolder tcf_view _ _ _ _ := arg_0__ in
  tcf_view.

#[global] Definition ru_act (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ ru_act _ _ _ _ _ _ _ _ _ => ru_act
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_act' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

#[global] Definition ru_args (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ ru_args _ _ _ _ _ => ru_args
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_args' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

#[global] Definition ru_auto (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ ru_auto _ _ _ => ru_auto
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_auto' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

#[global] Definition ru_bndrs (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ ru_bndrs _ _ _ _ _ _ => ru_bndrs
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_bndrs' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

#[global] Definition ru_fn (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ ru_fn _ _ _ _ _ _ _ _ => ru_fn
  | BuiltinRule _ ru_fn _ _ => ru_fn
  end.

#[global] Definition ru_local (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ ru_local => ru_local
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_local' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

#[global] Definition ru_name (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule ru_name _ _ _ _ _ _ _ _ _ _ => ru_name
  | BuiltinRule ru_name _ _ _ => ru_name
  end.

#[global] Definition ru_nargs (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_nargs' has no match in constructor `Rule' of type `CoreRule'")
  | BuiltinRule _ _ ru_nargs _ => ru_nargs
  end.

#[global] Definition ru_origin (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ ru_origin _ _ => ru_origin
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_origin' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

#[global] Definition ru_orphan (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ ru_orphan _ => ru_orphan
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_orphan' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

#[global] Definition ru_rough (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ ru_rough _ _ _ _ _ _ _ => ru_rough
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_rough' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

#[global] Definition ru_try (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_try' has no match in constructor `Rule' of type `CoreRule'")
  | BuiltinRule _ _ _ ru_try => ru_try
  end.

#[global] Definition envL (arg_0__ : RnEnv2) :=
  let 'RV2 envL _ _ := arg_0__ in
  envL.

#[global] Definition envR (arg_0__ : RnEnv2) :=
  let 'RV2 _ envR _ := arg_0__ in
  envR.

#[global] Definition in_scope (arg_0__ : RnEnv2) :=
  let 'RV2 _ _ in_scope := arg_0__ in
  in_scope.

#[global] Definition tcm_covar {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'Mk_TyCoMapper _ tcm_covar _ _ _ := arg_0__ in
  tcm_covar.

#[global] Definition tcm_hole {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'Mk_TyCoMapper _ _ tcm_hole _ _ := arg_0__ in
  tcm_hole.

#[global] Definition tcm_tycobinder {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'Mk_TyCoMapper _ _ _ tcm_tycobinder _ := arg_0__ in
  tcm_tycobinder.

#[global] Definition tcm_tycon {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'Mk_TyCoMapper _ _ _ _ tcm_tycon := arg_0__ in
  tcm_tycon.

#[global] Definition tcm_tyvar {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'Mk_TyCoMapper tcm_tyvar _ _ _ _ := arg_0__ in
  tcm_tyvar.

(* Midamble *)

(*  IdInfo: midamble *)

Require Import HsToCoq.Err.

(* --------------------- *)


(*****)

#[global] Instance Default__RuleInfo : HsToCoq.Err.Default RuleInfo :=
  HsToCoq.Err.Build_Default _ EmptyRuleInfo.

#[global] Instance Default__TickBoxOp : HsToCoq.Err.Default TickBoxOp :=
  HsToCoq.Err.Build_Default _ (TickBox HsToCoq.Err.default HsToCoq.Err.default).

(* Default__DmdType, Default__IdInfo, Default__Var, Default__DataCon
   are injected via sed in Makefile before record accessors need them.
   Default__RecSelParent is needed by record accessors for IdDetails. *)
#[global] Instance Default__RecSelParent : HsToCoq.Err.Default RecSelParent :=
  HsToCoq.Err.Build_Default _ (RecSelData HsToCoq.Err.default).
(* ---- TyCon midamble ----- *)
(* Default__AlgTyConFlav is auto-generated by hs-to-coq *)

(* ------------- Var midamble.v --------------- *)
Instance Name_NamedThing_TyCoVar : Name.NamedThing TyCoVar.
intros r d. eapply d. eapply Name.NamedThing__Dict_Build.
eapply varName. intro v. eapply Name.nameOccName. eapply varName. exact v.
Qed.
Instance Name_NamedThing_VarId : Name.NamedThing Id.
intros r d. eapply d. eapply Name.NamedThing__Dict_Build.
eapply varName. intro v. eapply Name.nameOccName. eapply varName. exact v.
Qed.


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
(* ------------- VarEnv midamble.v ------------ *)
(* GHC 9.10: InScopeSet has 1 field (VarSet only, no nat counter) *)
#[global] Instance Default__InScopeSet : HsToCoq.Err.Default InScopeSet :=
  HsToCoq.Err.Build_Default _ (InScope HsToCoq.Err.default).
#[global] Instance Default__RnEnv2 : HsToCoq.Err.Default RnEnv2 :=
  HsToCoq.Err.Build_Default _ (RV2 HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
#[global] Instance Default__TidyEnv : HsToCoq.Err.Default TidyEnv :=
  HsToCoq.Err.Build_Default _ (pair HsToCoq.Err.default HsToCoq.Err.default).

(* ------------- CoreSyn midamble.v ------------ *)
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;lia.

Ltac intro_split :=
  try intros [? [? [? ?]]];
  try intros [? [? ?]];
  try intros [? ?].

Ltac distinguish3 :=
  split; intros; unfold not;  intro_split; discriminate.

Ltac solve_collectAnnArgsTicks :=
  Tactics.program_simpl;
  try solve [distinguish3];
  try solve [repeat match goal with [ f : AnnExpr _ _ |- _ ] => destruct f end;
             Tactics.program_simpl;
             lia].

(* This function is needed to show the termination of collectAnnArgs, 
   collectAnnArgsTicks. *)
Fixpoint size_AnnExpr' {a}{b} (e: AnnExpr' a b) :=
  match e with 
  | AnnVar _ => 0
  | AnnLit _ => 0
  | AnnLam _ (_ , bdy) => S (size_AnnExpr' bdy)
  | AnnApp (_,e1) (_, e2) => S (size_AnnExpr' e1 + size_AnnExpr' e2)
  | AnnCase (_,scrut) bndr _ alts =>
    S (size_AnnExpr' scrut +
       List.fold_right plus 0
                          (List.map (fun p =>
                                       match p with
                                         | Mk_AnnAlt _ _ (_,e) => size_AnnExpr' e
                                    end)
                                    alts))
  | AnnLet (AnnNonRec v (_,rhs)) (_,body) => 
        S (size_AnnExpr' rhs + size_AnnExpr' body)
  | AnnLet (AnnRec pairs) (_,body) => 
        S (Lists.List.fold_right plus 0 
          (Lists.List.map (fun p => size_AnnExpr' (snd (snd p))) pairs) +
           size_AnnExpr' body)

  | AnnCast (_,e) _ => S (size_AnnExpr' e)
(*  | AnnTick _ (_,e) => S (size_AnnExpr' e) *)
  | AnnType _ => 0
  | AnnCoercion _ => 0 
  end.

(* ---------------------------------- *)

#[global] Instance Default__Expr {b} : HsToCoq.Err.Default (Expr b) :=
  HsToCoq.Err.Build_Default _ (Mk_Var HsToCoq.Err.default).

(* Default__Tickish removed: Tickish is now GHC.Types.Tickish.CoreTickish (axiomatized) *)

#[global] Instance Default_TaggedBndr {t}`{HsToCoq.Err.Default t} : HsToCoq.Err.Default (TaggedBndr t) :=
  HsToCoq.Err.Build_Default _ (TB HsToCoq.Err.default HsToCoq.Err.default).

#[global] Instance Default__AnnExpr' {a}{b} : HsToCoq.Err.Default (AnnExpr' a b) :=
  HsToCoq.Err.Build_Default _ (AnnVar HsToCoq.Err.default). 

#[global] Instance Default__AnnBind {a}{b} : HsToCoq.Err.Default (AnnBind a b) :=
  HsToCoq.Err.Build_Default _ (AnnRec HsToCoq.Err.default). 

#[global] Instance Default__Bind {b} : HsToCoq.Err.Default (Bind b) :=
  HsToCoq.Err.Build_Default _ (Rec HsToCoq.Err.default). 

(* Default__CoreVect removed: CoreVect doesn't exist in GHC 9.10 *)

(* Default__CoreRule and Default__RuleEnv injected by sed before record accessors *)


(* ---------------------------------- *)

(* collectBinders and collectNBinders — no longer auto-generated in GHC 9.10 *)

Definition collectBinders {b : Type} : Expr b -> (list b * Expr b)%type :=
  let fix go (bs : list b) (e : Expr b) : (list b * Expr b) :=
    match e with
    | Lam b body => go (cons b bs) body
    | _ => pair (GHC.List.reverse bs) e
    end in
  fun e => go nil e.

Definition collectNBinders {b : Type}
  : nat -> Expr b -> (list b * Expr b)%type :=
  fun orig_n orig_expr =>
    let fix go (n : nat) (bs : list b) (expr : Expr b) : (list b * Expr b) :=
      match n, bs, expr with
      | O, _, _ => pair (GHC.List.reverse bs) expr
      | S m, _, Lam b body => go m (cons b bs) body
      | _, _, _ => Panic.panicStr (GHC.Base.hs_string__ "collectNBinders") Panic.someSDoc
      end in
    go orig_n nil orig_expr.

Definition collectArgs {b : Type} : Expr b -> (Expr b * list (Expr b))%type :=
  let fix go (e : Expr b) (args : list (Expr b)) : (Expr b * list (Expr b)) :=
    match e with
    | App f a => go f (cons a args)
    | _ => pair e args
    end in
  fun e => go e nil.

(* See comments in CoreSyn/edits file. We can't use termination edits for collect. *)

Definition collectNAnnBndrs {bndr} {annot}`{HsToCoq.Err.Default annot}
    : nat -> AnnExpr bndr annot -> (list bndr * AnnExpr bndr annot)%type :=
          fun orig_n e =>
            let fix collect (arg_0__:nat) (arg_1__ : list bndr) (arg_2__:AnnExpr bndr annot) :=
                               match arg_0__, arg_1__, arg_2__ with
                               | O, bs, body =>
                                 pair (GHC.List.reverse bs) body 
                               | S m, bs, body =>
                                   match arg_0__, arg_1__, arg_2__ with
                                   | n, bs, pair _ (AnnLam b body) => collect m (cons b bs) body
                                   | _, _, _ =>
                                       Panic.panicStr (GHC.Base.hs_string__ "collectNBinders") Panic.someSDoc
                                   end
                               end in
            collect orig_n nil e.
(* DEMAND midamble file. Termination defs and tactics . *)

Require Import HsToCoq.Nat.
Require Import HsToCoq.Unpeel.
Require Import Lia.

Ltac solve_not_zero_N := match goal with
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] =>
    unfold GHC.Base.op_zeze__ in H;
    unfold GHC.Base.Eq_Char___ in H;
    simpl in H;
    apply N.eqb_neq in H end;
    zify;
    lia.
Ltac simpl_not_zero := match goal with
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] =>
  unfold GHC.Base.op_zeze__ in H;
    unfold Eq_nat in H;
    simpl in H;
  apply Nat.eqb_neq in H end.
Ltac solve_error_sub :=
  unfold error_sub;
  let Hltb := fresh in
  let HeqHltb := fresh in
  match goal with
    [ |- context[ Nat.ltb ?x (Pos.to_nat 1) ] ] =>
    remember (Nat.ltb x (Pos.to_nat 1)) as Hltb eqn:HeqHltb;
      destruct Hltb;
      symmetry in HeqHltb;
      try (rewrite Nat.ltb_lt in HeqHltb);
      try (rewrite Nat.ltb_ge in HeqHltb);
      try solve [zify; lia]
  end.

Ltac distinguish := split; intros; unfold not; intros [? ?]; discriminate.
Ltac solve_mkWorkerDemand := Tactics.program_simpl; simpl_not_zero; solve_error_sub.

Ltac solve_dmdTransform := Tactics.program_simpl; try solve_mkWorkerDemand; try distinguish.

(* GHC 9.10: StrictSig renamed to DmdSig *)
(* Unpeel_StrictSig removed — StrictSig no longer exists *)
(* Str_size/StrDmd_size/ArgStrDmd_size removed — Str/StrDmd types removed in GHC 9.10 *)

(* Converted value declarations: *)

#[local] Definition Functor__NormaliseStepResult_fmap
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> NormaliseStepResult a -> NormaliseStepResult b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, NS_Done => NS_Done
      | f, NS_Abort => NS_Abort
      | f, NS_Step a1 a2 a3 => NS_Step a1 a2 (f a3)
      end.

#[local] Definition Functor__NormaliseStepResult_op_zlzd__
   : forall {a : Type},
     forall {b : Type}, a -> NormaliseStepResult b -> NormaliseStepResult a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | z, NS_Done => NS_Done
      | z, NS_Abort => NS_Abort
      | z, NS_Step a1 a2 a3 => NS_Step a1 a2 z
      end.

#[global]
Program Instance Functor__NormaliseStepResult
   : GHC.Base.Functor NormaliseStepResult :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} =>
             Functor__NormaliseStepResult_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__NormaliseStepResult_op_zlzd__ |}.

Axiom dataConTag : DataCon -> HsSyn.ConTag.

#[local] Definition Uniquable__TyCon_getUnique : TyCon -> Unique.Unique :=
  fun tc => tyConUnique tc.

#[global]
Program Instance Uniquable__TyCon : Unique.Uniquable TyCon :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__TyCon_getUnique |}.

#[local] Definition Eq___TyCon_op_zeze__ : TyCon -> TyCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

#[local] Definition Eq___TyCon_op_zsze__ : TyCon -> TyCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

#[global]
Program Instance Eq___TyCon : GHC.Base.Eq_ TyCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TyCon_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TyCon_op_zsze__ |}.

#[local] Definition Ord__AltCon_compare : AltCon -> AltCon -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | DataAlt con1, DataAlt con2 =>
        GHC.Base.compare (dataConTag con1) (dataConTag con2)
    | DataAlt _, _ => Gt
    | _, DataAlt _ => Lt
    | LitAlt l1, LitAlt l2 => GHC.Base.compare l1 l2
    | LitAlt _, DEFAULT => Gt
    | DEFAULT, DEFAULT => Eq
    | DEFAULT, _ => Lt
    end.

#[local] Definition Ord__AltCon_op_zl__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base.== Lt.

#[local] Definition Ord__AltCon_op_zlze__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base./= Gt.

#[local] Definition Ord__AltCon_op_zg__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base.== Gt.

#[local] Definition Ord__AltCon_op_zgze__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base./= Lt.

#[local] Definition Ord__AltCon_max : AltCon -> AltCon -> AltCon :=
  fun x y => if Ord__AltCon_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__AltCon_min : AltCon -> AltCon -> AltCon :=
  fun x y => if Ord__AltCon_op_zlze__ x y : bool then x else y.

#[local] Definition Uniquable__DataCon_getUnique : DataCon -> Unique.Unique :=
  dcUnique.

#[global]
Program Instance Uniquable__DataCon : Unique.Uniquable DataCon :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__DataCon_getUnique |}.

#[local] Definition Eq___DataCon_op_zsze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

#[local] Definition Eq___DataCon_op_zeze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

#[global]
Program Instance Eq___DataCon : GHC.Base.Eq_ DataCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___DataCon_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___DataCon_op_zsze__ |}.

#[local] Definition Eq___AltCon_op_zeze__ : AltCon -> AltCon -> bool :=
  fun a b => match a, b with
    | DataAlt dc1, DataAlt dc2 => dc1 GHC.Base.== dc2
    | LitAlt l1, LitAlt l2 => l1 GHC.Base.== l2
    | DEFAULT, DEFAULT => true
    | _, _ => false
  end.

#[local] Definition Eq___AltCon_op_zsze__ : AltCon -> AltCon -> bool :=
  fun a b => negb (Eq___AltCon_op_zeze__ a b).

#[global]
Program Instance Eq___AltCon : GHC.Base.Eq_ AltCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___AltCon_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___AltCon_op_zsze__ |}.

#[global]
Program Instance Ord__AltCon : GHC.Base.Ord AltCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__AltCon_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__AltCon_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__AltCon_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__AltCon_op_zgze__ ;
           GHC.Base.compare__ := Ord__AltCon_compare ;
           GHC.Base.max__ := Ord__AltCon_max ;
           GHC.Base.min__ := Ord__AltCon_min |}.

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__IsOrphan' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__AltCon' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TaggedBndr' *)

#[local] Definition Eq___Class_op_zeze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.== classKey c2.

#[local] Definition Eq___Class_op_zsze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base./= classKey c2.

#[global]
Program Instance Eq___Class : GHC.Base.Eq_ Class :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Class_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Class_op_zsze__ |}.

#[local] Definition Uniquable__Class_getUnique : Class -> Unique.Unique :=
  fun c => classKey c.

#[global]
Program Instance Uniquable__Class : Unique.Uniquable Class :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__Class_getUnique |}.

#[local] Definition NamedThing__Class_getName : Class -> Name.Name :=
  fun clas => className clas.

#[local] Definition NamedThing__Class_getOccName : Class -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__Class_getName n).

#[global]
Program Instance NamedThing__Class : Name.NamedThing Class :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__Class_getName ;
           Name.getOccName__ := NamedThing__Class_getOccName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Class' *)

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `Core.Data__Class' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__NormaliseStepResult' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__LiftingContext' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__EqSpec' *)

#[local] Definition NamedThing__DataCon_getName : DataCon -> Name.Name :=
  dcName.

#[local] Definition NamedThing__DataCon_getOccName
   : DataCon -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__DataCon_getName n).

#[global]
Program Instance NamedThing__DataCon : Name.NamedThing DataCon :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__DataCon_getName ;
           Name.getOccName__ := NamedThing__DataCon_getOccName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__DataCon' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `Core.OutputableBndr__DataCon' *)

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `Core.Data__DataCon' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__HsSrcBang' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__HsImplBang' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__SrcStrictness' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__SrcUnpackedness' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__StrictnessMark' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__StrictnessMark' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__SrcStrictness' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__SrcUnpackedness' *)

#[local] Definition Uniquable__PatSyn_getUnique : PatSyn -> Unique.Unique :=
  psUnique.

#[global]
Program Instance Uniquable__PatSyn : Unique.Uniquable PatSyn :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__PatSyn_getUnique |}.

#[local] Definition Eq___PatSyn_op_zeze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base.==_ Unique.getUnique.

#[local] Definition Eq___PatSyn_op_zsze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base./=_ Unique.getUnique.

#[global]
Program Instance Eq___PatSyn : GHC.Base.Eq_ PatSyn :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___PatSyn_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___PatSyn_op_zsze__ |}.

Axiom patSynName : PatSyn -> Name.Name.

#[local] Definition NamedThing__PatSyn_getName : PatSyn -> Name.Name :=
  patSynName.

#[local] Definition NamedThing__PatSyn_getOccName : PatSyn -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__PatSyn_getName n).

#[global]
Program Instance NamedThing__PatSyn : Name.NamedThing PatSyn :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__PatSyn_getName ;
           Name.getOccName__ := NamedThing__PatSyn_getOccName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__PatSyn' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `Core.OutputableBndr__PatSyn' *)

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `Core.Data__PatSyn' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Type_' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyLit' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Coercion' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__CoSel' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__FunSel' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__CoSel' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Core.NFData__CoSel' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__MCoercion' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__UnivCoProvenance' *)

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `Core.Data__CoercionHole' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__CoercionHole' *)

(* Skipping instance `Core.Uniquable__CoercionHole' of class
   `Unique.Uniquable' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Scaled' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyConBndrVis' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__VarBndr__TyConBndrVis__11' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__TyConBndrVis' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__AlgTyConFlav' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__FamTyConFlav' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__PrimRep' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__PrimElemRep' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__PrimRep' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__PrimElemRep' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyCon' *)

#[local] Definition NamedThing__TyCon_getName : TyCon -> Name.Name :=
  tyConName.

#[local] Definition NamedThing__TyCon_getOccName : TyCon -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__TyCon_getName n).

#[global]
Program Instance NamedThing__TyCon : Name.NamedThing TyCon :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__TyCon_getName ;
           Name.getOccName__ := NamedThing__TyCon_getOccName |}.

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `Core.Data__TyCon' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__Injectivity' *)

(* Skipping instance `Core.Eq___SubDemand' of class `GHC.Base.Eq_' *)

(* Skipping instance `Core.Eq___DmdEnv' of class `GHC.Base.Eq_' *)

(* Skipping instance `Core.Eq___DmdType' of class `GHC.Base.Eq_' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__Card' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Card' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Demand' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__SubDemand' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Divergence' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__DmdEnv' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__DmdType' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__DmdSig' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TypeShape' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__Card' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__Demand' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__SubDemand' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__Divergence' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__DmdEnv' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__DmdType' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__DmdSig' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__RecSelParent' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__IdDetails' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__CafInfo' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TickBoxOp' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Var' *)

#[local] Definition NamedThing__Var_getName : Var -> Name.Name :=
  varName.

#[local] Definition NamedThing__Var_getOccName : Var -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__Var_getName n).

#[global]
Program Instance NamedThing__Var : Name.NamedThing Var :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__Var_getName ;
           Name.getOccName__ := NamedThing__Var_getOccName |}.

#[global] Definition varUnique : Var -> Unique.Unique :=
  fun var => realUnique var.

#[local] Definition Uniquable__Var_getUnique : Var -> Unique.Unique :=
  varUnique.

#[global]
Program Instance Uniquable__Var : Unique.Uniquable Var :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__Var_getUnique |}.

#[local] Definition Eq___Var_op_zeze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.== realUnique b.

#[local] Definition Eq___Var_op_zsze__ : Var -> Var -> bool :=
  fun x y => negb (Eq___Var_op_zeze__ x y).

#[global]
Program Instance Eq___Var : GHC.Base.Eq_ Var :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Var_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Var_op_zsze__ |}.

#[local] Definition Ord__Var_op_zl__ : Var -> Var -> bool :=
  fun a b => Unique.getKey (realUnique a) GHC.Base.< Unique.getKey (realUnique b).

#[local] Definition Ord__Var_op_zlze__ : Var -> Var -> bool :=
  fun a b =>
    Unique.getKey (realUnique a) GHC.Base.<= Unique.getKey (realUnique b).

#[local] Definition Ord__Var_op_zg__ : Var -> Var -> bool :=
  fun a b => Unique.getKey (realUnique a) GHC.Base.> Unique.getKey (realUnique b).

#[local] Definition Ord__Var_op_zgze__ : Var -> Var -> bool :=
  fun a b =>
    Unique.getKey (realUnique a) GHC.Base.>= Unique.getKey (realUnique b).

#[global] Definition nonDetCmpVar : Var -> Var -> comparison :=
  fun a b => Unique.nonDetCmpUnique (varUnique a) (varUnique b).

#[local] Definition Ord__Var_compare : Var -> Var -> comparison :=
  fun a b => nonDetCmpVar a b.

#[local] Definition Ord__Var_max : Var -> Var -> Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__Var_min : Var -> Var -> Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__Var : GHC.Base.Ord Var :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Var_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Var_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Var_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Var_op_zgze__ ;
           GHC.Base.compare__ := Ord__Var_compare ;
           GHC.Base.max__ := Ord__Var_max ;
           GHC.Base.min__ := Ord__Var_min |}.

(* Skipping all instances of class `GHC.Internal.Data.Data.Data', including
   `Core.Data__Var' *)

#[local] Definition HasOccName__Var_occName : Var -> OccName.OccName :=
  Name.nameOccName GHC.Base.∘ varName.

#[global]
Program Instance HasOccName__Var : OccName.HasOccName Var :=
  fun _ k__ => k__ {| OccName.occName__ := HasOccName__Var_occName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__ForAllTyFlag' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__Specificity' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__ForAllTyFlag' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Core.NFData__Specificity' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Core.NFData__ForAllTyFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__FunTyFlag' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__FunTyFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__VarBndr__ForAllTyFlag__11' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__VarBndr__Specificity__11' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__VarBndr' *)

#[local] Definition NamedThing__VarBndr_getName {inst_tv : Type} {inst_flag
   : Type} `{Name.NamedThing inst_tv}
   : VarBndr inst_tv inst_flag -> Name.Name :=
  fun '(Bndr tv _) => Name.getName tv.

#[local] Definition NamedThing__VarBndr_getOccName {inst_tv : Type} {inst_flag
   : Type} `{Name.NamedThing inst_tv}
   : VarBndr inst_tv inst_flag -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__VarBndr_getName n).

#[global]
Program Instance NamedThing__VarBndr {tv : Type} {flag : Type} `{Name.NamedThing
  tv}
   : Name.NamedThing (VarBndr tv flag) :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__VarBndr_getName ;
           Name.getOccName__ := NamedThing__VarBndr_getOccName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__PiTyBinder' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__InScopeSet' *)

Axiom classMinimalDef : Class -> ClassMinimalDef.

Axiom mkClass : Name.Name ->
                list TyVar ->
                list (FunDep TyVar) ->
                list PredType ->
                list Id ->
                list ClassATItem -> list ClassOpItem -> ClassMinimalDef -> TyCon -> Class.

Axiom mkAbstractClass : Name.Name ->
                        list TyVar -> list (FunDep TyVar) -> TyCon -> Class.

Axiom classArity : Class -> BasicTypes.Arity.

Axiom classAllSelIds : Class -> list Id.

Axiom classSCSelIds : Class -> list Id.

(* Skipping definition `Core.classSCSelId' *)

Axiom classMethods : Class -> list Id.

Axiom classOpItems : Class -> list ClassOpItem.

Axiom classATs : Class -> list TyCon.

Axiom classATItems : Class -> list ClassATItem.

Axiom classSCTheta : Class -> list PredType.

Axiom classHasSCs : Class -> bool.

Axiom classTvsFds : Class -> (list TyVar * list (FunDep TyVar))%type.

Axiom classHasFds : Class -> bool.

Axiom classBigSig : Class ->
                    (list TyVar * list PredType * list Id * list ClassOpItem)%type.

Axiom classExtraBigSig : Class ->
                         (list TyVar * list (FunDep TyVar) * list PredType * list Id * list ClassATItem *
                          list ClassOpItem)%type.

Axiom isAbstractClass : Class -> bool.

(* Skipping definition `Core.pprDefMethInfo' *)

(* Skipping definition `Core.pprFundeps' *)

(* Skipping definition `Core.pprFunDep' *)

Axiom coVarName : CoVar -> Name.Name.

Axiom setCoVarUnique : CoVar -> Unique.Unique -> CoVar.

Axiom setCoVarName : CoVar -> Name.Name -> CoVar.

Axiom etaExpandCoAxBranch : CoAxBranch ->
                            (list TyVar * list Type_ * Type_)%type.

Axiom pprCoAxiom : forall {br : BranchFlag}, CoAxiom br -> GHC.Base.String.

Axiom pprCoAxBranchUser : TyCon -> CoAxBranch -> GHC.Base.String.

Axiom pprCoAxBranchLHS : TyCon -> CoAxBranch -> GHC.Base.String.

Axiom pprCoAxBranch : TyCon -> CoAxBranch -> GHC.Base.String.

Axiom ppr_co_ax_branch : (TidyEnv -> Type_ -> GHC.Base.String) ->
                         TyCon -> CoAxBranch -> GHC.Base.String.

Axiom tidyCoAxBndrsForUser : TidyEnv -> list Var -> (TidyEnv * list Var)%type.

Axiom coToMCo : Coercion -> MCoercion.

Axiom checkReflexiveMCo : MCoercion -> MCoercion.

Axiom isGReflMCo : MCoercion -> bool.

Axiom mkGReflCo : HsSyn.Role -> Type_ -> MCoercionN -> Coercion.

Axiom mkTransMCo : MCoercion -> MCoercion -> MCoercion.

Axiom mkTransMCoL : MCoercion -> Coercion -> MCoercion.

Axiom mkTransMCoR : Coercion -> MCoercion -> MCoercion.

Axiom mkSymMCo : MCoercion -> MCoercion.

Axiom mkCastTyMCo : Type_ -> MCoercion -> Type_.

Axiom mkPiMCos : list Var -> MCoercion -> MCoercion.

Axiom mkFunResMCo : Id -> MCoercionR -> MCoercionR.

Axiom mkGReflLeftMCo : HsSyn.Role -> Type_ -> MCoercionN -> Coercion.

Axiom mkGReflRightMCo : HsSyn.Role -> Type_ -> MCoercionN -> Coercion.

Axiom mkCoherenceRightMCo : HsSyn.Role ->
                            Type_ -> MCoercionN -> Coercion -> Coercion.

Axiom isReflMCo : MCoercion -> bool.

Axiom decomposeCo : BasicTypes.Arity ->
                    Coercion -> GHC.Data.List.Infinite.Infinite HsSyn.Role -> list Coercion.

Axiom decomposeFunCo : forall `{Util.HasDebugCallStack},
                       Coercion -> (CoercionN * Coercion * Coercion)%type.

Axiom decomposePiCos : forall `{Util.HasDebugCallStack},
                       CoercionN -> Pair.Pair Type_ -> list Type_ -> (list CoercionN * CoercionN)%type.

Axiom getCoVar_maybe : Coercion -> option CoVar.

Axiom multToCo : Mult -> Coercion.

Axiom splitAppCo_maybe : Coercion -> option (Coercion * Coercion)%type.

Axiom splitFunCo_maybe : Coercion -> option (Coercion * Coercion)%type.

Axiom splitForAllCo_maybe : Coercion ->
                            option (TyCoVar * ForAllTyFlag * ForAllTyFlag * Coercion * Coercion)%type.

Axiom splitForAllCo_ty_maybe : Coercion ->
                               option (TyVar * ForAllTyFlag * ForAllTyFlag * Coercion * Coercion)%type.

Axiom splitForAllCo_co_maybe : Coercion ->
                               option (CoVar * ForAllTyFlag * ForAllTyFlag * Coercion * Coercion)%type.

Axiom coVarLType : forall `{Util.HasDebugCallStack}, CoVar -> Type_.

Axiom coVarRType : forall `{Util.HasDebugCallStack}, CoVar -> Type_.

Axiom coVarTypes : forall `{Util.HasDebugCallStack}, CoVar -> Pair.Pair Type_.

Axiom coVarKindsTypesRole : forall `{Util.HasDebugCallStack},
                            CoVar -> (Kind * Kind * Type_ * Type_ * HsSyn.Role)%type.

Axiom coVarKind : CoVar -> Type_.

Axiom coVarRole : CoVar -> HsSyn.Role.

Axiom eqTyConRole : TyCon -> HsSyn.Role.

Axiom mkRuntimeRepCo : forall `{Util.HasDebugCallStack}, Coercion -> Coercion.

Axiom isReflCoVar_maybe : Var -> option Coercion.

Axiom isGReflCo : Coercion -> bool.

Axiom isReflCo : Coercion -> bool.

Axiom isGReflCo_maybe : Coercion -> option (Type_ * HsSyn.Role)%type.

Axiom isReflCo_maybe : Coercion -> option (Type_ * HsSyn.Role)%type.

Axiom isReflexiveCo : Coercion -> bool.

Axiom isReflexiveCo_maybe : Coercion -> option (Type_ * HsSyn.Role)%type.

Axiom mkReflCo : HsSyn.Role -> Type_ -> Coercion.

Axiom mkRepReflCo : Type_ -> Coercion.

Axiom mkNomReflCo : Type_ -> Coercion.

Axiom mkTyConAppCo : forall `{Util.HasDebugCallStack},
                     HsSyn.Role -> TyCon -> list Coercion -> Coercion.

Axiom mkFunCoNoFTF : forall `{Util.HasDebugCallStack},
                     HsSyn.Role -> CoercionN -> Coercion -> Coercion -> Coercion.

Axiom mkFunCo : HsSyn.Role ->
                FunTyFlag -> CoercionN -> Coercion -> Coercion -> Coercion.

Axiom mkNakedFunCo : HsSyn.Role ->
                     FunTyFlag -> CoercionN -> Coercion -> Coercion -> Coercion.

Axiom mkFunCo2 : HsSyn.Role ->
                 FunTyFlag -> FunTyFlag -> CoercionN -> Coercion -> Coercion -> Coercion.

Axiom mkAppCo : Coercion -> Coercion -> Coercion.

Axiom mkAppCos : Coercion -> list Coercion -> Coercion.

Axiom mkForAllCo : forall `{Util.HasDebugCallStack},
                   TyCoVar -> ForAllTyFlag -> ForAllTyFlag -> CoercionN -> Coercion -> Coercion.

Axiom mkHomoForAllCos : list ForAllTyBinder -> Coercion -> Coercion.

Axiom mkForAllCo_NoRefl : TyCoVar ->
                          ForAllTyFlag -> ForAllTyFlag -> CoercionN -> Coercion -> Coercion.

Axiom assertGoodForAllCo : forall {a},
                           forall `{Util.HasDebugCallStack},
                           TyCoVar -> ForAllTyFlag -> ForAllTyFlag -> CoercionN -> Coercion -> a -> a.

Axiom mkNakedForAllCo : TyVar ->
                        ForAllTyFlag -> ForAllTyFlag -> CoercionN -> Coercion -> Coercion.

(* Skipping definition `Core.mkCoVarCo' *)

(* Skipping definition `Core.mkCoVarCos' *)

Axiom mkAxInstCo : forall {br : BranchFlag},
                   HsSyn.Role ->
                   CoAxiom br -> BranchIndex -> list Type_ -> list Coercion -> Coercion.

Axiom mkAxiomInstCo : CoAxiom Branched ->
                      BranchIndex -> list Coercion -> Coercion.

Axiom mkUnbranchedAxInstCo : HsSyn.Role ->
                             CoAxiom Unbranched -> list Type_ -> list Coercion -> Coercion.

Axiom mkAxInstRHS : forall {br : BranchFlag},
                    CoAxiom br -> BranchIndex -> list Type_ -> list Coercion -> Type_.

Axiom mkUnbranchedAxInstRHS : CoAxiom Unbranched ->
                              list Type_ -> list Coercion -> Type_.

Axiom mkAxInstLHS : forall {br : BranchFlag},
                    CoAxiom br -> BranchIndex -> list Type_ -> list Coercion -> Type_.

Axiom mkUnbranchedAxInstLHS : CoAxiom Unbranched ->
                              list Type_ -> list Coercion -> Type_.

Axiom mkHoleCo : CoercionHole -> Coercion.

Axiom mkUnivCo : UnivCoProvenance -> HsSyn.Role -> Type_ -> Type_ -> Coercion.

Axiom mkSymCo : Coercion -> Coercion.

Axiom mkTransCo : Coercion -> Coercion -> Coercion.

Axiom mkSelCo : forall `{Util.HasDebugCallStack}, CoSel -> Coercion -> Coercion.

Axiom mkSelCo_maybe : forall `{Util.HasDebugCallStack},
                      CoSel -> Coercion -> option Coercion.

Axiom getNthFun : forall {a : Type}, FunSel -> a -> a -> a -> a.

Axiom mkLRCo : BasicTypes.LeftOrRight -> Coercion -> Coercion.

Axiom mkInstCo : Coercion -> CoercionN -> Coercion.

Axiom mkGReflRightCo : HsSyn.Role -> Type_ -> CoercionN -> Coercion.

Axiom mkGReflLeftCo : HsSyn.Role -> Type_ -> CoercionN -> Coercion.

Axiom mkCoherenceLeftCo : HsSyn.Role ->
                          Type_ -> CoercionN -> Coercion -> Coercion.

Axiom mkCoherenceRightCo : HsSyn.Role ->
                           Type_ -> CoercionN -> Coercion -> Coercion.

Axiom mkKindCo : Coercion -> Coercion.

Axiom mkSubCo : forall `{Util.HasDebugCallStack}, Coercion -> Coercion.

Axiom downgradeRole_maybe : HsSyn.Role ->
                            HsSyn.Role -> Coercion -> option Coercion.

Axiom downgradeRole : HsSyn.Role -> HsSyn.Role -> Coercion -> Coercion.

Axiom mkAxiomRuleCo : CoAxiomRule -> list Coercion -> Coercion.

Axiom mkProofIrrelCo : HsSyn.Role ->
                       CoercionN -> Coercion -> Coercion -> Coercion.

Axiom setNominalRole_maybe : HsSyn.Role -> Coercion -> option CoercionN.

Axiom mkPhantomCo : Coercion -> Type_ -> Type_ -> Coercion.

Axiom toPhantomCo : Coercion -> Coercion.

Axiom applyRoles : TyCon -> list Coercion -> list Coercion.

Axiom tyConRolesX : HsSyn.Role ->
                    TyCon -> GHC.Data.List.Infinite.Infinite HsSyn.Role.

Axiom tyConRoleListX : HsSyn.Role -> TyCon -> list HsSyn.Role.

Axiom tyConRolesRepresentational : TyCon ->
                                   GHC.Data.List.Infinite.Infinite HsSyn.Role.

Axiom tyConRoleListRepresentational : TyCon -> list HsSyn.Role.

Axiom tyConRole : HsSyn.Role -> TyCon -> nat -> HsSyn.Role.

Axiom funRole : HsSyn.Role -> FunSel -> HsSyn.Role.

Axiom funRoleRepresentational : FunSel -> HsSyn.Role.

Axiom ltRole : HsSyn.Role -> HsSyn.Role -> bool.

Axiom promoteCoercion : forall `{Util.HasDebugCallStack}, Coercion -> CoercionN.

Axiom instCoercion : Pair.Pair Type_ ->
                     CoercionN -> Coercion -> option CoercionN.

Axiom instCoercions : CoercionN -> list Coercion -> option CoercionN.

Axiom castCoercionKind2 : Coercion ->
                          HsSyn.Role -> Type_ -> Type_ -> CoercionN -> CoercionN -> Coercion.

Axiom castCoercionKind1 : Coercion ->
                          HsSyn.Role -> Type_ -> Type_ -> CoercionN -> Coercion.

Axiom castCoercionKind : Coercion -> CoercionN -> CoercionN -> Coercion.

Axiom mkPiCos : HsSyn.Role -> list Var -> Coercion -> Coercion.

Axiom mkPiCo : HsSyn.Role -> Var -> Coercion -> Coercion.

Axiom mkFunResCo : HsSyn.Role -> Id -> Coercion -> Coercion.

Axiom mkCoCast : Coercion -> CoercionR -> Coercion.

Axiom instNewTyCon_maybe : TyCon ->
                           list Type_ -> option (Type_ * Coercion)%type.

Axiom composeSteppers : forall {ev : Type},
                        NormaliseStepper ev -> NormaliseStepper ev -> NormaliseStepper ev.

Axiom unwrapNewTypeStepper : NormaliseStepper Coercion.

Axiom topNormaliseTypeX : forall {ev : Type},
                          NormaliseStepper ev -> (ev -> ev -> ev) -> Type_ -> option (ev * Type_)%type.

Axiom topNormaliseNewType_maybe : Type_ -> option (Coercion * Type_)%type.

Axiom eqCoercion : Coercion -> Coercion -> bool.

Axiom eqCoercionX : RnEnv2 -> Coercion -> Coercion -> bool.

Axiom liftCoSubstWithEx : HsSyn.Role ->
                          list TyVar ->
                          list Coercion ->
                          list TyCoVar -> list Type_ -> ((Type_ -> Coercion) * list Type_)%type.

Axiom liftCoSubstWith : HsSyn.Role ->
                        list TyCoVar -> list Coercion -> Type_ -> Coercion.

Axiom liftCoSubst : forall `{Util.HasDebugCallStack},
                    HsSyn.Role -> LiftingContext -> Type_ -> Coercion.

Axiom emptyLiftingContext : InScopeSet -> LiftingContext.

Axiom mkLiftingContext : list (TyCoVar * Coercion)%type -> LiftingContext.

Axiom mkSubstLiftingContext : GHC.Core.TyCo.Subst.Subst -> LiftingContext.

Axiom extendLiftingContext : LiftingContext ->
                             TyCoVar -> Coercion -> LiftingContext.

Axiom extendLiftingContextCvSubst : LiftingContext ->
                                    CoVar -> Coercion -> LiftingContext.

Axiom extendLiftingContextAndInScope : LiftingContext ->
                                       TyCoVar -> Coercion -> LiftingContext.

Axiom extendLiftingContextEx : LiftingContext ->
                               list (TyCoVar * Type_)%type -> LiftingContext.

Axiom zapLiftingContext : LiftingContext -> LiftingContext.

Axiom substForAllCoBndrUsingLC : bool ->
                                 (Coercion -> Coercion) ->
                                 LiftingContext ->
                                 TyCoVar -> Coercion -> (LiftingContext * TyCoVar * Coercion)%type.

Axiom ty_co_subst : LiftingContext -> HsSyn.Role -> Type_ -> Coercion.

Axiom liftCoSubstTyVar : LiftingContext ->
                         HsSyn.Role -> TyVar -> option Coercion.

Axiom liftCoSubstVarBndr : LiftingContext ->
                           TyCoVar -> (LiftingContext * TyCoVar * Coercion)%type.

Axiom liftCoSubstVarBndrUsing : forall {r : Type},
                                (r -> CoercionN) ->
                                (LiftingContext -> Type_ -> r) ->
                                LiftingContext -> TyCoVar -> (LiftingContext * TyCoVar * r)%type.

Axiom liftCoSubstTyVarBndrUsing : forall {r},
                                  (r -> CoercionN) ->
                                  (LiftingContext -> Type_ -> r) ->
                                  LiftingContext -> TyVar -> (LiftingContext * TyVar * r)%type.

Axiom liftCoSubstCoVarBndrUsing : forall {r},
                                  (r -> CoercionN) ->
                                  (LiftingContext -> Type_ -> r) ->
                                  LiftingContext -> CoVar -> (LiftingContext * CoVar * r)%type.

Axiom isMappedByLC : TyCoVar -> LiftingContext -> bool.

Axiom substLeftCo : LiftingContext -> Coercion -> Coercion.

Axiom substRightCo : LiftingContext -> Coercion -> Coercion.

Axiom swapLiftCoEnv : LiftCoEnv -> LiftCoEnv.

Axiom lcSubstLeft : LiftingContext -> GHC.Core.TyCo.Subst.Subst.

Axiom lcSubstRight : LiftingContext -> GHC.Core.TyCo.Subst.Subst.

Axiom liftEnvSubstLeft : GHC.Core.TyCo.Subst.Subst ->
                         LiftCoEnv -> GHC.Core.TyCo.Subst.Subst.

Axiom liftEnvSubstRight : GHC.Core.TyCo.Subst.Subst ->
                          LiftCoEnv -> GHC.Core.TyCo.Subst.Subst.

Axiom liftEnvSubst : (forall {a}, Pair.Pair a -> a) ->
                     GHC.Core.TyCo.Subst.Subst -> LiftCoEnv -> GHC.Core.TyCo.Subst.Subst.

Axiom lcLookupCoVar : LiftingContext -> CoVar -> option Coercion.

Axiom lcInScopeSet : LiftingContext -> InScopeSet.

Axiom seqMCo : MCoercion -> unit.

Axiom seqCo : Coercion -> unit.

Axiom seqProv : UnivCoProvenance -> unit.

Axiom seqCos : list Coercion -> unit.

Axiom coercionKinds : list Coercion -> Pair.Pair (list Type_).

Axiom coercionKindRole : Coercion -> (Pair.Pair Type_ * HsSyn.Role)%type.

Axiom coercionType : Coercion -> Type_.

Axiom coercionKind : Coercion -> Pair.Pair Type_.

Axiom coercionLKind : Coercion -> Type_.

Axiom getNthFromType : forall `{Util.HasDebugCallStack},
                       CoSel -> Type_ -> Type_.

Axiom coercionRKind : Coercion -> Type_.

Axiom coercionRole : Coercion -> HsSyn.Role.

Axiom mkCoercionType : HsSyn.Role -> Type_ -> Type_ -> Type_.

Axiom mkPrimEqPred : Type_ -> Type_ -> Type_.

Axiom mkReprPrimEqPred : Type_ -> Type_ -> Type_.

Axiom mkPrimEqPredRole : HsSyn.Role -> Type_ -> Type_ -> PredType.

Axiom mkNomPrimEqPred : Kind -> Type_ -> Type_ -> Type_.

Axiom buildCoercion : Type_ -> Type_ -> CoercionN.

Axiom hasCoercionHoleTy : Type_ -> bool.

Axiom hasCoercionHoleCo : Coercion -> bool.

Axiom hasThisCoercionHoleTy : Type_ -> CoercionHole -> bool.

Axiom setCoHoleType : CoercionHole -> Type_ -> CoercionHole.

Axiom mkEqSpec : TyVar -> Type_ -> EqSpec.

Axiom eqSpecTyVar : EqSpec -> TyVar.

Axiom eqSpecType : EqSpec -> Type_.

Axiom eqSpecPair : EqSpec -> (TyVar * Type_)%type.

Axiom eqSpecPreds : list EqSpec -> ThetaType.

Axiom eqHsBang : HsImplBang -> HsImplBang -> bool.

Axiom isBanged : HsImplBang -> bool.

Axiom isSrcStrict : HsSyn.SrcStrictness -> bool.

Axiom isSrcUnpacked : HsSyn.SrcUnpackedness -> bool.

Axiom isMarkedStrict : StrictnessMark -> bool.

Axiom cbvFromStrictMark : StrictnessMark -> BasicTypes.CbvMark.

Axiom mkDataCon : Name.Name ->
                  bool ->
                  TyConRepName ->
                  list HsSrcBang ->
                  list FieldLabel.FieldLabel ->
                  list TyVar ->
                  list TyCoVar ->
                  TcType.ConcreteTyVars ->
                  list InvisTVBinder ->
                  list EqSpec ->
                  KnotTied ThetaType ->
                  list (KnotTied (Scaled Type_)) ->
                  KnotTied Type_ ->
                  PromDataConInfo ->
                  KnotTied TyCon -> HsSyn.ConTag -> ThetaType -> Id -> DataConRep -> DataCon.

(* Skipping definition `Core.freshNames' *)

Axiom dataConName : DataCon -> Name.Name.

Axiom dataConTagZ : DataCon -> BasicTypes.ConTagZ.

Axiom dataConTyCon : DataCon -> TyCon.

Axiom dataConOrigTyCon : DataCon -> TyCon.

Axiom dataConRepType : DataCon -> Type_.

Axiom dataConIsInfix : DataCon -> bool.

Axiom dataConUnivTyVars : DataCon -> list TyVar.

Axiom dataConExTyCoVars : DataCon -> list TyCoVar.

Axiom dataConUnivAndExTyCoVars : DataCon -> list TyCoVar.

Axiom dataConConcreteTyVars : DataCon -> TcType.ConcreteTyVars.

Axiom dataConUserTyVars : DataCon -> list TyVar.

Axiom dataConUserTyVarBinders : DataCon -> list InvisTVBinder.

Axiom dataConKindEqSpec : DataCon -> list EqSpec.

Axiom dataConTheta : DataCon -> ThetaType.

Axiom dataConWorkId : DataCon -> Id.

Axiom dataConWrapId_maybe : DataCon -> option Id.

Axiom dataConWrapId : DataCon -> Id.

Axiom dataConImplicitTyThings : DataCon -> list GHC.Types.TyThing.TyThing.

Axiom dataConFieldLabels : DataCon -> list FieldLabel.FieldLabel.

Axiom dataConFieldType : DataCon -> HsSyn.FieldLabelString -> Type_.

Axiom dataConFieldType_maybe : DataCon ->
                               HsSyn.FieldLabelString -> option (FieldLabel.FieldLabel * Type_)%type.

Axiom dataConSrcBangs : DataCon -> list HsSrcBang.

Axiom dataConSourceArity : DataCon -> BasicTypes.Arity.

Axiom dataConRepArity : DataCon -> BasicTypes.Arity.

Axiom isNullarySrcDataCon : DataCon -> bool.

Axiom isNullaryRepDataCon : DataCon -> bool.

Axiom dataConRepStrictness : DataCon -> list StrictnessMark.

Axiom dataConImplBangs : DataCon -> list HsImplBang.

Axiom dataConBoxer : DataCon -> option DataConBoxer.

Axiom dataConInstSig : DataCon ->
                       list Type_ -> (list TyCoVar * ThetaType * list Type_)%type.

Axiom dataConFullSig : DataCon ->
                       (list TyVar * list TyCoVar * list EqSpec * ThetaType * list (Scaled Type_) *
                        Type_)%type.

Axiom dataConOrigResTy : DataCon -> Type_.

Axiom dataConStupidTheta : DataCon -> ThetaType.

Axiom dataConWrapperType : DataCon -> Type_.

Axiom dataConNonlinearType : DataCon -> Type_.

Axiom dataConDisplayType : bool -> DataCon -> Type_.

Axiom dataConInstArgTys : DataCon -> list Type_ -> list (Scaled Type_).

Axiom dataConInstOrigArgTys : DataCon -> list Type_ -> list (Scaled Type_).

Axiom dataConInstUnivs : DataCon -> list Type_ -> list Type_.

Axiom dataConOrigArgTys : DataCon -> list (Scaled Type_).

Axiom dataConOtherTheta : DataCon -> ThetaType.

Axiom dataConRepArgTys : DataCon -> list (Scaled Type_).

(* Skipping definition `Core.dataConIdentity' *)

Axiom isTupleDataCon : DataCon -> bool.

Axiom isBoxedTupleDataCon : DataCon -> bool.

Axiom isUnboxedTupleDataCon : DataCon -> bool.

Axiom isUnboxedSumDataCon : DataCon -> bool.

Axiom isVanillaDataCon : DataCon -> bool.

Axiom isNewDataCon : DataCon -> bool.

Axiom isTypeDataCon : DataCon -> bool.

Axiom isCovertGadtDataCon : DataCon -> bool.

Axiom specialPromotedDc : DataCon -> bool.

Axiom classDataCon : Class -> DataCon.

Axiom dataConCannotMatch : list Type_ -> DataCon -> bool.

Axiom dataConResRepTyArgs : DataCon -> list Type_.

Axiom checkDataConTyVars : DataCon -> bool.

Axiom dataConUserTyVarsNeedWrapper : DataCon -> bool.

Axiom promoteDataCon : DataCon -> TyCon.

Axiom splitDataProductType_maybe : Type_ ->
                                   option (TyCon * list Type_ * DataCon * list (Scaled Type_))%type.

Axiom mkPatSyn : Name.Name ->
                 bool ->
                 (list InvisTVBinder * ThetaType)%type ->
                 (list InvisTVBinder * ThetaType)%type ->
                 list FRRType ->
                 Type_ -> PatSynMatcher -> PatSynBuilder -> list FieldLabel.FieldLabel -> PatSyn.

Axiom patSynIsInfix : PatSyn -> bool.

Axiom patSynArity : PatSyn -> BasicTypes.Arity.

Axiom isVanillaPatSyn : PatSyn -> bool.

Axiom patSynArgs : PatSyn -> list Type_.

Axiom patSynFieldLabels : PatSyn -> list FieldLabel.FieldLabel.

Axiom patSynFieldType : PatSyn -> HsSyn.FieldLabelString -> Type_.

Axiom patSynUnivTyVarBinders : PatSyn -> list InvisTVBinder.

Axiom patSynExTyVars : PatSyn -> list TyVar.

Axiom patSynExTyVarBinders : PatSyn -> list InvisTVBinder.

Axiom patSynSigBndr : PatSyn ->
                      (list InvisTVBinder * ThetaType * list InvisTVBinder * ThetaType *
                       list (Scaled Type_) *
                       Type_)%type.

Axiom patSynSig : PatSyn ->
                  (list TyVar * ThetaType * list TyVar * ThetaType * list (Scaled Type_) *
                   Type_)%type.

Axiom patSynMatcher : PatSyn -> PatSynMatcher.

Axiom patSynBuilder : PatSyn -> PatSynBuilder.

Axiom patSynResultType : PatSyn -> Type_.

Axiom patSynInstArgTys : PatSyn -> list Type_ -> list Type_.

Axiom patSynInstResTy : PatSyn -> list Type_ -> Type_.

(* Skipping definition `Core.pprPatSynType' *)

Axiom nonDetCmpTyLit : TyLit -> TyLit -> comparison.

Axiom cmpTyLit : TyLit -> TyLit -> comparison.

Axiom cmpTyLitWith : forall {r},
                     forall `{GHC.Base.Ord r},
                     (FastString.FastString -> r) -> TyLit -> TyLit -> comparison.

(* Skipping definition `Core.mkTyVarTy' *)

(* Skipping definition `Core.mkTyVarTys' *)

Axiom mkTyCoVarTy : TyCoVar -> Type_.

Axiom mkTyCoVarTys : list TyCoVar -> list Type_.

Axiom mkNakedFunTy : FunTyFlag -> Kind -> Kind -> Kind.

Axiom mkFunTy : forall `{Util.HasDebugCallStack},
                FunTyFlag -> Mult -> Type_ -> Type_ -> Type_.

Axiom mkInvisFunTy : forall `{Util.HasDebugCallStack}, Type_ -> Type_ -> Type_.

Axiom mkInvisFunTys : forall `{Util.HasDebugCallStack},
                      list Type_ -> Type_ -> Type_.

Axiom mkVisFunTy : forall `{Util.HasDebugCallStack},
                   Mult -> Type_ -> Type_ -> Type_.

Axiom mkVisFunTyMany : forall `{Util.HasDebugCallStack},
                       Type_ -> Type_ -> Type_.

Axiom mkVisFunTysMany : list Type_ -> Type_ -> Type_.

Axiom mkScaledFunTy : forall `{Util.HasDebugCallStack},
                      FunTyFlag -> Scaled Type_ -> Type_ -> Type_.

Axiom mkScaledFunTys : forall `{Util.HasDebugCallStack},
                       list (Scaled Type_) -> Type_ -> Type_.

Axiom mkForAllTy : ForAllTyBinder -> Type_ -> Type_.

Axiom mkForAllTys : list ForAllTyBinder -> Type_ -> Type_.

Axiom mkInvisForAllTys : list InvisTVBinder -> Type_ -> Type_.

Axiom mkPiTy : forall `{Util.HasDebugCallStack}, PiTyBinder -> Type_ -> Type_.

Axiom mkPiTys : forall `{Util.HasDebugCallStack},
                list PiTyBinder -> Type_ -> Type_.

Axiom mkNakedTyConTy : TyCon -> Type_.

Axiom tcMkVisFunTy : Mult -> Type_ -> Type_ -> Type_.

Axiom tcMkInvisFunTy : BasicTypes.TypeOrConstraint -> Type_ -> Type_ -> Type_.

Axiom tcMkScaledFunTys : list (Scaled Type_) -> Type_ -> Type_.

Axiom tcMkScaledFunTy : Scaled Type_ -> Type_ -> Type_.

Axiom coHoleCoVar : CoercionHole -> CoVar.

Axiom isHeteroKindCoHole : CoercionHole -> bool.

Axiom setCoHoleCoVar : CoercionHole -> CoVar -> CoercionHole.

Axiom foldTyCo : forall {a : Type},
                 forall {env : Type},
                 forall `{GHC.Base.Monoid a},
                 TyCoFolder env a ->
                 env ->
                 ((Type_ -> a) * (list Type_ -> a) * (Coercion -> a) *
                  (list Coercion -> a))%type.

Axiom noView : Type_ -> option Type_.

Axiom typeSize : Type_ -> nat.

Axiom typesSize : list Type_ -> nat.

Axiom coercionSize : Coercion -> nat.

Axiom provSize : UnivCoProvenance -> nat.

Axiom scaledMult : forall {a : Type}, Scaled a -> Mult.

Axiom scaledThing : forall {a : Type}, Scaled a -> a.

Axiom mapScaledType : (Type_ -> Type_) -> Scaled Type_ -> Scaled Type_.

Axiom mkAnonTyConBinder : TyVar -> TyConBinder.

Axiom mkAnonTyConBinders : list TyVar -> list TyConBinder.

Axiom mkNamedTyConBinder : ForAllTyFlag -> TyVar -> TyConBinder.

Axiom mkNamedTyConBinders : ForAllTyFlag -> list TyVar -> list TyConBinder.

Axiom mkRequiredTyConBinder : TyCoVarSet -> TyVar -> TyConBinder.

Axiom tyConBinderForAllTyFlag : TyConBinder -> ForAllTyFlag.

Axiom tyConBndrVisForAllTyFlag : TyConBndrVis -> ForAllTyFlag.

Axiom isNamedTyConBinder : TyConBinder -> bool.

Axiom isVisibleTyConBinder : forall {tv : Type},
                             VarBndr tv TyConBndrVis -> bool.

Axiom isVisibleTcbVis : TyConBndrVis -> bool.

Axiom isInvisSpecTcbVis : TyConBndrVis -> bool.

Axiom isInvisibleTyConBinder : forall {tv : Type},
                               VarBndr tv TyConBndrVis -> bool.

Axiom mkTyConKind : list TyConBinder -> Kind -> Kind.

Axiom mkTyConTy : TyCon -> Type_.

Axiom tyConInvisTVBinders : list TyConBinder -> list InvisTVBinder.

Axiom tyConVisibleTyVars : TyCon -> list TyVar.

Axiom mkSumTyConRhs : list DataCon -> AlgTyConRhs.

Axiom mkLevPolyDataTyConRhs : bool -> bool -> list DataCon -> AlgTyConRhs.

Axiom mkDataTyConRhs : list DataCon -> AlgTyConRhs.

Axiom visibleDataCons : AlgTyConRhs -> list DataCon.

Axiom okParent : Name.Name -> AlgTyConFlav -> bool.

Axiom isNoParent : AlgTyConFlav -> bool.

Axiom tyConRepName_maybe : TyCon -> option TyConRepName.

Axiom mkPrelTyConRepName : Name.Name -> TyConRepName.

Axiom tyConRepModOcc : Module.Module ->
                       OccName.OccName -> (Module.Module * OccName.OccName)%type.

Axiom isGcPtrRep : PrimRep -> bool.

Axiom primRepCompatible : Platform.Platform -> PrimRep -> PrimRep -> bool.

Axiom primRepsCompatible : Platform.Platform ->
                           list PrimRep -> list PrimRep -> bool.

(* Skipping definition `Core.primRepSizeB' *)

Axiom primRepSizeW64_B : PrimRep -> nat.

Axiom primElemRepSizeB : Platform.Platform -> PrimElemRep -> nat.

Axiom primElemRepSizeW64_B : PrimElemRep -> nat.

Axiom primElemRepToPrimRep : PrimElemRep -> PrimRep.

Axiom primRepIsFloat : PrimRep -> option bool.

Axiom primRepIsWord : PrimRep -> bool.

Axiom primRepIsInt : PrimRep -> bool.

Axiom tyConFieldLabels : TyCon -> list FieldLabel.FieldLabel.

Axiom tyConFieldLabelEnv : TyCon -> FieldLabel.FieldLabelEnv.

Axiom lookupTyConFieldLabel : HsSyn.FieldLabelString ->
                              TyCon -> option FieldLabel.FieldLabel.

Axiom fieldsOfAlgTcRhs : AlgTyConRhs -> FieldLabel.FieldLabelEnv.

Axiom mkTyCon : Name.Name ->
                list TyConBinder -> Kind -> list HsSyn.Role -> TyConDetails -> TyCon.

Axiom mkAlgTyCon : Name.Name ->
                   list TyConBinder ->
                   Kind ->
                   list HsSyn.Role ->
                   option CType -> list PredType -> AlgTyConRhs -> AlgTyConFlav -> bool -> TyCon.

Axiom mkClassTyCon : Name.Name ->
                     list TyConBinder ->
                     list HsSyn.Role -> AlgTyConRhs -> Class -> Name.Name -> TyCon.

Axiom mkTupleTyCon : Name.Name ->
                     list TyConBinder ->
                     Kind -> DataCon -> BasicTypes.TupleSort -> AlgTyConFlav -> TyCon.

Axiom constRoles : list TyConBinder -> HsSyn.Role -> list HsSyn.Role.

Axiom mkSumTyCon : Name.Name ->
                   list TyConBinder -> Kind -> list DataCon -> AlgTyConFlav -> TyCon.

Axiom mkTcTyCon : Name.Name ->
                  list TyConBinder ->
                  Kind ->
                  list (Name.Name * TcTyVar)%type ->
                  bool -> BasicTypes.TyConFlavour TyCon -> TyCon.

Axiom noTcTyConScopedTyVars : list (Name.Name * TcTyVar)%type.

Axiom mkPrimTyCon : Name.Name ->
                    list TyConBinder -> Kind -> list HsSyn.Role -> TyCon.

Axiom mkSynonymTyCon : Name.Name ->
                       list TyConBinder ->
                       Kind -> list HsSyn.Role -> Type_ -> bool -> bool -> bool -> bool -> TyCon.

Axiom mkFamilyTyCon : Name.Name ->
                      list TyConBinder ->
                      Kind ->
                      option Name.Name -> FamTyConFlav -> option Class -> Injectivity -> TyCon.

Axiom mkPromotedDataCon : DataCon ->
                          Name.Name ->
                          TyConRepName ->
                          list TyConBinder -> Kind -> list HsSyn.Role -> PromDataConInfo -> TyCon.

Axiom isAbstractTyCon : TyCon -> bool.

Axiom isPrimTyCon : TyCon -> bool.

Axiom isAlgTyCon : TyCon -> bool.

Axiom isVanillaAlgTyCon : TyCon -> bool.

Axiom isValidDTT2TyCon : TyCon -> bool.

Axiom isDataTyCon : TyCon -> bool.

Axiom isTypeDataTyCon : TyCon -> bool.

Axiom isInjectiveTyCon : TyCon -> HsSyn.Role -> bool.

Axiom isGenerativeTyCon : TyCon -> HsSyn.Role -> bool.

Axiom isGenInjAlgRhs : AlgTyConRhs -> bool.

Axiom isNewTyCon : TyCon -> bool.

Axiom unwrapNewTyCon_maybe : TyCon ->
                             option (list TyVar * Type_ * CoAxiom Unbranched)%type.

Axiom unwrapNewTyConEtad_maybe : TyCon ->
                                 option (list TyVar * Type_ * CoAxiom Unbranched)%type.

Axiom isTypeSynonymTyCon : TyCon -> bool.

Axiom isTauTyCon : TyCon -> bool.

Axiom isFamFreeTyCon : TyCon -> bool.

Axiom isForgetfulSynTyCon : TyCon -> bool.

Axiom tyConMustBeSaturated : TyCon -> bool.

Axiom isGadtSyntaxTyCon : TyCon -> bool.

Axiom isEnumerationTyCon : TyCon -> bool.

Axiom isFamilyTyCon : TyCon -> bool.

Axiom isOpenFamilyTyCon : TyCon -> bool.

Axiom isTypeFamilyTyCon : TyCon -> bool.

Axiom isDataFamilyTyCon : TyCon -> bool.

Axiom isOpenTypeFamilyTyCon : TyCon -> bool.

Axiom isClosedSynFamilyTyConWithAxiom_maybe : TyCon ->
                                              option (CoAxiom Branched).

Axiom isBuiltInSynFamTyCon_maybe : TyCon -> option BuiltInSynFamily.

Axiom tyConFamilyResVar_maybe : TyCon -> option Name.Name.

Axiom tyConInjectivityInfo : TyCon -> Injectivity.

Axiom isDataFamFlav : FamTyConFlav -> bool.

Axiom isTyConAssoc : TyCon -> bool.

Axiom tyConAssoc_maybe : TyCon -> option TyCon.

Axiom isTupleTyCon : TyCon -> bool.

Axiom tyConTuple_maybe : TyCon -> option BasicTypes.TupleSort.

Axiom isUnboxedTupleTyCon : TyCon -> bool.

Axiom isBoxedTupleTyCon : TyCon -> bool.

Axiom isUnboxedSumTyCon : TyCon -> bool.

Axiom isLiftedAlgTyCon : TyCon -> bool.

Axiom isPromotedDataCon_maybe : TyCon -> option DataCon.

Axiom isPromotedTupleTyCon : TyCon -> bool.

Axiom isPromotedDataCon : TyCon -> bool.

Axiom isDataKindsPromotedDataCon : TyCon -> bool.

Axiom isKindTyCon : TyCon -> bool.

Axiom isKindName : Name.Name -> bool.

Axiom isKindUniquable : forall {a}, forall `{Unique.Uniquable a}, a -> bool.

Axiom kindTyConKeys : UniqSet.UniqSet Unique.Unique.

Axiom isLiftedTypeKindTyConName : Name.Name -> bool.

Axiom isImplicitTyCon : TyCon -> bool.

Axiom tyConCType_maybe : TyCon -> option CType.

Axiom tcHasFixedRuntimeRep : TyCon -> bool.

Axiom isConcreteTyCon : TyCon -> bool.

Axiom isTcTyCon : TyCon -> bool.

Axiom setTcTyConKind : TyCon -> Kind -> TyCon.

Axiom isMonoTcTyCon : TyCon -> bool.

Axiom tcTyConScopedTyVars : TyCon -> list (Name.Name * TcTyVar)%type.

Axiom expandSynTyCon_maybe : forall {tyco : Type},
                             TyCon -> list tyco -> ExpandSynResult tyco.

Axiom isTyConWithSrcDataCons : TyCon -> bool.

Axiom tyConDataCons : TyCon -> list DataCon.

Axiom tyConDataCons_maybe : TyCon -> option (list DataCon).

Axiom tyConSingleDataCon_maybe : TyCon -> option DataCon.

Axiom tyConSingleDataCon : TyCon -> DataCon.

Axiom tyConSingleAlgDataCon_maybe : TyCon -> option DataCon.

Axiom tyConAlgDataCons_maybe : TyCon -> option (list DataCon).

Axiom tyConFamilySize : TyCon -> nat.

Axiom algTyConRhs : TyCon -> AlgTyConRhs.

Axiom newTyConRhs : TyCon -> (list TyVar * Type_)%type.

Axiom newTyConEtadArity : TyCon -> nat.

Axiom newTyConEtadRhs : TyCon -> (list TyVar * Type_)%type.

Axiom newTyConCo_maybe : TyCon -> option (CoAxiom Unbranched).

Axiom newTyConCo : TyCon -> CoAxiom Unbranched.

Axiom newTyConDataCon_maybe : TyCon -> option DataCon.

Axiom tyConStupidTheta : TyCon -> list PredType.

Axiom synTyConDefn_maybe : TyCon -> option (list TyVar * Type_)%type.

Axiom synTyConRhs_maybe : TyCon -> option Type_.

Axiom famTyConFlav_maybe : TyCon -> option FamTyConFlav.

Axiom isClassTyCon : TyCon -> bool.

Axiom tyConClass_maybe : TyCon -> option Class.

Axiom tyConATs : TyCon -> list TyCon.

Axiom isFamInstTyCon : TyCon -> bool.

Axiom tyConFamInstSig_maybe : TyCon ->
                              option (TyCon * list Type_ * CoAxiom Unbranched)%type.

Axiom tyConFamInst_maybe : TyCon -> option (TyCon * list Type_)%type.

Axiom tyConFamilyCoercion_maybe : TyCon -> option (CoAxiom Unbranched).

Axiom tyConPromDataConInfo : TyCon -> PromDataConInfo.

Axiom mkTyConTagMap : TyCon -> NameEnv.NameEnv HsSyn.ConTag.

Axiom tyConFlavour : TyCon -> BasicTypes.TyConFlavour TyCon.

Axiom tcFlavourMustBeSaturated : forall {tc},
                                 BasicTypes.TyConFlavour tc -> bool.

Axiom tcFlavourIsOpen : forall {tc : Type}, BasicTypes.TyConFlavour tc -> bool.

Axiom pprPromotionQuote : TyCon -> GHC.Base.String.

Axiom tyConSkolem : TyCon -> bool.

Axiom rewriterView : Type_ -> option Type_.

Axiom coreView : Type_ -> option Type_.

Axiom coreFullView : Type_ -> Type_.

Axiom core_full_view : Type_ -> Type_.

Axiom expandSynTyConApp_maybe : TyCon -> list Type_ -> option Type_.

Axiom saturates : list Type_ -> BasicTypes.Arity -> bool.

Axiom expand_syn : list TyVar -> Type_ -> list Type_ -> Type_.

Axiom expandTypeSynonyms : Type_ -> Type_.

Axiom isTyConKeyApp_maybe : Unique.Unique -> Type_ -> option (list Type_).

Axiom kindRep : forall `{Util.HasDebugCallStack}, Kind -> RuntimeRepType.

Axiom kindRep_maybe : forall `{Util.HasDebugCallStack},
                      Kind -> option RuntimeRepType.

Axiom isLiftedTypeKind : Kind -> bool.

Axiom isUnliftedTypeKind : Kind -> bool.

Axiom pickyIsLiftedTypeKind : Kind -> bool.

Axiom kindBoxedRepLevity_maybe : Type_ -> option BasicTypes.Levity.

Axiom isLiftedRuntimeRep : RuntimeRepType -> bool.

Axiom isUnliftedRuntimeRep : RuntimeRepType -> bool.

Axiom isNullaryTyConKeyApp : Unique.Unique -> Type_ -> bool.

Axiom isLiftedLevity : Type_ -> bool.

Axiom isUnliftedLevity : Type_ -> bool.

Axiom isLevityTy : Type_ -> bool.

Axiom isRuntimeRepTy : Type_ -> bool.

Axiom isRuntimeRepVar : TyVar -> bool.

Axiom isLevityVar : TyVar -> bool.

Axiom isMultiplicityTy : Type_ -> bool.

Axiom isMultiplicityVar : TyVar -> bool.

Axiom splitRuntimeRep_maybe : RuntimeRepType ->
                              option (TyCon * list Type_)%type.

Axiom isBoxedRuntimeRep : RuntimeRepType -> bool.

Axiom isBoxedRuntimeRep_maybe : RuntimeRepType -> option LevityType.

Axiom runtimeRepLevity_maybe : RuntimeRepType -> option BasicTypes.Levity.

Axiom levityType_maybe : LevityType -> option BasicTypes.Levity.

Axiom mapTyCo : forall {m : Type -> Type},
                forall `{GHC.Base.Monad m},
                TyCoMapper unit m ->
                ((Type_ -> m Type_) * (list Type_ -> m (list Type_)) * (Coercion -> m Coercion)
                 *
                 (list Coercion -> m (list Coercion)))%type.

Axiom mapTyCoX : forall {m : Type -> Type},
                 forall {env : Type},
                 forall `{GHC.Base.Monad m},
                 TyCoMapper env m ->
                 ((env -> Type_ -> m Type_) * (env -> list Type_ -> m (list Type_)) *
                  (env -> Coercion -> m Coercion) *
                  (env -> list Coercion -> m (list Coercion)))%type.

Axiom getTyVar : forall `{Util.HasDebugCallStack}, Type_ -> TyVar.

Axiom getTyVar_maybe : Type_ -> option TyVar.

Axiom repGetTyVar_maybe : Type_ -> option TyVar.

Axiom isTyVarTy : Type_ -> bool.

Axiom getCastedTyVar_maybe : Type_ -> option (TyVar * CoercionN)%type.

Axiom mkAppTy : Type_ -> Type_ -> Type_.

Axiom mkAppTys : Type_ -> list Type_ -> Type_.

Axiom splitAppTy_maybe : Type_ -> option (Type_ * Type_)%type.

Axiom splitAppTy : Type_ -> (Type_ * Type_)%type.

Axiom splitAppTyNoView_maybe : forall `{Util.HasDebugCallStack},
                               Type_ -> option (Type_ * Type_)%type.

Axiom tcSplitAppTyNoView_maybe : Type_ -> option (Type_ * Type_)%type.

Axiom splitAppTys : forall `{Util.HasDebugCallStack},
                    Type_ -> (Type_ * list Type_)%type.

Axiom splitAppTysNoView : forall `{Util.HasDebugCallStack},
                          Type_ -> (Type_ * list Type_)%type.

Axiom mkNumLitTy : GHC.Num.Integer -> Type_.

Axiom isNumLitTy : Type_ -> option GHC.Num.Integer.

Axiom mkStrLitTy : FastString.FastString -> Type_.

Axiom isStrLitTy : Type_ -> option FastString.FastString.

Axiom mkCharLitTy : GHC.Char.Char -> Type_.

Axiom isCharLitTy : Type_ -> option GHC.Char.Char.

Axiom isLitTy : Type_ -> option TyLit.

Axiom userTypeError_maybe : Type_ -> option ErrorMsgType.

Axiom deepUserTypeError_maybe : Type_ -> option ErrorMsgType.

Axiom pprUserTypeErrorTy : ErrorMsgType -> GHC.Base.String.

Axiom funTyConAppTy_maybe : FunTyFlag ->
                            Type_ -> Type_ -> Type_ -> option (TyCon * list Type_)%type.

Axiom tyConAppFunTy_maybe : forall `{Util.HasDebugCallStack},
                            TyCon -> list Type_ -> option Type_.

Axiom tyConAppFunCo_maybe : forall `{Util.HasDebugCallStack},
                            HsSyn.Role -> TyCon -> list Coercion -> option Coercion.

(* Skipping definition `Core.ty_con_app_fun_maybe' *)

Axiom mkFunctionType : forall `{Util.HasDebugCallStack},
                       Mult -> Type_ -> Type_ -> Type_.

Axiom mkScaledFunctionTys : list (Scaled Type_) -> Type_ -> Type_.

Axiom chooseFunTyFlag : forall `{Util.HasDebugCallStack},
                        Type_ -> Type_ -> FunTyFlag.

Axiom splitFunTy : Type_ -> (Mult * Type_ * Type_)%type.

Axiom splitFunTy_maybe : Type_ ->
                         option (FunTyFlag * Mult * Type_ * Type_)%type.

Axiom splitFunTys : Type_ -> (list (Scaled Type_) * Type_)%type.

Axiom funResultTy : forall `{Util.HasDebugCallStack}, Type_ -> Type_.

Axiom funArgTy : forall `{Util.HasDebugCallStack}, Type_ -> Type_.

Axiom piResultTy : forall `{Util.HasDebugCallStack}, Type_ -> Type_ -> Type_.

Axiom piResultTy_maybe : Type_ -> Type_ -> option Type_.

Axiom piResultTys : forall `{Util.HasDebugCallStack},
                    Type_ -> list Type_ -> Type_.

Axiom applyTysX : forall `{Util.HasDebugCallStack},
                  list TyVar -> Type_ -> list Type_ -> Type_.

Axiom tyConAppTyConPicky_maybe : Type_ -> option TyCon.

Axiom tyConAppTyCon_maybe : Type_ -> option TyCon.

Axiom tyConAppTyCon : forall `{Util.HasDebugCallStack}, Type_ -> TyCon.

Axiom tyConAppArgs_maybe : Type_ -> option (list Type_).

Axiom tyConAppArgs : forall `{GHC.Prim.HasCallStack}, Type_ -> list Type_.

Axiom splitTyConApp : Type_ -> (TyCon * list Type_)%type.

Axiom splitTyConApp_maybe : forall `{Util.HasDebugCallStack},
                            Type_ -> option (TyCon * list Type_)%type.

Axiom splitTyConAppNoView_maybe : forall `{Util.HasDebugCallStack},
                                  Type_ -> option (TyCon * list Type_)%type.

Axiom tcSplitTyConApp_maybe : forall `{GHC.Prim.HasCallStack},
                              Type_ -> option (TyCon * list Type_)%type.

Axiom tcSplitTyConApp : Type_ -> (TyCon * list Type_)%type.

Axiom newTyConInstRhs : TyCon -> list Type_ -> Type_.

Axiom splitCastTy_maybe : Type_ -> option (Type_ * Coercion)%type.

Axiom mkCastTy : Type_ -> Coercion -> Type_.

Axiom mk_cast_ty : Type_ -> Coercion -> Type_.

Axiom mkCoercionTy : Coercion -> Type_.

Axiom isCoercionTy : Type_ -> bool.

Axiom isCoercionTy_maybe : Type_ -> option Coercion.

Axiom stripCoercionTy : Type_ -> Coercion.

Axiom tyConBindersPiTyBinders : list TyConBinder -> list PiTyBinder.

Axiom mkTyCoForAllTy : TyCoVar -> ForAllTyFlag -> Type_ -> Type_.

Axiom mkTyCoForAllTys : list ForAllTyBinder -> Type_ -> Type_.

Axiom mkTyCoInvForAllTy : TyCoVar -> Type_ -> Type_.

Axiom mkInfForAllTy : TyVar -> Type_ -> Type_.

Axiom mkTyCoInvForAllTys : list TyCoVar -> Type_ -> Type_.

Axiom mkInfForAllTys : list TyVar -> Type_ -> Type_.

Axiom mkSpecForAllTy : TyVar -> Type_ -> Type_.

Axiom mkSpecForAllTys : list TyVar -> Type_ -> Type_.

Axiom mkVisForAllTys : list TyVar -> Type_ -> Type_.

Axiom mkTyConBindersPreferAnon : list TyVar -> TyCoVarSet -> list TyConBinder.

Axiom splitForAllForAllTyBinders : Type_ -> (list ForAllTyBinder * Type_)%type.

Axiom splitForAllTyCoVars : Type_ -> (list TyCoVar * Type_)%type.

Axiom splitForAllTyVars : Type_ -> (list TyVar * Type_)%type.

Axiom splitForAllReqTyBinders : Type_ -> (list ReqTyBinder * Type_)%type.

Axiom splitForAllInvisTyBinders : Type_ -> (list InvisTyBinder * Type_)%type.

Axiom isForAllTy : Type_ -> bool.

Axiom isForAllTy_ty : Type_ -> bool.

Axiom isForAllTy_invis_ty : Type_ -> bool.

Axiom isForAllTy_co : Type_ -> bool.

Axiom isPiTy : Type_ -> bool.

Axiom isFunTy : Type_ -> bool.

Axiom splitForAllTyCoVar : Type_ -> (TyCoVar * Type_)%type.

Axiom dropForAlls : Type_ -> Type_.

Axiom splitForAllForAllTyBinder_maybe : Type_ ->
                                        option (ForAllTyBinder * Type_)%type.

Axiom splitForAllTyCoVar_maybe : Type_ -> option (TyCoVar * Type_)%type.

Axiom splitForAllTyVar_maybe : Type_ -> option (TyVar * Type_)%type.

Axiom splitForAllCoVar_maybe : Type_ -> option (CoVar * Type_)%type.

Axiom splitPiTy_maybe : Type_ -> option (PiTyBinder * Type_)%type.

Axiom splitPiTy : Type_ -> (PiTyBinder * Type_)%type.

Axiom splitPiTys : Type_ -> (list PiTyBinder * Type_)%type.

Axiom getRuntimeArgTys : Type_ -> list (Scaled Type_ * FunTyFlag)%type.

Axiom invisibleTyBndrCount : Type_ -> nat.

Axiom splitInvisPiTys : Type_ -> (list PiTyBinder * Type_)%type.

Axiom splitInvisPiTysN : nat -> Type_ -> (list PiTyBinder * Type_)%type.

Axiom filterOutInvisibleTypes : TyCon -> list Type_ -> list Type_.

Axiom filterOutInferredTypes : TyCon -> list Type_ -> list Type_.

Axiom partitionInvisibleTypes : TyCon ->
                                list Type_ -> (list Type_ * list Type_)%type.

Axiom partitionInvisibles : forall {a : Type},
                            list (a * ForAllTyFlag)%type -> (list a * list a)%type.

Axiom tyConForAllTyFlags : TyCon -> list Type_ -> list ForAllTyFlag.

Axiom appTyForAllTyFlags : Type_ -> list Type_ -> list ForAllTyFlag.

Axiom fun_kind_arg_flags : Kind -> list Type_ -> list ForAllTyFlag.

Axiom isTauTy : Type_ -> bool.

Axiom isAtomicTy : Type_ -> bool.

Axiom mkFamilyTyConApp : TyCon -> list Type_ -> Type_.

Axiom coAxNthLHS : forall {br : BranchFlag}, CoAxiom br -> nat -> Type_.

Axiom isFamFreeTy : Type_ -> bool.

Axiom buildSynTyCon : Name.Name ->
                      list (KnotTied TyConBinder) ->
                      Kind -> list HsSyn.Role -> KnotTied Type_ -> TyCon.

Axiom typeLevity_maybe : forall `{Util.HasDebugCallStack},
                         Type_ -> option BasicTypes.Levity.

Axiom typeLevity : forall `{Util.HasDebugCallStack}, Type_ -> BasicTypes.Levity.

Axiom isUnliftedType : forall `{Util.HasDebugCallStack}, Type_ -> bool.

Axiom mightBeLiftedType : Type_ -> bool.

Axiom definitelyLiftedType : Type_ -> bool.

Axiom mightBeUnliftedType : Type_ -> bool.

Axiom definitelyUnliftedType : Type_ -> bool.

Axiom isBoxedType : Type_ -> bool.

Axiom isRuntimeRepKindedTy : Type_ -> bool.

Axiom dropRuntimeRepArgs : list Type_ -> list Type_.

Axiom getRuntimeRep_maybe : forall `{Util.HasDebugCallStack},
                            Type_ -> option RuntimeRepType.

Axiom getRuntimeRep : forall `{Util.HasDebugCallStack}, Type_ -> RuntimeRepType.

Axiom getLevity_maybe : forall `{Util.HasDebugCallStack}, Type_ -> option Type_.

Axiom getLevity : forall `{Util.HasDebugCallStack}, Type_ -> Type_.

Axiom isUnboxedTupleType : Type_ -> bool.

Axiom isUnboxedSumType : Type_ -> bool.

Axiom isAlgType : Type_ -> bool.

Axiom isDataFamilyAppType : Type_ -> bool.

Axiom isStrictType : forall `{Util.HasDebugCallStack}, Type_ -> bool.

Axiom isTerminatingType : forall `{Util.HasDebugCallStack}, Type_ -> bool.

Axiom isCoVarType : Type_ -> bool.

Axiom isPrimitiveType : Type_ -> bool.

Axiom isValidJoinPointType : BasicTypes.JoinArity -> Type_ -> bool.

Axiom seqType : Type_ -> unit.

Axiom seqTypes : list Type_ -> unit.

Axiom typeKind : forall `{Util.HasDebugCallStack}, Type_ -> Kind.

Axiom sORTKind_maybe : Kind ->
                       option (BasicTypes.TypeOrConstraint * Type_)%type.

Axiom typeTypeOrConstraint : forall `{Util.HasDebugCallStack},
                             Type_ -> BasicTypes.TypeOrConstraint.

Axiom isPredTy : forall `{Util.HasDebugCallStack}, Type_ -> bool.

Axiom isTYPEorCONSTRAINT : Kind -> bool.

Axiom tyConIsTYPEorCONSTRAINT : TyCon -> bool.

Axiom isConstraintLikeKind : Kind -> bool.

Axiom isConstraintKind : Kind -> bool.

Axiom tcIsLiftedTypeKind : Kind -> bool.

Axiom tcIsBoxedTypeKind : Kind -> bool.

Axiom isTypeLikeKind : Kind -> bool.

Axiom returnsConstraintKind : Kind -> bool.

Axiom typeLiteralKind : TyLit -> Kind.

Axiom typeHasFixedRuntimeRep : forall `{Util.HasDebugCallStack}, Type_ -> bool.

Axiom isFixedRuntimeRepKind : forall `{Util.HasDebugCallStack}, Kind -> bool.

Axiom isConcreteType : Type_ -> bool.

Axiom tyConAppNeedsKindSig : bool -> TyCon -> nat -> bool.

Axiom unrestricted : forall {a : Type}, a -> Scaled a.

Axiom linear : forall {a : Type}, a -> Scaled a.

Axiom tymult : forall {a : Type}, a -> Scaled a.

Axiom irrelevantMult : forall {a : Type}, Scaled a -> a.

Axiom mkScaled : forall {a : Type}, Mult -> a -> Scaled a.

Axiom scaledSet : forall {a : Type},
                  forall {b : Type}, Scaled a -> b -> Scaled b.

Axiom isManyTy : Mult -> bool.

Axiom isOneTy : Mult -> bool.

Axiom isLinearType : Type_ -> bool.

Axiom mkTyConApp : TyCon -> list Type_ -> Type_.

Axiom mkTYPEapp : RuntimeRepType -> Type_.

Axiom mkTYPEapp_maybe : RuntimeRepType -> option Type_.

Axiom mkCONSTRAINTapp : RuntimeRepType -> Type_.

Axiom mkCONSTRAINTapp_maybe : RuntimeRepType -> option Type_.

Axiom mkBoxedRepApp_maybe : LevityType -> option Type_.

Axiom mkTupleRepApp_maybe : Type_ -> option Type_.

Axiom typeOrConstraintKind : BasicTypes.TypeOrConstraint ->
                             RuntimeRepType -> Kind.

Axiom boxedWins : HsSyn.Boxity -> HsSyn.Boxity -> HsSyn.Boxity.

Axiom _unboxedWins : HsSyn.Boxity -> HsSyn.Boxity -> HsSyn.Boxity.

Axiom lubBoxity : HsSyn.Boxity -> HsSyn.Boxity -> HsSyn.Boxity.

Axiom _botCard : Card.

Axiom topCard : Card.

Axiom isStrict : Card -> bool.

Axiom isAbs : Card -> bool.

Axiom isAtMostOnce : Card -> bool.

Axiom isCardNonAbs : Card -> bool.

Axiom isCardNonOnce : Card -> bool.

Axiom oneifyCard : Card -> Card.

Axiom strictifyCard : Card -> Card.

Axiom lubCard : Card -> Card -> Card.

Axiom glbCard : Card -> Card -> Card.

Axiom plusCard : Card -> Card -> Card.

Axiom multCard : Card -> Card -> Card.

Axiom viewDmdPair : Demand -> (Card * SubDemand)%type.

Axiom topSubDmd : SubDemand.

Axiom botSubDmd : SubDemand.

Axiom seqSubDmd : SubDemand.

Axiom polyFieldDmd : HsSyn.Boxity -> CardNonOnce -> Demand.

Axiom mkProd : HsSyn.Boxity -> list Demand -> SubDemand.

Axiom viewProd : BasicTypes.Arity ->
                 SubDemand -> option (HsSyn.Boxity * list Demand)%type.

Axiom mkCall : CardNonAbs -> SubDemand -> SubDemand.

Axiom viewCall : SubDemand -> option (Card * SubDemand)%type.

Axiom topDmd : Demand.

Axiom absDmd : Demand.

Axiom botDmd : Demand.

Axiom seqDmd : Demand.

Axiom unboxDeeplySubDmd : SubDemand -> SubDemand.

Axiom unboxDeeplyDmd : Demand -> Demand.

Axiom multDmd : Card -> Demand -> Demand.

Axiom multSubDmd : Card -> SubDemand -> SubDemand.

Axiom lazifyIfStrict : Card -> SubDemand -> SubDemand.

Axiom lubDmd : Demand -> Demand -> Demand.

Axiom lubSubDmd : SubDemand -> SubDemand -> SubDemand.

Axiom plusDmd : Demand -> Demand -> Demand.

Axiom plusSubDmd : SubDemand -> SubDemand -> SubDemand.

Axiom isTopDmd : Demand -> bool.

Axiom isAbsDmd : Demand -> bool.

Axiom isStrictDmd : Demand -> bool.

Axiom isStrUsedDmd : Demand -> bool.

Axiom isAtMostOnceDmd : Demand -> bool.

Axiom isWeakDmd : Demand -> bool.

Axiom evalDmd : Demand.

Axiom strictOnceApply1Dmd : Demand.

Axiom strictManyApply1Dmd : Demand.

Axiom lazyApply1Dmd : Demand.

Axiom lazyApply2Dmd : Demand.

Axiom oneifyDmd : Demand -> Demand.

Axiom strictifyDmd : Demand -> Demand.

(* Skipping definition `Core.strictifyDictDmd' *)

Axiom lazifyDmd : Demand -> Demand.

Axiom floatifyDmd : Demand -> Demand.

Axiom mkCalledOnceDmd : SubDemand -> SubDemand.

Axiom mkCalledOnceDmds : BasicTypes.Arity -> SubDemand -> SubDemand.

Axiom peelCallDmd : SubDemand -> (Card * SubDemand)%type.

Axiom peelManyCalls : BasicTypes.Arity -> SubDemand -> (Card * SubDemand)%type.

Axiom subDemandIfEvaluated : Demand -> SubDemand.

Axiom mkWorkerDemand : nat -> Demand.

Axiom argsOneShots : DmdSig ->
                     BasicTypes.Arity -> list (list BasicTypes.OneShotInfo).

Axiom argOneShots : Demand -> list BasicTypes.OneShotInfo.

Axiom callCards : SubDemand -> list Card.

Axiom saturatedByOneShots : nat -> Demand -> bool.

Axiom lubDivergence : Divergence -> Divergence -> Divergence.

Axiom plusDivergence : Divergence -> Divergence -> Divergence.

Axiom multDivergence : Card -> Divergence -> Divergence.

Axiom topDiv : Divergence.

Axiom exnDiv : Divergence.

Axiom botDiv : Divergence.

Axiom isDeadEndDiv : Divergence -> bool.

Axiom defaultFvDmd : Divergence -> Demand.

Axiom defaultArgDmd : Divergence -> Demand.

Axiom mkEmptyDmdEnv : Divergence -> DmdEnv.

Axiom mkTermDmdEnv : VarEnv Demand -> DmdEnv.

Axiom nopDmdEnv : DmdEnv.

Axiom botDmdEnv : DmdEnv.

Axiom exnDmdEnv : DmdEnv.

Axiom lubDmdEnv : DmdEnv -> DmdEnv -> DmdEnv.

Axiom addVarDmdEnv : DmdEnv -> Id -> Demand -> DmdEnv.

Axiom plusDmdEnv : DmdEnv -> DmdEnv -> DmdEnv.

Axiom plusDmdEnvs : list DmdEnv -> DmdEnv.

Axiom multDmdEnv : Card -> DmdEnv -> DmdEnv.

Axiom reuseEnv : DmdEnv -> DmdEnv.

Axiom lookupDmdEnv : DmdEnv -> Id -> Demand.

Axiom delDmdEnv : DmdEnv -> Id -> DmdEnv.

Axiom lubDmdType : DmdType -> DmdType -> DmdType.

Axiom discardArgDmds : DmdType -> DmdEnv.

Axiom plusDmdType : DmdType -> DmdEnv -> DmdType.

Axiom botDmdType : DmdType.

Axiom nopDmdType : DmdType.

Axiom exnDmdType : DmdType.

Axiom dmdTypeDepth : DmdType -> BasicTypes.Arity.

Axiom etaExpandDmdType : BasicTypes.Arity -> DmdType -> DmdType.

Axiom decreaseArityDmdType : DmdType -> DmdType.

Axiom splitDmdTy : DmdType -> (Demand * DmdType)%type.

Axiom multDmdType : Card -> DmdType -> DmdType.

Axiom peelFV : DmdType -> Var -> (DmdType * Demand)%type.

Axiom addDemand : Demand -> DmdType -> DmdType.

Axiom findIdDemand : DmdType -> Var -> Demand.

Axiom deferAfterPreciseException : DmdType -> DmdType.

Axiom mkDmdSigForArity : BasicTypes.Arity -> DmdType -> DmdSig.

Axiom mkClosedDmdSig : list Demand -> Divergence -> DmdSig.

Axiom mkVanillaDmdSig : BasicTypes.Arity -> Divergence -> DmdSig.

Axiom splitDmdSig : DmdSig -> (list Demand * Divergence)%type.

Axiom dmdSigDmdEnv : DmdSig -> DmdEnv.

Axiom hasDemandEnvSig : DmdSig -> bool.

Axiom botSig : DmdSig.

Axiom nopSig : DmdSig.

Axiom isNopSig : DmdSig -> bool.

Axiom isDeadEndSig : DmdSig -> bool.

Axiom isBottomingSig : DmdSig -> bool.

Axiom onlyBoxedArguments : DmdSig -> bool.

Axiom isDeadEndAppSig : DmdSig -> nat -> bool.

Axiom trimBoxityDmdEnv : DmdEnv -> DmdEnv.

Axiom trimBoxityDmdType : DmdType -> DmdType.

Axiom trimBoxityDmdSig : DmdSig -> DmdSig.

Axiom transferBoxity : Demand -> Demand -> Demand.

Axiom transferArgBoxityDmdType : DmdType -> DmdType -> DmdType.

Axiom transferArgBoxityDmdSig : DmdSig -> DmdSig -> DmdSig.

Axiom prependArgsDmdSig : nat -> DmdSig -> DmdSig.

Axiom etaConvertDmdSig : BasicTypes.Arity -> DmdSig -> DmdSig.

Axiom dmdTransformSig : DmdSig -> DmdTransformer.

Axiom dmdTransformDataConSig : list StrictnessMark -> DmdTransformer.

Axiom dmdTransformDictSelSig : DmdSig -> DmdTransformer.

Axiom zapDmdEnv : DmdEnv -> DmdEnv.

Axiom zapDmdEnvSig : DmdSig -> DmdSig.

Axiom zapUsageDemand : Demand -> Demand.

Axiom zapUsedOnceDemand : Demand -> Demand.

Axiom zapUsedOnceSig : DmdSig -> DmdSig.

Axiom kill_usage_card : KillFlags -> Card -> Card.

Axiom kill_usage : KillFlags -> Demand -> Demand.

Axiom kill_usage_sd : KillFlags -> SubDemand -> SubDemand.

(* Skipping definition `Core.trimToType' *)

Axiom trimBoxity : Demand -> Demand.

#[global] Definition seqDemand : Demand -> unit :=
  fun x => tt.

Axiom seqSubDemand : SubDemand -> unit.

#[global] Definition seqDemandList : list Demand -> unit :=
  fun x => tt.

#[global] Definition seqDmdType : DmdType -> unit :=
  fun x => tt.

#[global] Definition seqDmdEnv : DmdEnv -> unit :=
  fun x => tt.

Axiom seqDmdSig : DmdSig -> unit.

Axiom pp_boxity : HsSyn.Boxity -> GHC.Base.String.

#[global] Definition mkBinds {b : Type}
   : BasicTypes.RecFlag -> list (b * Expr b)%type -> list (Bind b) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | BasicTypes.Recursive, binds => cons (Rec binds) nil
    | BasicTypes.NonRecursive, binds =>
        GHC.Base.map (Data.Tuple.uncurry NonRec) binds
    end.

#[global] Definition isOrphan : IsOrphan -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_IsOrphan => true | _ => false end.

#[global] Definition notOrphan : IsOrphan -> bool :=
  fun arg_0__ => match arg_0__ with | NotOrphan _ => true | _ => false end.

#[global] Definition chooseOrphanAnchor (local_names : list Name.Name)
   : IsOrphan :=
  match GHC.Base.map Name.nameOccName local_names with
  | cons hd tl => NotOrphan (Data.Foldable.foldr GHC.Base.min hd tl)
  | nil => Mk_IsOrphan
  end.

#[global] Definition isBuiltinRule : CoreRule -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => true
    | _ => false
    end.

#[global] Definition isAutoRule : CoreRule -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => false
    | Rule _ _ _ _ _ _ _ is_auto _ _ _ => is_auto
    end.

#[global] Definition ruleArity : CoreRule -> nat :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ n _ => n
    | Rule _ _ _ _ _ args _ _ _ _ _ => Coq.Lists.List.length args
    end.

#[global] Definition ruleName : CoreRule -> BasicTypes.RuleName :=
  ru_name.

#[global] Definition ruleModule : CoreRule -> option Module.Module :=
  fun arg_0__ =>
    match arg_0__ with
    | Rule _ _ _ _ _ _ _ _ ru_origin _ _ => Some ru_origin
    | BuiltinRule _ _ _ _ => None
    end.

#[global] Definition ruleActivation : CoreRule -> BasicTypes.Activation :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => BasicTypes.AlwaysActive
    | Rule _ act _ _ _ _ _ _ _ _ _ => act
    end.

#[global] Definition ruleIdName : CoreRule -> Name.Name :=
  ru_fn.

#[global] Definition isLocalRule : CoreRule -> bool :=
  ru_local.

#[global] Definition setRuleIdName : Name.Name -> CoreRule -> CoreRule :=
  fun nm ru =>
    match ru with
    | Rule ru_name_0__ ru_act_1__ ru_fn_2__ ru_rough_3__ ru_bndrs_4__ ru_args_5__
    ru_rhs_6__ ru_auto_7__ ru_origin_8__ ru_orphan_9__ ru_local_10__ =>
        Rule ru_name_0__ ru_act_1__ nm ru_rough_3__ ru_bndrs_4__ ru_args_5__ ru_rhs_6__
             ru_auto_7__ ru_origin_8__ ru_orphan_9__ ru_local_10__
    | BuiltinRule ru_name_11__ ru_fn_12__ ru_nargs_13__ ru_try_14__ =>
        BuiltinRule ru_name_11__ nm ru_nargs_13__ ru_try_14__
    end.

#[global] Definition needSaturated : bool :=
  false.

#[global] Definition unSaturatedOk : bool :=
  true.

#[global] Definition boringCxtOk : bool :=
  true.

#[global] Definition boringCxtNotOk : bool :=
  false.

#[global] Definition noUnfolding : Unfolding :=
  NoUnfolding.

Axiom evaldUnfolding : Unfolding.

(* Skipping definition `Core.bootUnfolding' *)

(* Skipping definition `Core.mkOtherCon' *)

Axiom unfoldingTemplate : Unfolding -> CoreExpr.

#[global] Definition maybeUnfoldingTemplate : Unfolding -> option CoreExpr :=
  fun arg_0__ => None.

#[global] Definition otherCons : Unfolding -> list AltCon :=
  fun arg_0__ => nil.

#[global] Definition isValueUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition isEvaldUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition isConLikeUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition isCheapUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition isExpandableUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition expandUnfolding_maybe : Unfolding -> option CoreExpr :=
  fun arg_0__ => None.

#[global] Definition isCompulsoryUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition isStableUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition isStableUserUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition isStableSystemUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition isInlineUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition hasSomeUnfolding : Unfolding -> bool :=
  fun '(NoUnfolding) => false.

#[global] Definition isBootUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition neverUnfoldGuidance : UnfoldingGuidance -> bool :=
  fun arg_0__ => match arg_0__ with | UnfNever => true | _ => false end.

#[global] Definition hasCoreUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition canUnfold : Unfolding -> bool :=
  fun arg_0__ => false.

#[global] Definition cmpAltCon : AltCon -> AltCon -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | DEFAULT, DEFAULT => Eq
    | DEFAULT, _ => Lt
    | DataAlt d1, DataAlt d2 => GHC.Base.compare (dataConTag d1) (dataConTag d2)
    | DataAlt _, DEFAULT => Gt
    | LitAlt l1, LitAlt l2 => GHC.Base.compare l1 l2
    | LitAlt _, DEFAULT => Gt
    | con1, con2 =>
        Panic.pprPanic (GHC.Base.hs_string__ "cmpAltCon") (Panic.someSDoc)
    end.

#[global] Definition cmpAlt {a : Type} : Alt a -> Alt a -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Alt con1 _ _, Mk_Alt con2 _ _ => cmpAltCon con1 con2
    end.

#[global] Definition ltAlt {a : Type} : Alt a -> Alt a -> bool :=
  fun a1 a2 => (cmpAlt a1 a2) GHC.Base.== Lt.

Fixpoint deTagExpr {t : Type} (arg_0__ : TaggedExpr t) : CoreExpr
  := let deTagBind {t} (arg_0__ : TaggedBind t) : CoreBind :=
       match arg_0__ with
       | NonRec (TB b _) rhs => NonRec b (deTagExpr rhs)
       | Rec prs =>
           Rec (let cont_2__ arg_3__ :=
                  let 'pair (TB b _) rhs := arg_3__ in
                  cons (pair b (deTagExpr rhs)) nil in
                Coq.Lists.List.flat_map cont_2__ prs)
       end in
     let deTagAlt {t} (arg_0__ : TaggedAlt t) : CoreAlt :=
       let 'Mk_Alt con bndrs rhs := arg_0__ in
       Mk_Alt con (let cont_1__ arg_2__ := let 'TB b _ := arg_2__ in cons b nil in
                   Coq.Lists.List.flat_map cont_1__ bndrs) (deTagExpr rhs) in
     match arg_0__ with
     | Mk_Var v => Mk_Var v
     | Lit l => Lit l
     | Mk_Type ty => Mk_Type ty
     | Mk_Coercion co => Mk_Coercion co
     | App e1 e2 => App (deTagExpr e1) (deTagExpr e2)
     | Lam (TB b _) e => Lam b (deTagExpr e)
     | Let bind body => Let (deTagBind bind) (deTagExpr body)
     | Case e (TB b _) ty alts =>
         Case (deTagExpr e) b ty (GHC.Base.map deTagAlt alts)
     | Cast e co => Cast (deTagExpr e) co
     end.

#[global] Definition deTagBind {t} : TaggedBind t -> CoreBind :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec (TB b _) rhs => NonRec b (deTagExpr rhs)
    | Rec prs =>
        Rec (let cont_2__ arg_3__ :=
               let 'pair (TB b _) rhs := arg_3__ in
               cons (pair b (deTagExpr rhs)) nil in
             Coq.Lists.List.flat_map cont_2__ prs)
    end.

#[global] Definition deTagAlt {t} : TaggedAlt t -> CoreAlt :=
  fun '(Mk_Alt con bndrs rhs) =>
    Mk_Alt con (let cont_1__ arg_2__ := let 'TB b _ := arg_2__ in cons b nil in
                Coq.Lists.List.flat_map cont_1__ bndrs) (deTagExpr rhs).

#[global] Definition mkApps {b : Type} : Expr b -> list (Arg b) -> Expr b :=
  fun f args => Data.Foldable.foldl' App f args.

#[global] Definition mkCoApps {b : Type} : Expr b -> list Coercion -> Expr b :=
  fun f args => Data.Foldable.foldl' (fun e a => App e (Mk_Coercion a)) f args.

#[global] Definition varToCoreExpr {b : Type} : CoreBndr -> Expr b :=
  fun v => Mk_Var v.

#[global] Definition mkVarApps {b : Type} : Expr b -> list Var -> Expr b :=
  fun f vars => Data.Foldable.foldl' (fun e a => App e (varToCoreExpr a)) f vars.

#[global] Definition mkConApp {b : Type} : DataCon -> list (Arg b) -> Expr b :=
  fun con args => mkApps (Mk_Var (dataConWorkId con)) args.

#[global] Definition mkTyArg {b : Type} : Type_ -> Expr b :=
  fun ty =>
    match isCoercionTy_maybe ty with
    | Some co => Mk_Coercion co
    | _ => Mk_Type ty
    end.

#[global] Definition mkTyApps {b : Type} : Expr b -> list Type_ -> Expr b :=
  fun f args => Data.Foldable.foldl' (fun e a => App e (mkTyArg a)) f args.

#[global] Definition mkConApp2 {b : Type}
   : DataCon -> list Type_ -> list Var -> Expr b :=
  fun con tys arg_ids =>
    mkApps (mkApps (Mk_Var (dataConWorkId con)) (GHC.Base.map Mk_Type tys))
           (GHC.Base.map varToCoreExpr arg_ids).

(* Skipping definition `Core.mkIntLit' *)

#[global] Definition mkIntLitWrap {b : Type}
   : Platform.Platform -> GHC.Num.Integer -> Expr b :=
  fun platform n => Lit (mkLitIntWrap platform n).

(* Skipping definition `Core.mkWordLit' *)

#[global] Definition mkWordLitWrap {b : Type}
   : Platform.Platform -> GHC.Num.Integer -> Expr b :=
  fun platform w => Lit (mkLitWordWrap platform w).

#[global] Definition mkWord8Lit {b : Type} : GHC.Num.Integer -> Expr b :=
  fun w => Lit (mkLitWord8 w).

(* Skipping definition `Core.mkWord32LitWord32' *)

(* Skipping definition `Core.mkWord64LitWord64' *)

(* Skipping definition `Core.mkInt64LitInt64' *)

#[global] Definition mkCharLit {b : Type} : GHC.Char.Char -> Expr b :=
  fun c => Lit (mkLitChar c).

#[global] Definition mkStringLit {b : Type} : GHC.Base.String -> Expr b :=
  fun s => Lit (mkLitString s).

#[global] Definition mkFloatLit {b : Type} : GHC.Real.Rational -> Expr b :=
  fun f => Lit (mkLitFloat f).

(* Skipping definition `Core.mkFloatLitFloat' *)

#[global] Definition mkDoubleLit {b : Type} : GHC.Real.Rational -> Expr b :=
  fun d => Lit (mkLitDouble d).

(* Skipping definition `Core.mkDoubleLitDouble' *)

#[global] Definition mkLams {b : Type} : list b -> Expr b -> Expr b :=
  fun binders body => Data.Foldable.foldr Lam body binders.

#[global] Definition mkLet {b : Type} : Bind b -> Expr b -> Expr b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Rec nil, body => body
    | bind, body => Let bind body
    end.

#[global] Definition mkLets {b : Type} : list (Bind b) -> Expr b -> Expr b :=
  fun binds body => Data.Foldable.foldr mkLet body binds.

#[global] Definition mkLetNonRec {b : Type} : b -> Expr b -> Expr b -> Expr b :=
  fun b rhs body => Let (NonRec b rhs) body.

#[global] Definition mkLetRec {b : Type}
   : list (b * Expr b)%type -> Expr b -> Expr b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | nil, body => body
    | bs, body => Let (Rec bs) body
    end.

#[global] Definition mkTyBind : TyVar -> Type_ -> CoreBind :=
  fun tv ty => NonRec tv (Mk_Type ty).

#[global] Definition mkCoBind : CoVar -> Coercion -> CoreBind :=
  fun cv co => NonRec cv (Mk_Coercion co).

#[global] Definition varsToCoreExprs {b : Type}
   : list CoreBndr -> list (Expr b) :=
  fun vs => GHC.Base.map varToCoreExpr vs.

(* Skipping definition `Core.exprToType' *)

#[global] Definition bindersOf {b : Type} : Bind b -> list b :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec binder _ => cons binder nil
    | Rec pairs =>
        let cont_2__ arg_3__ := let 'pair binder _ := arg_3__ in cons binder nil in
        Coq.Lists.List.flat_map cont_2__ pairs
    end.

#[global] Definition bindersOfBinds {b : Type} : list (Bind b) -> list b :=
  fun binds =>
    Data.Foldable.foldr (Coq.Init.Datatypes.app GHC.Base.∘ bindersOf) nil binds.

#[global] Definition foldBindersOfBindStrict {a : Type} {b : Type}
   : (a -> b -> a) -> a -> Bind b -> a :=
  fun f =>
    fun z bind =>
      match bind with
      | NonRec b _rhs => f z b
      | Rec pairs => Data.Foldable.foldl' f z (GHC.Base.map Data.Tuple.fst pairs)
      end.

#[global] Definition foldBindersOfBindsStrict {a : Type} {b : Type}
   : (a -> b -> a) -> a -> list (Bind b) -> a :=
  fun f =>
    let fold_bind := (foldBindersOfBindStrict f) in
    fun z binds => Data.Foldable.foldl' fold_bind z binds.

#[global] Definition rhssOfBind {b : Type} : Bind b -> list (Expr b) :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec _ rhs => cons rhs nil
    | Rec pairs =>
        let cont_2__ arg_3__ := let 'pair _ rhs := arg_3__ in cons rhs nil in
        Coq.Lists.List.flat_map cont_2__ pairs
    end.

#[global] Definition rhssOfAlts {b : Type} : list (Alt b) -> list (Expr b) :=
  fun alts =>
    let cont_0__ arg_1__ := let 'Mk_Alt _ _ e := arg_1__ in cons e nil in
    Coq.Lists.List.flat_map cont_0__ alts.

Fixpoint flattenBinds {b : Type} (arg_0__ : list (Bind b)) : list (b *
                                                                   Expr b)%type
  := match arg_0__ with
     | cons (NonRec b r) binds => cons (pair b r) (flattenBinds binds)
     | cons (Rec prs1) binds => Coq.Init.Datatypes.app prs1 (flattenBinds binds)
     | nil => nil
     end.

(* Skipping definition `Core.collectBinders' *)

#[global] Definition isTyVar : Var -> bool :=
  fun arg_0__ => false.

#[global] Definition collectTyBinders
   : CoreExpr -> (list TyVar * CoreExpr)%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
      := let j_3__ :=
           match arg_0__, arg_1__ with
           | tvs, e => pair (GHC.List.reverse tvs) e
           end in
         match arg_0__, arg_1__ with
         | tvs, Lam b e => if isTyVar b : bool then go (cons b tvs) e else j_3__
         | _, _ => j_3__
         end in
    go nil expr.

#[global] Definition isId : Var -> bool :=
  fun '(Mk_Id _ _ _ _ _ _ _) => true.

#[global] Definition collectValBinders
   : CoreExpr -> (list Id * CoreExpr)%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
      := let j_3__ :=
           match arg_0__, arg_1__ with
           | ids, body => pair (GHC.List.reverse ids) body
           end in
         match arg_0__, arg_1__ with
         | ids, Lam b e => if isId b : bool then go (cons b ids) e else j_3__
         | _, _ => j_3__
         end in
    go nil expr.

#[global] Definition collectTyAndValBinders
   : CoreExpr -> (list TyVar * list Id * CoreExpr)%type :=
  fun expr =>
    let 'pair tvs body1 := collectTyBinders expr in
    let 'pair ids body := collectValBinders body1 in
    pair (pair tvs ids) body.

(* Skipping definition `Core.collectNBinders' *)

#[global] Definition collectNValBinders_maybe
   : BasicTypes.Arity -> CoreExpr -> option (list Var * CoreExpr)%type :=
  fun orig_n orig_expr =>
    let fix go arg_0__ arg_1__ arg_2__
      := match arg_0__, arg_1__, arg_2__ with
         | num_3__, bs, expr =>
             if num_3__ GHC.Base.== #0 : bool
             then Some (pair (GHC.List.reverse bs) expr) else
             match arg_0__, arg_1__, arg_2__ with
             | n, bs, Lam b e =>
                 if isId b : bool then go (n GHC.Num.- #1) (cons b bs) e else
                 go n (cons b bs) e
             | _, _, _ => None
             end
         end in
    go orig_n nil orig_expr.

(* Skipping definition `Core.collectArgs' *)

#[global] Definition collectFunSimple {b : Type} : Expr b -> Expr b :=
  fun expr =>
    let fix go expr'
      := match expr' with
         | App f _a => go f
         | Cast e _co => go e
         | e => e
         end in
    go expr.

#[global] Definition wrapLamBody
   : (CoreExpr -> CoreExpr) -> CoreExpr -> CoreExpr :=
  fun f expr =>
    let fix go arg_0__
      := match arg_0__ with
         | Lam v body => Lam v (go body)
         | expr => f expr
         end in
    go expr.

Fixpoint stripNArgs {a : Type} (arg_0__ : GHC.Num.Word) (arg_1__ : Expr a)
  : option (Expr a)
  := match arg_0__, arg_1__ with
     | n, Cast f _ => stripNArgs n f
     | num_2__, e =>
         if num_2__ GHC.Base.== #0 : bool then Some e else
         match arg_0__, arg_1__ with
         | n, App f _ => stripNArgs (n GHC.Num.- #1) f
         | _, _ => None
         end
     end.

#[global] Definition collectArgsTicks {b : Type}
   : (GHC.Types.Tickish.CoreTickish -> bool) ->
     Expr b -> (Expr b * list (Arg b) * list GHC.Types.Tickish.CoreTickish)%type :=
  fun skipTick expr =>
    let fix go arg_0__ arg_1__ arg_2__
      := match arg_0__, arg_1__, arg_2__ with
         | App f a, as_, ts => go f (cons a as_) ts
         | e, as_, ts => pair (pair e as_) (GHC.List.reverse ts)
         end in
    go expr nil nil.

#[global] Definition isRuntimeVar : Var -> bool :=
  isId.

#[global] Definition isTypeArg {b : Type} : Expr b -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_Type _ => true | _ => false end.

#[global] Definition isValArg {b : Type} : Expr b -> bool :=
  fun e => negb (isTypeArg e).

#[global] Definition isRuntimeArg : CoreExpr -> bool :=
  isValArg.

#[global] Definition isTyCoArg {b : Type} : Expr b -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Type _ => true
    | Mk_Coercion _ => true
    | _ => false
    end.

#[global] Definition isCoArg {b : Type} : Expr b -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_Coercion _ => true | _ => false end.

#[global] Definition valBndrCount : list CoreBndr -> nat :=
  Util.count isId.

#[global] Definition valArgCount {b : Type} : list (Arg b) -> nat :=
  Util.count isValArg.

#[global] Program Definition collectAnnArgs {b : Type} {a : Type}
   : AnnExpr b a -> (AnnExpr b a * list (AnnExpr b a))%type :=
  fun expr =>
    let go :=
      HsToCoq.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                           size_AnnExpr' (snd arg_0__)) _ (fun arg_0__ arg_1__ go =>
                           match arg_0__, arg_1__ with
                           | pair _ (AnnApp f a), as_ => go f (cons a as_)
                           | e, as_ => pair e as_
                           end) in
    go expr nil.
Solve Obligations with (solve_collectAnnArgsTicks).

#[global] Program Definition collectAnnArgsTicks {b : Type} {a : Type}
   : (GHC.Types.Tickish.CoreTickish -> bool) ->
     AnnExpr b a ->
     (AnnExpr b a * list (AnnExpr b a) * list GHC.Types.Tickish.CoreTickish)%type :=
  fun tickishOk expr =>
    let go :=
      HsToCoq.Wf.wfFix3 Coq.Init.Peano.lt (fun arg_0__ arg_1__ arg_2__ =>
                           size_AnnExpr' (snd arg_0__)) _ (fun arg_0__ arg_1__ arg_2__ go =>
                           match arg_0__, arg_1__, arg_2__ with
                           | pair _ (AnnApp f a), as_, ts => go f (cons a as_) ts
                           | e, as_, ts => pair (pair e as_) (GHC.List.reverse ts)
                           end) in
    go expr nil nil.
Solve Obligations with (solve_collectAnnArgsTicks).

#[global] Definition deAnnotate'
   : forall {bndr : Type} {annot : Type}, AnnExpr' bndr annot -> Expr bndr :=
  fix deAnnotate' {bndr annot : Type} (arg_0__ : AnnExpr' bndr annot) : Expr bndr
    := let deAnnotate {bndr annot : Type} (arg_0__ : AnnExpr bndr annot)
        : Expr bndr :=
         let 'pair _ e := arg_0__ in
         deAnnotate' e in
       let deAnnAlt {bndr annot : Type} (arg_0__ : AnnAlt bndr annot) : Alt bndr :=
         let 'Mk_AnnAlt con args rhs := arg_0__ in
         Mk_Alt con args (deAnnotate rhs) in
       match arg_0__ with
       | AnnType t => Mk_Type t
       | AnnCoercion co => Mk_Coercion co
       | AnnVar v => Mk_Var v
       | AnnLit lit => Lit lit
       | AnnLam binder body => Lam binder (deAnnotate body)
       | AnnApp fun_ arg => App (deAnnotate fun_) (deAnnotate arg)
       | AnnCast e (pair _ co) => Cast (deAnnotate e) co
       | AnnLet bind body => Let (deAnnBind bind) (deAnnotate body)
       | AnnCase scrut v t alts =>
           Case (deAnnotate scrut) v t (GHC.Base.map deAnnAlt alts)
       end
  with deAnnBind {b annot : Type} (arg_0__ : AnnBind b annot) : Bind b
    := let deAnnotate {bndr annot : Type} (arg_0__ : AnnExpr bndr annot)
        : Expr bndr :=
         let 'pair _ e := arg_0__ in
         deAnnotate' e in
       match arg_0__ with
       | AnnNonRec var rhs => NonRec var (deAnnotate rhs)
       | AnnRec pairs =>
           Rec (let cont_2__ arg_3__ :=
                  let 'pair v rhs := arg_3__ in
                  cons (pair v (deAnnotate rhs)) nil in
                Coq.Lists.List.flat_map cont_2__ pairs)
       end for deAnnotate'.

#[global] Definition deAnnotate {bndr : Type} {annot : Type}
   : AnnExpr bndr annot -> Expr bndr :=
  fun '(pair _ e) => deAnnotate' e.

#[global] Definition deAnnAlt {bndr : Type} {annot : Type}
   : AnnAlt bndr annot -> Alt bndr :=
  fun '(Mk_AnnAlt con args rhs) => Mk_Alt con args (deAnnotate rhs).

#[global] Definition deAnnBind
   : forall {b : Type} {annot : Type}, AnnBind b annot -> Bind b :=
  fix deAnnotate' {bndr annot : Type} (arg_0__ : AnnExpr' bndr annot) : Expr bndr
    := let deAnnotate {bndr annot : Type} (arg_0__ : AnnExpr bndr annot)
        : Expr bndr :=
         let 'pair _ e := arg_0__ in
         deAnnotate' e in
       let deAnnAlt {bndr annot : Type} (arg_0__ : AnnAlt bndr annot) : Alt bndr :=
         let 'Mk_AnnAlt con args rhs := arg_0__ in
         Mk_Alt con args (deAnnotate rhs) in
       match arg_0__ with
       | AnnType t => Mk_Type t
       | AnnCoercion co => Mk_Coercion co
       | AnnVar v => Mk_Var v
       | AnnLit lit => Lit lit
       | AnnLam binder body => Lam binder (deAnnotate body)
       | AnnApp fun_ arg => App (deAnnotate fun_) (deAnnotate arg)
       | AnnCast e (pair _ co) => Cast (deAnnotate e) co
       | AnnLet bind body => Let (deAnnBind bind) (deAnnotate body)
       | AnnCase scrut v t alts =>
           Case (deAnnotate scrut) v t (GHC.Base.map deAnnAlt alts)
       end
  with deAnnBind {b annot : Type} (arg_0__ : AnnBind b annot) : Bind b
    := let deAnnotate {bndr annot : Type} (arg_0__ : AnnExpr bndr annot)
        : Expr bndr :=
         let 'pair _ e := arg_0__ in
         deAnnotate' e in
       match arg_0__ with
       | AnnNonRec var rhs => NonRec var (deAnnotate rhs)
       | AnnRec pairs =>
           Rec (let cont_2__ arg_3__ :=
                  let 'pair v rhs := arg_3__ in
                  cons (pair v (deAnnotate rhs)) nil in
                Coq.Lists.List.flat_map cont_2__ pairs)
       end for deAnnBind.

#[global] Program Definition collectAnnBndrs {bndr : Type} {annot : Type}
   : AnnExpr bndr annot -> (list bndr * AnnExpr bndr annot)%type :=
  fun e =>
    let collect :=
      HsToCoq.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                           size_AnnExpr' (snd arg_1__)) _ (fun arg_0__ arg_1__ collect =>
                           match arg_0__, arg_1__ with
                           | bs, pair _ (AnnLam b body) => collect (cons b bs) body
                           | bs, body => pair (GHC.List.reverse bs) body
                           end) in
    collect nil e.

(* Skipping definition `Core.collectNAnnBndrs' *)

#[global] Definition idDetailsConcreteTvs
   : IdDetails -> TcType.ConcreteTyVars :=
  fun arg_0__ =>
    match arg_0__ with
    | PrimOpId _ conc_tvs => conc_tvs
    | RepPolyId conc_tvs => conc_tvs
    | DataConWorkId dc => dataConConcreteTyVars dc
    | DataConWrapId dc => dataConConcreteTyVars dc
    | _ => TcType.noConcreteTyVars
    end.

#[global] Definition recSelParentName : RecSelParent -> Name.Name :=
  fun arg_0__ =>
    match arg_0__ with
    | RecSelData tc => tyConName tc
    | RecSelPatSyn ps => patSynName ps
    end.

#[global] Definition recSelFirstConName : RecSelParent -> Name.Name :=
  fun arg_0__ =>
    match arg_0__ with
    | RecSelData tc => dataConName (GHC.Err.head (tyConDataCons tc))
    | RecSelPatSyn ps => patSynName ps
    end.

#[global] Definition recSelParentCons : RecSelParent -> list ConLike :=
  fun arg_0__ =>
    match arg_0__ with
    | RecSelData tc =>
        if isAlgTyCon tc : bool
        then GHC.Base.map RealDataCon (visibleDataCons (algTyConRhs tc)) else
        nil
    | RecSelPatSyn ps => cons (PatSynCon ps) nil
    end.

(* Skipping definition `Core.coVarDetails' *)

#[global] Definition isCoVarDetails : IdDetails -> bool :=
  fun arg_0__ => false.

#[global] Definition isJoinIdDetails_maybe
   : IdDetails ->
     option (BasicTypes.JoinArity * option (list BasicTypes.CbvMark))%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_JoinId join_arity marks => Some (pair join_arity marks)
    | _ => None
    end.

(* Skipping definition `Core.pprIdDetails' *)

#[global] Definition emptyBitField : BitField :=
  Mk_BitField #0.

#[global] Definition bitfieldGetOneShotInfo
   : BitField -> BasicTypes.OneShotInfo :=
  fun '(Mk_BitField bits) =>
    if Data.Bits.testBit bits #0 : bool
    then BasicTypes.OneShotLam
    else BasicTypes.NoOneShotInfo.

#[global] Definition bitfieldGetCafInfo : BitField -> CafInfo :=
  fun '(Mk_BitField bits) =>
    if Data.Bits.testBit bits #1 : bool
    then NoCafRefs
    else MayHaveCafRefs.

Axiom bitfieldGetCallArityInfo : BitField -> ArityInfo.

Axiom bitfieldGetArityInfo : BitField -> ArityInfo.

#[global] Definition bitfieldSetOneShotInfo
   : BasicTypes.OneShotInfo -> BitField -> BitField :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | info, Mk_BitField bits =>
        match info with
        | BasicTypes.NoOneShotInfo => Mk_BitField (Data.Bits.clearBit bits #0)
        | BasicTypes.OneShotLam => Mk_BitField (Data.Bits.setBit bits #0)
        end
    end.

#[global] Definition bitfieldSetCafInfo : CafInfo -> BitField -> BitField :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | info, Mk_BitField bits =>
        match info with
        | MayHaveCafRefs => Mk_BitField (Data.Bits.clearBit bits #1)
        | NoCafRefs => Mk_BitField (Data.Bits.setBit bits #1)
        end
    end.

Axiom bitfieldSetCallArityInfo : ArityInfo -> BitField -> BitField.

Axiom bitfieldSetArityInfo : ArityInfo -> BitField -> BitField.

#[global] Definition oneShotInfo : IdInfo -> BasicTypes.OneShotInfo :=
  bitfieldGetOneShotInfo GHC.Base.∘ bitfield.

#[global] Definition arityInfo : IdInfo -> ArityInfo :=
  bitfieldGetArityInfo GHC.Base.∘ bitfield.

#[global] Definition cafInfo : IdInfo -> CafInfo :=
  bitfieldGetCafInfo GHC.Base.∘ bitfield.

#[global] Definition callArityInfo : IdInfo -> ArityInfo :=
  bitfieldGetCallArityInfo GHC.Base.∘ bitfield.

#[global] Definition tagSigInfo
   : IdInfo -> option GHC.Stg.InferTags.TagSig.TagSig :=
  tagSig.

#[global] Definition setRuleInfo : IdInfo -> RuleInfo -> IdInfo :=
  fun info sp =>
    GHC.Prim.seq sp (let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__
                        inlinePragInfo_2__ occInfo_3__ dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__
                        bitfield_7__ lfInfo_8__ tagSig_9__ := info in
                  Mk_IdInfo sp realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__ dmdSigInfo_4__
                            cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__ tagSig_9__).

#[global] Definition setInlinePragInfo
   : IdInfo -> BasicTypes.InlinePragma -> IdInfo :=
  fun info pr =>
    GHC.Prim.seq pr (let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__
                        inlinePragInfo_2__ occInfo_3__ dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__
                        bitfield_7__ lfInfo_8__ tagSig_9__ := info in
                  Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ pr occInfo_3__ dmdSigInfo_4__
                            cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__ tagSig_9__).

#[global] Definition setOccInfo : IdInfo -> BasicTypes.OccInfo -> IdInfo :=
  fun info oc =>
    GHC.Prim.seq oc (let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__
                        inlinePragInfo_2__ occInfo_3__ dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__
                        bitfield_7__ lfInfo_8__ tagSig_9__ := info in
                  Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ oc
                            dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__
                            tagSig_9__).

#[global] Definition trimUnfolding : Unfolding -> Unfolding :=
  fun unf => if isEvaldUnfolding unf : bool then evaldUnfolding else noUnfolding.

#[global] Definition unfoldingInfo : IdInfo -> Unfolding :=
  fun info =>
    if BasicTypes.isStrongLoopBreaker (occInfo info) : bool
    then trimUnfolding (realUnfoldingInfo info) else
    realUnfoldingInfo info.

#[global] Definition setUnfoldingInfo : IdInfo -> Unfolding -> IdInfo :=
  fun info uf =>
    let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
       dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__
       tagSig_9__ := info in
    Mk_IdInfo ruleInfo_0__ uf inlinePragInfo_2__ occInfo_3__ dmdSigInfo_4__
              cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__ tagSig_9__.

#[global] Definition hasInlineUnfolding : IdInfo -> bool :=
  fun info => isInlineUnfolding (unfoldingInfo info).

#[global] Definition setArityInfo : IdInfo -> ArityInfo -> IdInfo :=
  fun info ar =>
    let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
       dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__
       tagSig_9__ := info in
    Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
              dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ (bitfieldSetArityInfo ar (bitfield
                                                                                     info)) lfInfo_8__ tagSig_9__.

#[global] Definition setCallArityInfo : IdInfo -> ArityInfo -> IdInfo :=
  fun info ar =>
    let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
       dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__
       tagSig_9__ := info in
    Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
              dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ (bitfieldSetCallArityInfo ar
               (bitfield info)) lfInfo_8__ tagSig_9__.

#[global] Definition setCafInfo : IdInfo -> CafInfo -> IdInfo :=
  fun info caf =>
    let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
       dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__
       tagSig_9__ := info in
    Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
              dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ (bitfieldSetCafInfo caf (bitfield
                                                                                    info)) lfInfo_8__ tagSig_9__.

#[global] Definition setLFInfo
   : IdInfo -> GHC.StgToCmm.Types.LambdaFormInfo -> IdInfo :=
  fun info lf =>
    let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
       dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__
       tagSig_9__ := info in
    Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
              dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ (Some lf) tagSig_9__.

#[global] Definition setTagSig
   : IdInfo -> GHC.Stg.InferTags.TagSig.TagSig -> IdInfo :=
  fun info sig =>
    let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
       dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__
       tagSig_9__ := info in
    Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
              dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__ (Some sig).

#[global] Definition setOneShotInfo
   : IdInfo -> BasicTypes.OneShotInfo -> IdInfo :=
  fun info lb =>
    let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
       dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__
       tagSig_9__ := info in
    Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
              dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ (bitfieldSetOneShotInfo lb
               (bitfield info)) lfInfo_8__ tagSig_9__.

#[global] Definition setDemandInfo : IdInfo -> Demand -> IdInfo :=
  fun info dd =>
    GHC.Prim.seq dd (let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__
                        inlinePragInfo_2__ occInfo_3__ dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__
                        bitfield_7__ lfInfo_8__ tagSig_9__ := info in
                  Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
                            dmdSigInfo_4__ cprSigInfo_5__ dd bitfield_7__ lfInfo_8__ tagSig_9__).

#[global] Definition setDmdSigInfo : IdInfo -> DmdSig -> IdInfo :=
  fun info dd =>
    GHC.Prim.seq dd (let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__
                        inlinePragInfo_2__ occInfo_3__ dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__
                        bitfield_7__ lfInfo_8__ tagSig_9__ := info in
                  Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__ dd
                            cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__ tagSig_9__).

#[global] Definition setCprSigInfo : IdInfo -> GHC.Types.Cpr.CprSig -> IdInfo :=
  fun info cpr =>
    GHC.Prim.seq cpr (let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__
                         inlinePragInfo_2__ occInfo_3__ dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__
                         bitfield_7__ lfInfo_8__ tagSig_9__ := info in
                  Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
                            dmdSigInfo_4__ cpr demandInfo_6__ bitfield_7__ lfInfo_8__ tagSig_9__).

#[global] Definition emptyRuleInfo :=
  EmptyRuleInfo.

#[global] Definition unknownArity : BasicTypes.Arity :=
  #0.

#[global] Definition vanillaCafInfo : CafInfo :=
  MayHaveCafRefs.

#[global] Definition vanillaIdInfo : IdInfo :=
  Mk_IdInfo emptyRuleInfo noUnfolding BasicTypes.defaultInlinePragma
            BasicTypes.noOccInfo nopSig GHC.Types.Cpr.topCprSig topDmd (bitfieldSetCafInfo
             vanillaCafInfo (bitfieldSetArityInfo unknownArity (bitfieldSetCallArityInfo
                                                   unknownArity (bitfieldSetOneShotInfo BasicTypes.NoOneShotInfo
                                                                                        emptyBitField)))) None None.

#[global] Definition noCafIdInfo : IdInfo :=
  setCafInfo vanillaIdInfo NoCafRefs.

(* Skipping definition `Core.ppArityInfo' *)

(* Skipping definition `Core.pprStrictness' *)

#[global] Definition isEmptyRuleInfo : RuleInfo -> bool :=
  fun x => true.

#[global] Definition emptyDVarSet : DVarSet :=
  UniqSet.emptyUniqSet.

#[global] Definition ruleInfoFreeVars : RuleInfo -> DVarSet :=
  fun x => emptyDVarSet.

#[global] Definition ruleInfoRules : RuleInfo -> list CoreRule :=
  fun x => nil.

#[global] Definition setRuleInfoHead : Name.Name -> RuleInfo -> RuleInfo :=
  fun x y => EmptyRuleInfo.

#[global] Definition mayHaveCafRefs : CafInfo -> bool :=
  fun arg_0__ => match arg_0__ with | MayHaveCafRefs => true | _ => false end.

(* Skipping definition `Core.ppCafInfo' *)

#[global] Definition zapLamInfo : IdInfo -> option IdInfo :=
  fun '((Mk_IdInfo _ _ _ occ _ _ demand _ _ _ as info)) =>
    let is_safe_dmd := fun dmd => negb (isStrUsedDmd dmd) in
    let safe_occ :=
      match occ with
      | BasicTypes.OneOcc _ _ _ _ =>
          match occ with
          | BasicTypes.ManyOccs _ =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          | BasicTypes.IAmDead =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          | BasicTypes.OneOcc occ_in_lam_2__ occ_n_br_3__ occ_int_cxt_4__ occ_tail_5__ =>
              BasicTypes.OneOcc BasicTypes.IsInsideLam occ_n_br_3__ occ_int_cxt_4__
                                BasicTypes.NoTailCallInfo
          | BasicTypes.IAmALoopBreaker _ _ =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          end
      | BasicTypes.IAmALoopBreaker _ _ =>
          match occ with
          | BasicTypes.ManyOccs occ_tail_12__ =>
              BasicTypes.ManyOccs BasicTypes.NoTailCallInfo
          | BasicTypes.IAmDead =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          | BasicTypes.OneOcc occ_in_lam_13__ occ_n_br_14__ occ_int_cxt_15__
          occ_tail_16__ =>
              BasicTypes.OneOcc occ_in_lam_13__ occ_n_br_14__ occ_int_cxt_15__
                                BasicTypes.NoTailCallInfo
          | BasicTypes.IAmALoopBreaker occ_rules_only_17__ occ_tail_18__ =>
              BasicTypes.IAmALoopBreaker occ_rules_only_17__ BasicTypes.NoTailCallInfo
          end
      | _other => occ
      end in
    let is_safe_occ :=
      fun arg_27__ =>
        let 'occ := arg_27__ in
        if BasicTypes.isAlwaysTailCalled occ : bool then false else
        match arg_27__ with
        | BasicTypes.OneOcc BasicTypes.NotInsideLam _ _ _ => false
        | _other => true
        end in
    if andb (is_safe_occ occ) (is_safe_dmd demand) : bool then None else
    Some (let 'Mk_IdInfo ruleInfo_31__ realUnfoldingInfo_32__ inlinePragInfo_33__
             occInfo_34__ dmdSigInfo_35__ cprSigInfo_36__ demandInfo_37__ bitfield_38__
             lfInfo_39__ tagSig_40__ := info in
          Mk_IdInfo ruleInfo_31__ realUnfoldingInfo_32__ inlinePragInfo_33__ safe_occ
                    dmdSigInfo_35__ cprSigInfo_36__ topDmd bitfield_38__ lfInfo_39__ tagSig_40__).

#[global] Definition lazifyDemandInfo : IdInfo -> option IdInfo :=
  fun '((Mk_IdInfo _ _ _ _ _ _ dmd _ _ _ as info)) =>
    Some (let 'Mk_IdInfo ruleInfo_1__ realUnfoldingInfo_2__ inlinePragInfo_3__
             occInfo_4__ dmdSigInfo_5__ cprSigInfo_6__ demandInfo_7__ bitfield_8__ lfInfo_9__
             tagSig_10__ := info in
          Mk_IdInfo ruleInfo_1__ realUnfoldingInfo_2__ inlinePragInfo_3__ occInfo_4__
                    dmdSigInfo_5__ cprSigInfo_6__ (lazifyDmd dmd) bitfield_8__ lfInfo_9__
                    tagSig_10__).

#[global] Definition floatifyDemandInfo : IdInfo -> option IdInfo :=
  fun '((Mk_IdInfo _ _ _ _ _ _ dmd _ _ _ as info)) =>
    Some (let 'Mk_IdInfo ruleInfo_1__ realUnfoldingInfo_2__ inlinePragInfo_3__
             occInfo_4__ dmdSigInfo_5__ cprSigInfo_6__ demandInfo_7__ bitfield_8__ lfInfo_9__
             tagSig_10__ := info in
          Mk_IdInfo ruleInfo_1__ realUnfoldingInfo_2__ inlinePragInfo_3__ occInfo_4__
                    dmdSigInfo_5__ cprSigInfo_6__ (floatifyDmd dmd) bitfield_8__ lfInfo_9__
                    tagSig_10__).

#[global] Definition zapUsageInfo : IdInfo -> option IdInfo :=
  fun info =>
    Some (let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__
             occInfo_3__ dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__
             tagSig_9__ := info in
          Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
                    dmdSigInfo_4__ cprSigInfo_5__ (zapUsageDemand (demandInfo info)) bitfield_7__
                    lfInfo_8__ tagSig_9__).

#[global] Definition zapUsageEnvInfo : IdInfo -> option IdInfo :=
  fun info =>
    if hasDemandEnvSig (dmdSigInfo info) : bool
    then Some (let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__
                  occInfo_3__ dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__
                  tagSig_9__ := info in
               Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
                         (zapDmdEnvSig (dmdSigInfo info)) cprSigInfo_5__ demandInfo_6__ bitfield_7__
                         lfInfo_8__ tagSig_9__) else
    None.

#[global] Definition zapUsedOnceInfo : IdInfo -> option IdInfo :=
  fun info =>
    Some (let 'Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__
             occInfo_3__ dmdSigInfo_4__ cprSigInfo_5__ demandInfo_6__ bitfield_7__ lfInfo_8__
             tagSig_9__ := info in
          Mk_IdInfo ruleInfo_0__ realUnfoldingInfo_1__ inlinePragInfo_2__ occInfo_3__
                    (zapUsedOnceSig (dmdSigInfo info)) cprSigInfo_5__ (zapUsedOnceDemand (demandInfo
                                                                                          info)) bitfield_7__ lfInfo_8__
                    tagSig_9__).

#[global] Definition zapFragileUnfolding : Unfolding -> Unfolding :=
  fun unf => if isEvaldUnfolding unf : bool then evaldUnfolding else noUnfolding.

#[global] Definition zapFragileInfo : IdInfo -> option IdInfo :=
  fun '((Mk_IdInfo _ unf _ occ _ _ _ _ _ _ as info)) =>
    let new_unf := zapFragileUnfolding unf in
    GHC.Prim.seq new_unf (Some (setOccInfo (setUnfoldingInfo (setRuleInfo info
                                                                          emptyRuleInfo) new_unf)
                                           (BasicTypes.zapFragileOcc occ))).

#[global] Definition zapTailCallInfo : IdInfo -> option IdInfo :=
  fun info =>
    let 'occ := occInfo info in
    let safe_occ :=
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
      end in
    if BasicTypes.isAlwaysTailCalled occ : bool
    then Some (setOccInfo info safe_occ) else
    None.

#[global] Definition zapCallArityInfo : IdInfo -> IdInfo :=
  fun info => setCallArityInfo info #0.

(* Skipping definition `Core.ppr_id_scope' *)

#[global] Definition varMultMaybe : Var -> option Mult :=
  fun v => Some (varMult v).

#[global] Definition setVarUnique : Var -> Unique.Unique -> Var :=
  fun var uniq =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__
       id_details_5__ id_info_6__ := var in
    Mk_Id (Name.setNameUnique (varName var) uniq) uniq varType_2__ varMult_3__
          idScope_4__ id_details_5__ id_info_6__.

#[global] Definition setVarName : Var -> Name.Name -> Var :=
  fun var new_name =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__
       id_details_5__ id_info_6__ := var in
    Mk_Id new_name (Unique.getUnique new_name) varType_2__ varMult_3__ idScope_4__
          id_details_5__ id_info_6__.

#[global] Definition setVarType : Var -> Type_ -> Var :=
  fun id ty =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__
       id_details_5__ id_info_6__ := id in
    Mk_Id varName_0__ realUnique_1__ ty varMult_3__ idScope_4__ id_details_5__
          id_info_6__.

#[global] Definition updateVarType : (Type_ -> Type_) -> Var -> Var :=
  fun upd var =>
    let result :=
      let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__
         id_details_5__ id_info_6__ := var in
      Mk_Id varName_0__ realUnique_1__ (upd (varType var)) varMult_3__ idScope_4__
            id_details_5__ id_info_6__ in
    match var with
    | Mk_Id _ _ _ _ _ details _ => result
    end.

#[global] Definition updateVarTypeM {m : Type -> Type} `{GHC.Base.Monad m}
   : (Type_ -> m Type_) -> Var -> m Var :=
  fun upd var =>
    let result :=
      upd (varType var) GHC.Base.>>=
      (fun ty' =>
         GHC.Base.return_ (let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__
                              idScope_4__ id_details_5__ id_info_6__ := var in
                           Mk_Id varName_0__ realUnique_1__ ty' varMult_3__ idScope_4__ id_details_5__
                                 id_info_6__)) in
    match var with
    | Mk_Id _ _ _ _ _ details _ => result
    end.

#[global] Definition isInvisibleForAllTyFlag : ForAllTyFlag -> bool :=
  fun arg_0__ => match arg_0__ with | Invisible _ => true | Required => false end.

#[global] Definition isVisibleForAllTyFlag : ForAllTyFlag -> bool :=
  fun af => negb (isInvisibleForAllTyFlag af).

#[global] Definition isInferredForAllTyFlag : ForAllTyFlag -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Invisible InferredSpec => true
    | _ => false
    end.

#[global] Definition isSpecifiedForAllTyFlag : ForAllTyFlag -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Invisible SpecifiedSpec => true
    | _ => false
    end.

Axiom coreTyLamForAllTyFlag : ForAllTyFlag.

#[global] Definition invisArg : BasicTypes.TypeOrConstraint -> FunTyFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | BasicTypes.TypeLike => FTF_C_T
    | BasicTypes.ConstraintLike => FTF_C_C
    end.

#[global] Definition visArg : BasicTypes.TypeOrConstraint -> FunTyFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | BasicTypes.TypeLike => FTF_T_T
    | BasicTypes.ConstraintLike => FTF_T_C
    end.

#[global] Definition mkFunTyFlag
   : BasicTypes.TypeOrConstraint -> BasicTypes.TypeOrConstraint -> FunTyFlag :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | BasicTypes.TypeLike, torc => visArg torc
    | BasicTypes.ConstraintLike, torc => invisArg torc
    end.

#[global] Definition visArgTypeLike : FunTyFlag :=
  FTF_T_T.

#[global] Definition visArgConstraintLike : FunTyFlag :=
  FTF_T_C.

#[global] Definition invisArgTypeLike : FunTyFlag :=
  FTF_C_T.

#[global] Definition invisArgConstraintLike : FunTyFlag :=
  FTF_C_C.

#[global] Definition isVisibleFunArg : FunTyFlag -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FTF_T_T => true
    | FTF_T_C => true
    | _ => false
    end.

#[global] Definition isInvisibleFunArg : FunTyFlag -> bool :=
  fun af => negb (isVisibleFunArg af).

#[global] Definition isFUNArg : FunTyFlag -> bool :=
  fun arg_0__ => match arg_0__ with | FTF_T_T => true | _ => false end.

#[global] Definition funTyFlagArgTypeOrConstraint
   : FunTyFlag -> BasicTypes.TypeOrConstraint :=
  fun arg_0__ =>
    match arg_0__ with
    | FTF_T_T => BasicTypes.TypeLike
    | FTF_T_C => BasicTypes.TypeLike
    | _ => BasicTypes.ConstraintLike
    end.

#[global] Definition funTyFlagResultTypeOrConstraint
   : FunTyFlag -> BasicTypes.TypeOrConstraint :=
  fun arg_0__ =>
    match arg_0__ with
    | FTF_T_T => BasicTypes.TypeLike
    | FTF_C_T => BasicTypes.TypeLike
    | _ => BasicTypes.ConstraintLike
    end.

#[global] Definition tyVarSpecToBinder {a : Type}
   : VarBndr a Specificity -> VarBndr a ForAllTyFlag :=
  fun '(Bndr tv vis) => Bndr tv (Invisible vis).

#[global] Definition tyVarSpecToBinders {a : Type}
   : list (VarBndr a Specificity) -> list (VarBndr a ForAllTyFlag) :=
  GHC.Base.map tyVarSpecToBinder.

#[global] Definition tyVarReqToBinder {a : Type}
   : VarBndr a unit -> VarBndr a ForAllTyFlag :=
  fun '(Bndr tv _) => Bndr tv Required.

#[global] Definition tyVarReqToBinders {a : Type}
   : list (VarBndr a unit) -> list (VarBndr a ForAllTyFlag) :=
  GHC.Base.map tyVarReqToBinder.

#[global] Definition isVisibleForAllTyBinder : ForAllTyBinder -> bool :=
  fun '(Bndr _ vis) => isVisibleForAllTyFlag vis.

#[global] Definition isInvisibleForAllTyBinder : ForAllTyBinder -> bool :=
  fun '(Bndr _ vis) => isInvisibleForAllTyFlag vis.

#[global] Definition binderVar {tv : Type} {argf : Type}
   : VarBndr tv argf -> tv :=
  fun '(Bndr v _) => v.

#[global] Definition binderVars {tv : Type} {argf : Type}
   : list (VarBndr tv argf) -> list tv :=
  fun tvbs => GHC.Base.map binderVar tvbs.

#[global] Definition binderFlag {tv : Type} {argf : Type}
   : VarBndr tv argf -> argf :=
  fun '(Bndr _ argf) => argf.

#[global] Definition binderFlags {tv : Type} {argf : Type}
   : list (VarBndr tv argf) -> list argf :=
  fun tvbs => GHC.Base.map binderFlag tvbs.

#[global] Definition binderType {argf : Type} : VarBndr TyCoVar argf -> Type_ :=
  fun '(Bndr tv _) => varType tv.

#[global] Definition isTyVarBinder {vis : Type} : VarBndr TyCoVar vis -> bool :=
  fun '(Bndr tcv _) => isTyVar tcv.

#[global] Definition mkForAllTyBinder {vis : Type}
   : vis -> TyCoVar -> VarBndr TyCoVar vis :=
  fun vis var => Bndr var vis.

#[global] Definition mkTyVarBinder {vis : Type}
   : vis -> TyVar -> VarBndr TyVar vis :=
  fun vis var => Bndr var vis.

#[global] Definition mkForAllTyBinders {vis : Type}
   : vis -> list TyCoVar -> list (VarBndr TyCoVar vis) :=
  fun vis => GHC.Base.map (mkForAllTyBinder vis).

#[global] Definition mkTyVarBinders {vis : Type}
   : vis -> list TyVar -> list (VarBndr TyVar vis) :=
  fun vis => GHC.Base.map (mkTyVarBinder vis).

#[global] Definition mapVarBndr {var : Type} {var' : Type} {flag : Type}
   : (var -> var') -> VarBndr var flag -> VarBndr var' flag :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Bndr v fl => Bndr (f v) fl
    end.

#[global] Definition mapVarBndrs {var : Type} {var' : Type} {flag : Type}
   : (var -> var') -> list (VarBndr var flag) -> list (VarBndr var' flag) :=
  fun f => GHC.Base.map (mapVarBndr f).

#[global] Definition isInvisiblePiTyBinder : PiTyBinder -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Named (Bndr _ vis) => isInvisibleForAllTyFlag vis
    | Anon _ af => isInvisibleFunArg af
    end.

#[global] Definition isVisiblePiTyBinder : PiTyBinder -> bool :=
  negb GHC.Base.∘ isInvisiblePiTyBinder.

#[global] Definition isNamedPiTyBinder : PiTyBinder -> bool :=
  fun arg_0__ => match arg_0__ with | Named _ => true | Anon _ _ => false end.

#[global] Definition namedPiTyBinder_maybe : PiTyBinder -> option TyCoVar :=
  fun arg_0__ =>
    match arg_0__ with
    | Named tv => Some (binderVar tv)
    | _ => None
    end.

#[global] Definition isAnonPiTyBinder : PiTyBinder -> bool :=
  fun arg_0__ => match arg_0__ with | Named _ => false | Anon _ _ => true end.

#[global] Definition anonPiTyBinderType_maybe : PiTyBinder -> option Type_ :=
  fun arg_0__ =>
    match arg_0__ with
    | Named _ => None
    | Anon ty _ => Some (scaledThing ty)
    end.

#[global] Definition isTyBinder : PiTyBinder -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Named bnd => isTyVarBinder bnd
    | _ => true
    end.

#[global] Definition piTyBinderType : PiTyBinder -> Type_ :=
  fun arg_0__ =>
    match arg_0__ with
    | Named (Bndr tv _) => varType tv
    | Anon ty _ => scaledThing ty
    end.

#[global] Definition tyVarName : TyVar -> Name.Name :=
  varName.

#[global] Definition tyVarKind : TyVar -> Kind :=
  varType.

#[global] Definition setTyVarUnique : TyVar -> Unique.Unique -> TyVar :=
  setVarUnique.

#[global] Definition setTyVarName : TyVar -> Name.Name -> TyVar :=
  setVarName.

#[global] Definition setTyVarKind : TyVar -> Kind -> TyVar :=
  fun tv k =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__
       id_details_5__ id_info_6__ := tv in
    Mk_Id varName_0__ realUnique_1__ k varMult_3__ idScope_4__ id_details_5__
          id_info_6__.

#[global] Definition updateTyVarKind : (Kind -> Kind) -> TyVar -> TyVar :=
  fun update tv =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__
       id_details_5__ id_info_6__ := tv in
    Mk_Id varName_0__ realUnique_1__ (update (tyVarKind tv)) varMult_3__ idScope_4__
          id_details_5__ id_info_6__.

#[global] Definition updateTyVarKindM {m : Type -> Type} `{GHC.Base.Monad m}
   : (Kind -> m Kind) -> TyVar -> m TyVar :=
  fun update tv =>
    update (tyVarKind tv) GHC.Base.>>=
    (fun k' =>
       GHC.Base.return_ (let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__
                            idScope_4__ id_details_5__ id_info_6__ := tv in
                         Mk_Id varName_0__ realUnique_1__ k' varMult_3__ idScope_4__ id_details_5__
                               id_info_6__)).

(* Skipping definition `Core.mkTyVar' *)

(* Skipping definition `Core.mkTcTyVar' *)

(* Skipping definition `Core.tcTyVarDetails' *)

(* Skipping definition `Core.setTcTyVarDetails' *)

#[global] Definition idInfo `{Util.HasDebugCallStack} : Id -> IdInfo :=
  fun '(Mk_Id _ _ _ _ _ _ info) => info.

#[global] Definition idDetails : Id -> IdDetails :=
  fun '(Mk_Id _ _ _ _ _ details _) => details.

Axiom mkGlobalVar : IdDetails -> Name.Name -> Type_ -> IdInfo -> Id.

#[global] Definition mk_id
   : Name.Name -> Mult -> Type_ -> IdScope -> IdDetails -> IdInfo -> Id :=
  fun name w ty scope details info =>
    Mk_Id name (Name.nameUnique name) ty w scope details info.

#[global] Definition mkLocalVar
   : IdDetails -> Name.Name -> Mult -> Type_ -> IdInfo -> Id :=
  fun details name w ty info =>
    mk_id name w ty (LocalId NotExported) details info.

(* Skipping definition `Core.mkCoVar' *)

Axiom mkExportedLocalVar : IdDetails -> Name.Name -> Type_ -> IdInfo -> Id.

#[global] Definition lazySetIdInfo : Id -> IdInfo -> Var :=
  fun id info =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__
       id_details_5__ id_info_6__ := id in
    Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__
          id_details_5__ info.

#[global] Definition setIdDetails : Id -> IdDetails -> Id :=
  fun id details =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__
       id_details_5__ id_info_6__ := id in
    Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__ details
          id_info_6__.

(* Skipping definition `Core.globaliseId' *)

(* Skipping definition `Core.setIdExported' *)

(* Skipping definition `Core.setIdNotExported' *)

#[global] Definition updateIdTypeButNotMult : (Type_ -> Type_) -> Id -> Id :=
  fun f id =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__
       id_details_5__ id_info_6__ := id in
    Mk_Id varName_0__ realUnique_1__ (f (varType id)) varMult_3__ idScope_4__
          id_details_5__ id_info_6__.

Axiom updateIdTypeAndMult : (Type_ -> Type_) -> Id -> Id.

Axiom updateIdTypeAndMultM : forall {m : Type -> Type},
                             forall `{GHC.Base.Monad m}, (Type_ -> m Type_) -> Id -> m Id.

#[global] Definition setIdMult : Id -> Mult -> Id :=
  fun id r =>
    if isId id : bool
    then let 'Mk_Id varName_0__ realUnique_1__ varType_2__ varMult_3__ idScope_4__
            id_details_5__ id_info_6__ := id in
         Mk_Id varName_0__ realUnique_1__ varType_2__ r idScope_4__ id_details_5__
               id_info_6__ else
    Panic.pprPanic (GHC.Base.hs_string__ "setIdMult") (GHC.Base.mappend
                                                       Panic.someSDoc Panic.someSDoc).

#[global] Definition isTcTyVar : Var -> bool :=
  fun arg_0__ => false.

#[global] Definition isCoVar : Var -> bool :=
  fun '(Mk_Id _ _ _ _ _ details _) => isCoVarDetails details.

#[global] Definition isTyCoVar : Var -> bool :=
  fun v => orb (isTyVar v) (isCoVar v).

#[global] Definition isNonCoVarId : Var -> bool :=
  fun '(Mk_Id _ _ _ _ _ details _) => negb (isCoVarDetails details).

#[global] Definition isLocalId : Var -> bool :=
  fun v => Unique.isLocalUnique (varUnique v).

#[global] Definition isLocalId_maybe : Var -> option ExportFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ _ (LocalId ef) _ _ => Some ef
    | _ => None
    end.

#[global] Definition isGlobalId : Var -> bool :=
  fun v => negb (Unique.isLocalUnique (varUnique v)).

#[global] Definition isLocalVar : Var -> bool :=
  fun v => negb (isGlobalId v).

#[global] Definition mustHaveLocalBinding : Var -> bool :=
  fun var => isLocalVar var.

Axiom isExportedId : Var -> bool.

#[global] Definition emptyVarSet : VarSet :=
  UniqSet.emptyUniqSet.

#[global] Definition emptyInScopeSet : InScopeSet :=
  InScope emptyVarSet.

#[global] Definition getInScopeVars : InScopeSet -> VarSet :=
  fun '(InScope vs) => vs.

#[global] Definition mkInScopeSet : VarSet -> InScopeSet :=
  fun in_scope => InScope in_scope.

#[global] Definition mkDVarEnv {a : Type} : list (Var * a)%type -> DVarEnv a :=
  UniqFM.listToUFM.

#[global] Definition mkVarEnv {a : Type} : list (Var * a)%type -> VarEnv a :=
  UniqFM.listToUFM.

#[global] Definition mkDVarSet : list Var -> DVarSet :=
  UniqSet.mkUniqSet.

#[global] Definition mkVarSet : list Var -> VarSet :=
  UniqSet.mkUniqSet.

#[global] Definition mkInScopeSetList : list Var -> InScopeSet :=
  fun vs => InScope (mkVarSet vs).

#[global] Definition extendDVarEnv {a : Type}
   : DVarEnv a -> Var -> a -> DVarEnv a :=
  UniqFM.addToUFM.

#[global] Definition extendVarEnv {a : Type}
   : VarEnv a -> Var -> a -> VarEnv a :=
  UniqFM.addToUFM.

#[global] Definition extendDVarEnvList {a : Type}
   : DVarEnv a -> list (Var * a)%type -> DVarEnv a :=
  UniqFM.addListToUFM.

#[global] Definition extendVarEnvList {a : Type}
   : VarEnv a -> list (Var * a)%type -> VarEnv a :=
  UniqFM.addListToUFM.

#[global] Definition extendDVarEnv_C {a : Type}
   : (a -> a -> a) -> DVarEnv a -> Var -> a -> DVarEnv a :=
  UniqFM.addToUFM_C.

#[global] Definition extendVarEnv_Acc {a : Type} {b : Type}
   : (a -> b -> b) -> (a -> b) -> VarEnv b -> Var -> a -> VarEnv b :=
  UniqFM.addToUFM_Acc.

#[global] Definition extendVarEnv_C {a : Type}
   : (a -> a -> a) -> VarEnv a -> Var -> a -> VarEnv a :=
  UniqFM.addToUFM_C.

#[global] Definition extendVarSet : VarSet -> Var -> VarSet :=
  UniqSet.addOneToUniqSet.

#[global] Definition extendInScopeSet : InScopeSet -> Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope, v => InScope (extendVarSet in_scope v)
    end.

#[global] Definition extendInScopeSetList
   : InScopeSet -> list Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope, vs =>
        InScope (Data.Foldable.foldl' extendVarSet in_scope vs)
    end.

#[global] Definition unionVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.unionUniqSets.

#[global] Definition extendInScopeSetSet : InScopeSet -> VarSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope, vs => InScope (unionVarSet in_scope vs)
    end.

#[global] Definition alterDVarEnv {a : Type}
   : (option a -> option a) -> DVarEnv a -> Var -> DVarEnv a :=
  UniqFM.alterUFM.

#[global] Definition alterVarEnv {a : Type}
   : (option a -> option a) -> VarEnv a -> Var -> VarEnv a :=
  UniqFM.alterUFM.

#[global] Definition delDVarEnv {a : Type} : DVarEnv a -> Var -> DVarEnv a :=
  UniqFM.delFromUFM.

#[global] Definition delVarEnv {a : Type} : VarEnv a -> Var -> VarEnv a :=
  UniqFM.delFromUFM.

#[global] Definition delDVarEnvList {a : Type}
   : DVarEnv a -> list Var -> DVarEnv a :=
  UniqFM.delListFromUFM.

#[global] Definition delVarEnvList {a : Type}
   : VarEnv a -> list Var -> VarEnv a :=
  UniqFM.delListFromUFM.

#[global] Definition delDVarSet : DVarSet -> Var -> DVarSet :=
  UniqSet.delOneFromUniqSet.

#[global] Definition delVarSet : VarSet -> Var -> VarSet :=
  UniqSet.delOneFromUniqSet.

#[global] Definition delInScopeSet : InScopeSet -> Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope, v => InScope (delVarSet in_scope v)
    end.

#[global] Definition delVarSetByKey : VarSet -> Unique.Unique -> VarSet :=
  UniqSet.delOneFromUniqSet_Directly.

#[global] Definition elemDVarEnv {a : Type} : Var -> DVarEnv a -> bool :=
  UniqFM.elemUFM.

#[global] Definition elemVarEnv {a : Type} : Var -> VarEnv a -> bool :=
  UniqFM.elemUFM.

#[global] Definition elemDVarSet : Var -> DVarSet -> bool :=
  UniqSet.elementOfUniqSet.

#[global] Definition elemVarSet : Var -> VarSet -> bool :=
  UniqSet.elementOfUniqSet.

#[global] Definition elemInScopeSet : Var -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, InScope in_scope => elemVarSet v in_scope
    end.

#[global] Definition lookupDVarEnv {a : Type} : DVarEnv a -> Var -> option a :=
  UniqFM.lookupUFM.

#[global] Definition lookupVarEnv {a : Type} : VarEnv a -> Var -> option a :=
  UniqFM.lookupUFM.

#[global] Definition lookupVarEnv_Directly {a : Type}
   : VarEnv a -> Unique.Unique -> option a :=
  UniqFM.lookupUFM_Directly.

#[global] Definition lookupVarEnv_NF {a} `{_ : HsToCoq.Err.Default a} (env
    : VarEnv a) id
   : a :=
  match lookupVarEnv env id with
  | Some xx => xx
  | None => HsToCoq.Err.default
  end.

#[global] Definition lookupVarSet : VarSet -> Var -> option Var :=
  UniqSet.lookupUniqSet.

#[global] Definition lookupInScope : InScopeSet -> Var -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope, v => lookupVarSet in_scope v
    end.

#[global] Definition lookupVarSetByName : VarSet -> Name.Name -> option Var :=
  fun set name => UniqSet.lookupUniqSet_Directly set (Unique.getUnique name).

#[global] Definition lookupVarSet_Directly
   : VarSet -> Unique.Unique -> option Var :=
  UniqSet.lookupUniqSet_Directly.

#[global] Definition lookupInScope_Directly
   : InScopeSet -> Unique.Unique -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope, uniq => lookupVarSet_Directly in_scope uniq
    end.

#[global] Definition unionInScope : InScopeSet -> InScopeSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope s1, InScope s2 => InScope (unionVarSet s1 s2)
    end.

#[global] Definition isEmptyVarSet : VarSet -> bool :=
  UniqSet.isEmptyUniqSet.

#[global] Definition minusVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.minusUniqSet.

#[global] Definition subVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => isEmptyVarSet (minusVarSet s1 s2).

#[global] Definition varSetInScope : VarSet -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | vars, InScope s1 => subVarSet vars s1
    end.

Axiom uniqAway : InScopeSet -> Var -> Var.

#[global] Definition unsafeGetFreshLocalUnique : InScopeSet -> Unique.Unique :=
  fun '(InScope set) =>
    match Data.IntMap.Internal.lookupLT (Unique.getKey Unique.maxLocalUnique)
            (UniqFM.ufmToIntMap (UniqSet.getUniqSet set)) with
    | Some (pair uniq _) =>
        let uniq' := Unique.mkLocalUnique uniq in
        if negb (Unique.ltUnique uniq' Unique.minLocalUnique) : bool
        then Unique.incrUnique uniq' else
        Unique.minLocalUnique
    | _ => Unique.minLocalUnique
    end.

#[global] Definition uniqAway' : InScopeSet -> Var -> Var :=
  fun in_scope var => setVarUnique var (unsafeGetFreshLocalUnique in_scope).

#[global] Definition emptyVarEnv {a : Type} : VarEnv a :=
  UniqFM.emptyUFM.

#[global] Definition mkRnEnv2 : InScopeSet -> RnEnv2 :=
  fun vars => RV2 emptyVarEnv emptyVarEnv vars.

#[global] Definition extendRnInScopeSetList : RnEnv2 -> list Var -> RnEnv2 :=
  fun env vs =>
    if Data.Foldable.null vs : bool then env else
    let 'RV2 envL_0__ envR_1__ in_scope_2__ := env in
    RV2 envL_0__ envR_1__ (extendInScopeSetList (in_scope env) vs).

#[global] Definition rnInScope : Var -> RnEnv2 -> bool :=
  fun x env => elemInScopeSet x (in_scope env).

#[global] Definition rnInScopeSet : RnEnv2 -> InScopeSet :=
  in_scope.

#[global] Definition rnEnvL : RnEnv2 -> VarEnv Var :=
  envL.

#[global] Definition rnEnvR : RnEnv2 -> VarEnv Var :=
  envR.

#[global] Definition rnBndr2_var
   : RnEnv2 -> Var -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | RV2 envL envR in_scope, bL, bR =>
        let new_b :=
          if negb (elemInScopeSet bR in_scope) : bool then bR else
          if negb (elemInScopeSet bL in_scope) : bool
          then setVarUnique bR (varUnique bL) else
          uniqAway' in_scope bR in
        pair (RV2 (extendVarEnv envL bL new_b) (extendVarEnv envR bR new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

#[global] Definition rnBndr2 : RnEnv2 -> Var -> Var -> RnEnv2 :=
  fun env bL bR => Data.Tuple.fst (rnBndr2_var env bL bR).

#[global] Definition rnBndrs2 : RnEnv2 -> list Var -> list Var -> RnEnv2 :=
  fun env bsL bsR => Util.foldl2 rnBndr2 env bsL bsR.

#[global] Definition rnBndrL : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bL =>
        let new_b := uniqAway in_scope bL in
        pair (RV2 (extendVarEnv envL bL new_b) envR (extendInScopeSet in_scope new_b))
             new_b
    end.

#[global] Definition rnBndrR : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bR =>
        let new_b := uniqAway in_scope bR in
        pair (RV2 envL (extendVarEnv envR bR new_b) (extendInScopeSet in_scope new_b))
             new_b
    end.

#[global] Definition rnEtaL : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bL =>
        let new_b := uniqAway in_scope bL in
        pair (RV2 (extendVarEnv envL bL new_b) (extendVarEnv envR new_b new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

#[global] Definition rnEtaR : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bR =>
        let new_b := uniqAway in_scope bR in
        pair (RV2 (extendVarEnv envL new_b new_b) (extendVarEnv envR bR new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

#[global] Definition delBndrL : RnEnv2 -> Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 env _ in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 (delVarEnv env v) envR_3__ (extendInScopeSet in_scope v)
    end.

#[global] Definition delBndrR : RnEnv2 -> Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 _ env in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 envL_2__ (delVarEnv env v) (extendInScopeSet in_scope v)
    end.

#[global] Definition delBndrsL : RnEnv2 -> list Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 env _ in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 (delVarEnvList env v) envR_3__ (extendInScopeSetList in_scope v)
    end.

#[global] Definition delBndrsR : RnEnv2 -> list Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 _ env in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 envL_2__ (delVarEnvList env v) (extendInScopeSetList in_scope v)
    end.

#[global] Definition rnOccL : RnEnv2 -> Var -> Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => Maybes.orElse (lookupVarEnv env v) v
    end.

#[global] Definition rnOccR : RnEnv2 -> Var -> Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => Maybes.orElse (lookupVarEnv env v) v
    end.

#[global] Definition rnOccL_maybe : RnEnv2 -> Var -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => lookupVarEnv env v
    end.

#[global] Definition rnOccR_maybe : RnEnv2 -> Var -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => lookupVarEnv env v
    end.

#[global] Definition inRnEnvL : RnEnv2 -> Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => elemVarEnv v env
    end.

#[global] Definition inRnEnvR : RnEnv2 -> Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => elemVarEnv v env
    end.

#[global] Definition anyVarSet : (Var -> bool) -> VarSet -> bool :=
  UniqSet.uniqSetAny.

#[global] Definition isEmptyVarEnv {a : Type} : VarEnv a -> bool :=
  UniqFM.isNullUFM.

#[global] Definition anyInRnEnvR : RnEnv2 -> VarSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, vs =>
        if isEmptyVarEnv env : bool then false else
        anyVarSet (GHC.Prim.rightSection elemVarEnv env) vs
    end.

#[global] Definition lookupRnInScope : RnEnv2 -> Var -> Var :=
  fun env v => Maybes.orElse (lookupInScope (in_scope env) v) v.

#[global] Definition nukeRnEnvL : RnEnv2 -> RnEnv2 :=
  fun '(RV2 envL_0__ envR_1__ in_scope_2__) =>
    RV2 emptyVarEnv envR_1__ in_scope_2__.

#[global] Definition nukeRnEnvR : RnEnv2 -> RnEnv2 :=
  fun '(RV2 envL_0__ envR_1__ in_scope_2__) =>
    RV2 envL_0__ emptyVarEnv in_scope_2__.

#[global] Definition rnSwap : RnEnv2 -> RnEnv2 :=
  fun '(RV2 envL envR in_scope) => RV2 envR envL in_scope.

#[global] Definition emptyTidyEnv : TidyEnv :=
  pair OccName.emptyTidyOccEnv emptyVarEnv.

#[global] Definition mkEmptyTidyEnv : OccName.TidyOccEnv -> TidyEnv :=
  fun occ_env => pair occ_env emptyVarEnv.

#[global] Definition delTidyEnvList : TidyEnv -> list Var -> TidyEnv :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair occ_env var_env, vs =>
        let var_env' := delVarEnvList var_env vs in
        let occ_env' :=
          OccName.delTidyOccEnvList occ_env (GHC.Base.map (OccName.occNameFS GHC.Base.∘
                                                           Name.getOccName) vs) in
        pair occ_env' var_env'
    end.

#[global] Definition elemVarEnvByKey {a : Type}
   : Unique.Unique -> VarEnv a -> bool :=
  UniqFM.elemUFM_Directly.

#[global] Definition disjointVarEnv {a : Type} : VarEnv a -> VarEnv a -> bool :=
  UniqFM.disjointUFM.

#[global] Definition plusVarEnv_C {a : Type}
   : (a -> a -> a) -> VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM_C.

#[global] Definition plusVarEnv_CD {a : Type}
   : (a -> a -> a) -> VarEnv a -> a -> VarEnv a -> a -> VarEnv a :=
  UniqFM.plusUFM_CD.

#[global] Definition plusMaybeVarEnv_C {a : Type}
   : (a -> a -> option a) -> VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusMaybeUFM_C.

#[global] Definition minusVarEnv {a : Type} {b : Type}
   : VarEnv a -> VarEnv b -> VarEnv a :=
  UniqFM.minusUFM.

#[global] Definition plusVarEnv {a : Type} : VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM.

#[global] Definition plusVarEnvList {a : Type} : list (VarEnv a) -> VarEnv a :=
  UniqFM.plusUFMList.

#[global] Definition filterVarEnv {a : Type}
   : (a -> bool) -> VarEnv a -> VarEnv a :=
  UniqFM.filterUFM.

(* Skipping definition `Core.anyVarEnv' *)

#[global] Definition lookupWithDefaultVarEnv {a : Type}
   : VarEnv a -> a -> Var -> a :=
  UniqFM.lookupWithDefaultUFM.

#[global] Definition mapVarEnv {a : Type} {b : Type}
   : (a -> b) -> VarEnv a -> VarEnv b :=
  UniqFM.mapUFM.

#[global] Definition mkVarEnv_Directly {a : Type}
   : list (Unique.Unique * a)%type -> VarEnv a :=
  UniqFM.listToUFM_Directly.

#[global] Definition unitDVarEnv {a : Type} : Var -> a -> DVarEnv a :=
  UniqFM.unitUFM.

#[global] Definition unitVarEnv {a : Type} : Var -> a -> VarEnv a :=
  UniqFM.unitUFM.

#[global] Definition partitionVarEnv {a : Type}
   : (a -> bool) -> VarEnv a -> (VarEnv a * VarEnv a)%type :=
  UniqFM.partitionUFM.

(* Skipping definition `Core.varEnvDomain' *)

#[global] Definition nonDetStrictFoldVarEnv_Directly {a : Type} {r : Type}
   : (Unique.Unique -> a -> r -> r) -> r -> VarEnv a -> r :=
  UniqFM.nonDetStrictFoldUFM_Directly.

#[global] Definition elemVarSetByKey : Unique.Unique -> VarSet -> bool :=
  UniqSet.elemUniqSet_Directly.

#[global] Definition restrictVarEnv {a : Type}
   : VarEnv a -> VarSet -> VarEnv a :=
  fun env vs =>
    let keep :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | u, _ => elemVarSetByKey u vs
        end in
    UniqFM.filterUFM_Directly keep env.

#[global] Definition zipVarEnv {a : Type} : list Var -> list a -> VarEnv a :=
  fun tyvars tys =>
    mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipVarEnv") tyvars tys).

#[global] Definition modifyVarEnv {a : Type}
   : (a -> a) -> VarEnv a -> Var -> VarEnv a :=
  fun mangle_fn env key =>
    match (lookupVarEnv env key) with
    | None => env
    | Some xx => extendVarEnv env key (mangle_fn xx)
    end.

(* Skipping definition `Core.modifyVarEnv_Directly' *)

#[global] Definition emptyDVarEnv {a : Type} : DVarEnv a :=
  UniqFM.emptyUFM.

(* Skipping definition `Core.dVarEnvElts' *)

#[global] Definition minusDVarEnv {a : Type} {a' : Type}
   : DVarEnv a -> DVarEnv a' -> DVarEnv a :=
  UniqFM.minusUFM.

#[global] Definition foldDVarEnv {a : Type} {b : Type}
   : (a -> b -> b) -> b -> DVarEnv a -> b :=
  UniqFM.nonDetFoldUFM.

#[global] Definition nonDetStrictFoldDVarEnv {a : Type} {b : Type}
   : (a -> b -> b) -> b -> DVarEnv a -> b :=
  UniqDFM.nonDetStrictFoldUDFM.

#[global] Definition mapDVarEnv {a : Type} {b : Type}
   : (a -> b) -> DVarEnv a -> DVarEnv b :=
  UniqFM.mapUFM.

#[global] Definition filterDVarEnv {a : Type}
   : (a -> bool) -> DVarEnv a -> DVarEnv a :=
  UniqFM.filterUFM.

#[global] Definition plusDVarEnv {a : Type}
   : DVarEnv a -> DVarEnv a -> DVarEnv a :=
  UniqFM.plusUFM.

#[global] Definition plusDVarEnv_C {a : Type}
   : (a -> a -> a) -> DVarEnv a -> DVarEnv a -> DVarEnv a :=
  UniqFM.plusUFM_C.

#[global] Definition isEmptyDVarEnv {a : Type} : DVarEnv a -> bool :=
  UniqFM.isNullUFM.

#[global] Definition modifyDVarEnv {a : Type}
   : (a -> a) -> DVarEnv a -> Var -> DVarEnv a :=
  fun mangle_fn env key =>
    match (lookupDVarEnv env key) with
    | None => env
    | Some xx => extendDVarEnv env key (mangle_fn xx)
    end.

#[global] Definition partitionDVarEnv {a : Type}
   : (a -> bool) -> DVarEnv a -> (DVarEnv a * DVarEnv a)%type :=
  UniqFM.partitionUFM.

#[global] Definition anyDVarEnv {a : Type} : (a -> bool) -> DVarEnv a -> bool :=
  UniqFM.anyUFM.

#[global] Definition unitDVarSet : Var -> DVarSet :=
  UniqSet.unitUniqSet.

#[global] Definition unitVarSet : Var -> VarSet :=
  UniqSet.unitUniqSet.

#[global] Definition extendDVarSet : DVarSet -> Var -> DVarSet :=
  UniqSet.addOneToUniqSet.

#[global] Definition extendDVarSetList : DVarSet -> list Var -> DVarSet :=
  UniqSet.addListToUniqSet.

#[global] Definition extendVarSetList : VarSet -> list Var -> VarSet :=
  UniqSet.addListToUniqSet.

#[global] Definition intersectVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.intersectUniqSets.

#[global] Definition unionVarSets : list VarSet -> VarSet :=
  UniqSet.unionManyUniqSets.

#[global] Definition delDVarSetList : DVarSet -> list Var -> DVarSet :=
  UniqSet.delListFromUniqSet.

#[global] Definition delVarSetList : VarSet -> list Var -> VarSet :=
  UniqSet.delListFromUniqSet.

#[global] Definition sizeVarSet : VarSet -> nat :=
  UniqSet.sizeUniqSet.

#[global] Definition filterVarSet : (Var -> bool) -> VarSet -> VarSet :=
  UniqSet.filterUniqSet.

(* Skipping definition `Core.partitionVarSet' *)

#[global] Definition mapUnionVarSet {a : Type}
   : (a -> VarSet) -> list a -> VarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionVarSet GHC.Base.∘ get_set) emptyVarSet xs.

#[global] Definition disjointVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => UniqFM.disjointUFM (UniqSet.getUniqSet s1) (UniqSet.getUniqSet s2).

#[global] Definition intersectsVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => negb (disjointVarSet s1 s2).

#[global] Definition allVarSet : (Var -> bool) -> VarSet -> bool :=
  UniqSet.uniqSetAll.

(* Skipping definition `Core.mapVarSet' *)

#[global] Definition nonDetStrictFoldVarSet {a : Type}
   : (Var -> a -> a) -> a -> VarSet -> a :=
  UniqSet.nonDetStrictFoldUniqSet.

#[global] Definition fixVarSet : (VarSet -> VarSet) -> VarSet -> VarSet :=
  HsToCoq.DeferredFix.deferredFix2 (fun fixVarSet
                                    (fn : VarSet -> VarSet)
                                    (vars : VarSet) =>
                                      let new_vars := fn vars in
                                      if subVarSet new_vars vars : bool then vars else
                                      fixVarSet fn new_vars).

#[global] Definition transCloVarSet : (VarSet -> VarSet) -> VarSet -> VarSet :=
  fun fn seeds =>
    let go : VarSet -> VarSet -> VarSet :=
      HsToCoq.DeferredFix.deferredFix1 (fun go (acc candidates : VarSet) =>
                                          let new_vs := minusVarSet (fn candidates) acc in
                                          if isEmptyVarSet new_vs : bool then acc else
                                          go (unionVarSet acc new_vs) new_vs) in
    go seeds seeds.

#[global] Definition seqVarSet : VarSet -> unit :=
  fun s => GHC.Prim.seq s tt.

(* Skipping definition `Core.pluralVarSet' *)

(* Skipping definition `Core.pprVarSet' *)

#[global] Definition dVarSetElems : DVarSet -> list Var :=
  UniqSet.nonDetEltsUniqSet.

#[global] Definition isEmptyDVarSet : DVarSet -> bool :=
  UniqSet.isEmptyUniqSet.

#[global] Definition minusDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqSet.minusUniqSet.

#[global] Definition subDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => isEmptyDVarSet (minusDVarSet s1 s2).

#[global] Definition unionDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqSet.unionUniqSets.

#[global] Definition unionDVarSets : list DVarSet -> DVarSet :=
  UniqSet.unionManyUniqSets.

#[global] Definition mapUnionDVarSet {a : Type}
   : (a -> DVarSet) -> list a -> DVarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionDVarSet GHC.Base.∘ get_set) emptyDVarSet xs.

#[global] Definition intersectDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqSet.intersectUniqSets.

#[global] Definition dVarSetIntersectVarSet : DVarSet -> VarSet -> DVarSet :=
  UniqSet.intersectUniqSets.

#[global] Definition disjointDVarSet :=
  disjointVarSet.

#[global] Definition intersectsDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => negb (disjointDVarSet s1 s2).

#[global] Definition dVarSetMinusVarSet : DVarSet -> VarSet -> DVarSet :=
  UniqSet.minusUniqSet.

#[global] Definition nonDetStrictFoldDVarSet {a : Type}
   : (Var -> a -> a) -> a -> DVarSet -> a :=
  UniqDSet.nonDetStrictFoldUniqDSet.

#[global] Definition anyDVarSet :=
  anyVarSet.

#[global] Definition allDVarSet :=
  allVarSet.

#[global] Definition mapDVarSet {b : Type} {a : Type} `{Unique.Uniquable b}
   : (a -> b) -> UniqSet.UniqSet a -> UniqSet.UniqSet b :=
  UniqDSet.mapUniqDSet.

#[global] Definition filterDVarSet : (Var -> bool) -> DVarSet -> DVarSet :=
  UniqSet.filterUniqSet.

#[global] Definition sizeDVarSet : DVarSet -> nat :=
  UniqSet.sizeUniqSet.

#[global] Definition partitionDVarSet
   : (Var -> bool) -> DVarSet -> (DVarSet * DVarSet)%type :=
  UniqSet.partitionUniqSet.

#[global] Definition seqDVarSet : DVarSet -> unit :=
  fun s => GHC.Prim.seq s tt.

#[global] Definition dVarSetToVarSet : DVarSet -> VarSet :=
  fun x => x.

#[global] Definition transCloDVarSet
   : (DVarSet -> DVarSet) -> DVarSet -> DVarSet :=
  fun fn seeds =>
    let go : DVarSet -> DVarSet -> DVarSet :=
      HsToCoq.DeferredFix.deferredFix1 (fun go (acc candidates : DVarSet) =>
                                          let new_vs := minusDVarSet (fn candidates) acc in
                                          if isEmptyDVarSet new_vs : bool then acc else
                                          go (unionDVarSet acc new_vs) new_vs) in
    go seeds seeds.

(* External variables:
     BranchFlag BranchIndex Branched BuiltInSynFamily CType CoAxBranch CoAxiom
     CoAxiomRule Coercion DataConBoxer Eq ForeignCall Gt Kind Literal Lt None
     PredType PrimOp Some ThetaType Type Type_ Unbranched andb bool comparison cons
     false list mkLitChar mkLitDouble mkLitFloat mkLitIntWrap mkLitString mkLitWord8
     mkLitWordWrap nat negb nil op_zt__ option orb pair size_AnnExpr' snd true tt
     unit BasicTypes.Activation BasicTypes.AlwaysActive BasicTypes.Arity
     BasicTypes.CbvMark BasicTypes.ConTagZ BasicTypes.ConstraintLike
     BasicTypes.DefMethSpec BasicTypes.IAmALoopBreaker BasicTypes.IAmDead
     BasicTypes.InlinePragma BasicTypes.IsInsideLam BasicTypes.JoinArity
     BasicTypes.LeftOrRight BasicTypes.Levity BasicTypes.ManyOccs
     BasicTypes.NoOneShotInfo BasicTypes.NoTailCallInfo BasicTypes.NonRecursive
     BasicTypes.NotInsideLam BasicTypes.OccInfo BasicTypes.OneOcc
     BasicTypes.OneShotInfo BasicTypes.OneShotLam BasicTypes.RecFlag
     BasicTypes.Recursive BasicTypes.RuleName BasicTypes.SourceText
     BasicTypes.TupleSort BasicTypes.TyConFlavour BasicTypes.TypeLike
     BasicTypes.TypeOrConstraint BasicTypes.defaultInlinePragma
     BasicTypes.isAlwaysTailCalled BasicTypes.isStrongLoopBreaker
     BasicTypes.noOccInfo BasicTypes.zapFragileOcc BinNums.N
     BooleanFormula.BooleanFormula ConLike PatSynCon
     RealDataCon Coq.Init.Datatypes.app Coq.Init.Peano.lt
     Coq.Lists.List.flat_map Coq.Lists.List.length Data.Bits.clearBit
     Data.Bits.setBit Data.Bits.testBit Data.Foldable.foldl' Data.Foldable.foldr
     Data.Foldable.null Data.Function.on Data.IntMap.Internal.lookupLT Data.Tuple.fst
     Data.Tuple.uncurry FastString.FastString FieldLabel.FieldLabel
     FieldLabel.FieldLabelEnv GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.compare__
     GHC.Base.fmap__ GHC.Base.map GHC.Base.mappend GHC.Base.max__ GHC.Base.min
     GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zg__ GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____
     GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlzd____
     GHC.Base.op_zlze__ GHC.Base.op_zlze____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.return_ GHC.Char.Char GHC.Core.Rules.Config.RuleOpts
     GHC.Core.TyCo.Subst.Subst GHC.Core.TyCon.RecWalk.RecTcChecker
     GHC.Data.List.Infinite.Infinite GHC.Err.error GHC.Err.head GHC.List.reverse
     GHC.Num.Integer GHC.Num.Word GHC.Num.fromInteger GHC.Num.op_zm__
     GHC.Prim.HasCallStack GHC.Prim.rightSection GHC.Prim.seq GHC.Real.Rational
     GHC.Stg.InferTags.TagSig.TagSig GHC.StgToCmm.Types.LambdaFormInfo
     GHC.Types.Cpr.CprSig GHC.Types.Cpr.topCprSig GHC.Types.Tickish.CoreTickish
     GHC.Types.TyThing.TyThing HsSyn.Boxity HsSyn.ConTag HsSyn.FieldLabelString
     HsSyn.Role HsSyn.SrcStrictness HsSyn.SrcUnpackedness
     HsToCoq.DeferredFix.deferredFix1 HsToCoq.DeferredFix.deferredFix2
     HsToCoq.Err.Build_Default HsToCoq.Err.Default HsToCoq.Err.default
     HsToCoq.Wf.wfFix2 HsToCoq.Wf.wfFix3 Maybes.orElse Module.Module Name.Name
     Name.NamedThing Name.getName Name.getName__ Name.getOccName Name.getOccName__
     Name.nameOccName Name.nameUnique Name.setNameUnique NameEnv.NameEnv
     OccName.HasOccName OccName.OccName OccName.TidyOccEnv OccName.delTidyOccEnvList
     OccName.emptyTidyOccEnv OccName.occNameFS OccName.occName__ Pair.Pair
     Panic.pprPanic Panic.someSDoc Platform.Platform SrcLoc.SrcSpan
     TcType.ConcreteTyVars TcType.noConcreteTyVars UniqDFM.nonDetStrictFoldUDFM
     UniqDSet.mapUniqDSet UniqDSet.nonDetStrictFoldUniqDSet UniqFM.UniqFM
     UniqFM.addListToUFM UniqFM.addToUFM UniqFM.addToUFM_Acc UniqFM.addToUFM_C
     UniqFM.alterUFM UniqFM.anyUFM UniqFM.delFromUFM UniqFM.delListFromUFM
     UniqFM.disjointUFM UniqFM.elemUFM UniqFM.elemUFM_Directly UniqFM.emptyUFM
     UniqFM.filterUFM UniqFM.filterUFM_Directly UniqFM.isNullUFM UniqFM.listToUFM
     UniqFM.listToUFM_Directly UniqFM.lookupUFM UniqFM.lookupUFM_Directly
     UniqFM.lookupWithDefaultUFM UniqFM.mapUFM UniqFM.minusUFM UniqFM.nonDetFoldUFM
     UniqFM.nonDetStrictFoldUFM_Directly UniqFM.partitionUFM UniqFM.plusMaybeUFM_C
     UniqFM.plusUFM UniqFM.plusUFMList UniqFM.plusUFM_C UniqFM.plusUFM_CD
     UniqFM.ufmToIntMap UniqFM.unitUFM UniqSet.UniqSet UniqSet.addListToUniqSet
     UniqSet.addOneToUniqSet UniqSet.delListFromUniqSet UniqSet.delOneFromUniqSet
     UniqSet.delOneFromUniqSet_Directly UniqSet.elemUniqSet_Directly
     UniqSet.elementOfUniqSet UniqSet.emptyUniqSet UniqSet.filterUniqSet
     UniqSet.getUniqSet UniqSet.intersectUniqSets UniqSet.isEmptyUniqSet
     UniqSet.lookupUniqSet UniqSet.lookupUniqSet_Directly UniqSet.minusUniqSet
     UniqSet.mkUniqSet UniqSet.nonDetEltsUniqSet UniqSet.nonDetStrictFoldUniqSet
     UniqSet.partitionUniqSet UniqSet.sizeUniqSet UniqSet.unionManyUniqSets
     UniqSet.unionUniqSets UniqSet.uniqSetAll UniqSet.uniqSetAny UniqSet.unitUniqSet
     Unique.Uniquable Unique.Unique Unique.getKey Unique.getUnique Unique.getUnique__
     Unique.incrUnique Unique.isLocalUnique Unique.ltUnique Unique.maxLocalUnique
     Unique.minLocalUnique Unique.mkLocalUnique Unique.nonDetCmpUnique
     Util.HasDebugCallStack Util.count Util.foldl2 Util.zipEqual
*)
