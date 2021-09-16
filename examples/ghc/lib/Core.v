(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require Import AxiomatizedTypes.
Require BasicTypes.
Require DynFlags.
Require FastString.
Require FieldLabel.
Require GHC.Base.
Require GHC.Num.
Require Module.
Require Name.
Require OccName.
Require Pair.
Require UniqSet.
Require UniqSupply.
Require Unique.
Require Util.
Require BinNat.
Require BinNums.
Require BooleanFormula.
Require Coq.Init.Datatypes.
Require Coq.Init.Peano.
Require Coq.Lists.List.
Require Data.Foldable.
Require Data.Function.
Require Data.Tuple.
Require Datatypes.
Require GHC.Char.
Require GHC.Err.
Require GHC.List.
Require GHC.Prim.
Require GHC.Real.
Require HsToCoq.DeferredFix.
Require HsToCoq.Err.
Require HsToCoq.Wf.
Require Import Literal.
Require Maybes.
Require NameEnv.
Require Panic.
Require SrcLoc.
Require UniqFM.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition VarEnv :=
  UniqFM.UniqFM%type.

Inductive UnfoldingSource : Type :=
  | InlineRhs : UnfoldingSource
  | InlineStable : UnfoldingSource
  | InlineCompulsory : UnfoldingSource.

Inductive UnfoldingGuidance : Type :=
  | UnfWhen (ug_arity : BasicTypes.Arity) (ug_unsat_ok : bool) (ug_boring_ok
    : bool)
   : UnfoldingGuidance
  | UnfIfGoodArgs (ug_args : list nat) (ug_size : nat) (ug_res : nat)
   : UnfoldingGuidance
  | UnfNever : UnfoldingGuidance.

Inductive Unfolding : Type := | NoUnfolding : Unfolding.

Inductive TypeShape : Type :=
  | TsFun : TypeShape -> TypeShape
  | TsProd : list TypeShape -> TypeShape
  | TsUnk : TypeShape.

Inductive TypeOrdering : Type :=
  | TLT : TypeOrdering
  | TEQ : TypeOrdering
  | TEQX : TypeOrdering
  | TGT : TypeOrdering.

Definition TyVarEnv :=
  VarEnv%type.

Inductive TyVarBndr tyvar argf : Type :=
  | TvBndr : tyvar -> argf -> TyVarBndr tyvar argf.

Inductive TyLit : Type :=
  | NumTyLit : GHC.Num.Integer -> TyLit
  | StrTyLit : FastString.FastString -> TyLit.

Definition TyConRepName :=
  Name.Name%type.

Inductive TyConFlavour : Type :=
  | ClassFlavour : TyConFlavour
  | TupleFlavour : BasicTypes.Boxity -> TyConFlavour
  | SumFlavour : TyConFlavour
  | DataTypeFlavour : TyConFlavour
  | NewtypeFlavour : TyConFlavour
  | AbstractTypeFlavour : TyConFlavour
  | DataFamilyFlavour : TyConFlavour
  | OpenTypeFamilyFlavour : TyConFlavour
  | ClosedTypeFamilyFlavour : TyConFlavour
  | TypeSynonymFlavour : TyConFlavour
  | BuiltInTypeFlavour : TyConFlavour
  | PromotedDataConFlavour : TyConFlavour.

Definition TyCoVarEnv :=
  VarEnv%type.

Definition TvSubstEnv :=
  (TyVarEnv Type_)%type.

Inductive TickishScoping : Type :=
  | NoScope : TickishScoping
  | SoftScope : TickishScoping
  | CostCentreScope : TickishScoping.

Inductive TickishPlacement : Type :=
  | PlaceRuntime : TickishPlacement
  | PlaceNonLam : TickishPlacement
  | PlaceCostCentre : TickishPlacement.

Inductive Tickish id : Type :=
  | ProfNote (profNoteCC : CostCentre) (profNoteCount : bool) (profNoteScope
    : bool)
   : Tickish id
  | HpcTick (tickModule : Module.Module) (tickId : nat) : Tickish id
  | Breakpoint (breakpointId : nat) (breakpointFVs : list id) : Tickish id
  | SourceNote (sourceSpan : SrcLoc.RealSrcSpan) (sourceName : GHC.Base.String)
   : Tickish id.

Definition TickBoxId :=
  nat%type.

Inductive TickBoxOp : Type :=
  | TickBox : Module.Module -> TickBoxId -> TickBoxOp.

Inductive Termination r : Type :=
  | Diverges : Termination r
  | ThrowsExn : Termination r
  | Dunno : r -> Termination r.

Inductive StrictnessMark : Type :=
  | MarkedStrict : StrictnessMark
  | NotMarkedStrict : StrictnessMark.

Inductive SrcUnpackedness : Type :=
  | SrcUnpack : SrcUnpackedness
  | SrcNoUnpack : SrcUnpackedness
  | NoSrcUnpack : SrcUnpackedness.

Inductive SrcStrictness : Type :=
  | SrcLazy : SrcStrictness
  | SrcStrict : SrcStrictness
  | NoSrcStrict : SrcStrictness.

Inductive RuleInfo : Type := | EmptyRuleInfo.

Inductive RecTcChecker : Type :=
  | RC : nat -> (NameEnv.NameEnv nat) -> RecTcChecker.

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
  | VoidRep : PrimRep
  | LiftedRep : PrimRep
  | UnliftedRep : PrimRep
  | IntRep : PrimRep
  | WordRep : PrimRep
  | Int64Rep : PrimRep
  | Word64Rep : PrimRep
  | AddrRep : PrimRep
  | FloatRep : PrimRep
  | DoubleRep : PrimRep
  | VecRep : nat -> PrimElemRep -> PrimRep.

Inductive RuntimeRepInfo : Type :=
  | NoRRI : RuntimeRepInfo
  | RuntimeRep : (list Type_ -> list PrimRep) -> RuntimeRepInfo
  | VecCount : nat -> RuntimeRepInfo
  | VecElem : PrimElemRep -> RuntimeRepInfo.

Definition OutType :=
  Type_%type.

Definition OutKind :=
  Kind%type.

Definition OutCoercion :=
  Coercion%type.

Inductive NormaliseStepResult ev : Type :=
  | NS_Done : NormaliseStepResult ev
  | NS_Abort : NormaliseStepResult ev
  | NS_Step : RecTcChecker -> Type_ -> ev -> NormaliseStepResult ev.

Definition LiftCoEnv :=
  (VarEnv Coercion)%type.

Inductive LevityInfo : Type :=
  | NoLevityInfo : LevityInfo
  | NeverLevityPolymorphic : LevityInfo.

Definition KindOrType :=
  Type_%type.

Inductive KillFlags : Type :=
  | Mk_KillFlags (kf_abs : bool) (kf_used_once : bool) (kf_called_once : bool)
   : KillFlags.

Inductive JointDmd s u : Type := | JD (sd : s) (ud : u) : JointDmd s u.

Inductive IsOrphan : Type :=
  | Mk_IsOrphan : IsOrphan
  | NotOrphan : OccName.OccName -> IsOrphan.

Definition InlinePragInfo :=
  BasicTypes.InlinePragma%type.

Inductive Injectivity : Type :=
  | NotInjective : Injectivity
  | Injective : list bool -> Injectivity.

Definition InType :=
  Type_%type.

Definition InKind :=
  Kind%type.

Definition InCoercion :=
  Coercion%type.

Definition IdEnv :=
  VarEnv%type.

Inductive HsSrcBang : Type :=
  | Mk_HsSrcBang
   : BasicTypes.SourceText -> SrcUnpackedness -> SrcStrictness -> HsSrcBang.

Inductive HsImplBang : Type :=
  | HsLazy : HsImplBang
  | HsStrict : HsImplBang
  | HsUnpack : (option Coercion) -> HsImplBang.

Definition FunDep a :=
  (list a * list a)%type%type.

Inductive FamTyConFlav : Type :=
  | DataFamilyTyCon : TyConRepName -> FamTyConFlav
  | OpenSynFamilyTyCon : FamTyConFlav
  | ClosedSynFamilyTyCon : (option (CoAxiom Branched)) -> FamTyConFlav
  | AbstractClosedSynFamilyTyCon : FamTyConFlav
  | BuiltInSynFamTyCon : BuiltInSynFamily -> FamTyConFlav.

Inductive ExportFlag : Type :=
  | NotExported : ExportFlag
  | Exported : ExportFlag.

Inductive IdScope : Type :=
  | GlobalId : IdScope
  | LocalId : ExportFlag -> IdScope.

Inductive ExnStr : Type := | VanStr : ExnStr | Mk_ExnStr : ExnStr.

Inductive Str s : Type := | Lazy : Str s | Mk_Str : ExnStr -> s -> Str s.

Inductive EqRel : Type := | NomEq : EqRel | ReprEq : EqRel.

Definition DefMethInfo :=
  (option (Name.Name * BasicTypes.DefMethSpec Type_)%type)%type.

Definition DVarEnv :=
  UniqFM.UniqFM%type.

Definition DTyVarEnv :=
  DVarEnv%type.

Definition DIdEnv :=
  DVarEnv%type.

Inductive Count : Type := | One : Count | Many : Count.

Inductive Use u : Type := | Abs : Use u | Mk_Use : Count -> u -> Use u.

Definition DmdShell :=
  (JointDmd (Str unit) (Use unit))%type.

Definition CoercionR :=
  Coercion%type.

Definition CoercionP :=
  Coercion%type.

Definition CoercionN :=
  Coercion%type.

Definition KindCoercion :=
  CoercionN%type.

Inductive UnivCoProvenance : Type :=
  | UnsafeCoerceProv : UnivCoProvenance
  | PhantomProv : KindCoercion -> UnivCoProvenance
  | ProofIrrelProv : KindCoercion -> UnivCoProvenance
  | PluginProv : GHC.Base.String -> UnivCoProvenance.

Axiom CoercionHole : Type.

Definition CoVarEnv :=
  VarEnv%type.

Definition CvSubstEnv :=
  (CoVarEnv Coercion)%type.

Definition ClassMinimalDef :=
  (BooleanFormula.BooleanFormula Name.Name)%type.

Inductive CafInfo : Type := | MayHaveCafRefs : CafInfo | NoCafRefs : CafInfo.

Inductive CPRResult : Type :=
  | NoCPR : CPRResult
  | RetProd : CPRResult
  | RetSum : BasicTypes.ConTag -> CPRResult.

Definition DmdResult :=
  (Termination CPRResult)%type.

Definition ArityInfo :=
  BasicTypes.Arity%type.

Inductive UseDmd : Type :=
  | UCall : Count -> UseDmd -> UseDmd
  | UProd : list (Use UseDmd)%type -> UseDmd
  | UHead : UseDmd
  | Used : UseDmd.

Definition ArgUse :=
  (Use UseDmd)%type.

Inductive StrDmd : Type :=
  | HyperStr : StrDmd
  | SCall : StrDmd -> StrDmd
  | SProd : list (Str StrDmd)%type -> StrDmd
  | HeadStr : StrDmd.

Definition ArgStr :=
  (Str StrDmd)%type.

Definition Demand :=
  (JointDmd ArgStr ArgUse)%type.

Definition DmdEnv :=
  (VarEnv Demand)%type.

Definition BothDmdArg :=
  (DmdEnv * Termination unit)%type%type.

Inductive DmdType : Type :=
  | Mk_DmdType : DmdEnv -> list Demand -> DmdResult -> DmdType.

Inductive StrictSig : Type := | Mk_StrictSig : DmdType -> StrictSig.

Inductive IdInfo : Type :=
  | Mk_IdInfo (arityInfo : ArityInfo) (ruleInfo : RuleInfo) (unfoldingInfo
    : Unfolding) (cafInfo : CafInfo) (oneShotInfo : BasicTypes.OneShotInfo)
  (inlinePragInfo : BasicTypes.InlinePragma) (occInfo : BasicTypes.OccInfo)
  (strictnessInfo : StrictSig) (demandInfo : Demand) (callArityInfo : ArityInfo)
  (levityInfo : LevityInfo)
   : IdInfo.

Definition CleanDemand :=
  (JointDmd StrDmd UseDmd)%type.

Inductive ArgFlag : Type :=
  | Required : ArgFlag
  | Specified : ArgFlag
  | Inferred : ArgFlag.

Inductive TyConBndrVis : Type :=
  | NamedTCB : ArgFlag -> TyConBndrVis
  | AnonTCB : TyConBndrVis.

Inductive AlgTyConFlav : Type :=
  | VanillaAlgTyCon : TyConRepName -> AlgTyConFlav
  | UnboxedAlgTyCon : (option TyConRepName) -> AlgTyConFlav
  | ClassTyCon : Class -> TyConRepName -> AlgTyConFlav
  | DataFamInstTyCon : (CoAxiom Unbranched) -> TyCon -> list Type_ -> AlgTyConFlav
with Class : Type :=
  | Mk_Class (classTyCon : TyCon) (className : Name.Name) (classKey
    : Unique.Unique) (classTyVars : list Var%type) (classFunDeps
    : list (FunDep Var%type)) (classBody : ClassBody)
   : Class
with ClassBody : Type :=
  | AbstractClass : ClassBody
  | ConcreteClass (classSCThetaStuff : list PredType) (classSCSels
    : list Var%type) (classATStuff : list ClassATItem) (classOpStuff
    : list (Var%type * DefMethInfo)%type%type) (classMinimalDefStuff
    : ClassMinimalDef)
   : ClassBody
with ClassATItem : Type :=
  | ATI : TyCon -> (option (Type_ * SrcLoc.SrcSpan)%type) -> ClassATItem
with TyCon : Type :=
  | FunTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name) (tyConBinders
    : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConResKind : Kind) (tyConKind
    : Kind) (tyConArity : BasicTypes.Arity) (tcRepName : TyConRepName)
   : TyCon
  | AlgTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name) (tyConBinders
    : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConTyVars : list Var%type)
  (tyConResKind : Kind) (tyConKind : Kind) (tyConArity : BasicTypes.Arity)
  (tcRoles : list Role) (tyConCType : option CType) (algTcGadtSyntax : bool)
  (algTcStupidTheta : list PredType) (algTcRhs : AlgTyConRhs) (algTcFields
    : FieldLabel.FieldLabelEnv) (algTcParent : AlgTyConFlav)
   : TyCon
  | SynonymTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name)
  (tyConBinders : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConTyVars
    : list Var%type) (tyConResKind : Kind) (tyConKind : Kind) (tyConArity
    : BasicTypes.Arity) (tcRoles : list Role) (synTcRhs : Type_) (synIsTau : bool)
  (synIsFamFree : bool)
   : TyCon
  | FamilyTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name)
  (tyConBinders : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConTyVars
    : list Var%type) (tyConResKind : Kind) (tyConKind : Kind) (tyConArity
    : BasicTypes.Arity) (famTcResVar : option Name.Name) (famTcFlav : FamTyConFlav)
  (famTcParent : option Class) (famTcInj : Injectivity)
   : TyCon
  | PrimTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name) (tyConBinders
    : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConResKind : Kind) (tyConKind
    : Kind) (tyConArity : BasicTypes.Arity) (tcRoles : list Role) (isUnlifted
    : bool) (primRepName : option TyConRepName)
   : TyCon
  | PromotedDataCon (tyConUnique : Unique.Unique) (tyConName : Name.Name)
  (tyConBinders : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConResKind
    : Kind) (tyConKind : Kind) (tyConArity : BasicTypes.Arity) (tcRoles
    : list Role) (dataCon : DataCon) (tcRepName : TyConRepName) (promDcRepInfo
    : RuntimeRepInfo)
   : TyCon
  | TcTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name) (tyConBinders
    : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConTyVars : list Var%type)
  (tyConResKind : Kind) (tyConKind : Kind) (tyConArity : BasicTypes.Arity)
  (tcTyConScopedTyVars : list (Name.Name * Var%type)%type) (tcTyConFlavour
    : TyConFlavour)
   : TyCon
with AlgTyConRhs : Type :=
  | AbstractTyCon : AlgTyConRhs
  | DataTyCon (data_cons : list DataCon) (is_enum : bool) : AlgTyConRhs
  | TupleTyCon (data_con : DataCon) (tup_sort : BasicTypes.TupleSort)
   : AlgTyConRhs
  | SumTyCon (data_cons : list DataCon) : AlgTyConRhs
  | NewTyCon (data_con : DataCon) (nt_rhs : Type_) (nt_etad_rhs
    : (list Var%type * Type_)%type) (nt_co : CoAxiom Unbranched)
   : AlgTyConRhs
with DataCon : Type :=
  | MkData (dcName : Name.Name) (dcUnique : Unique.Unique) (dcTag
    : BasicTypes.ConTag) (dcVanilla : bool) (dcUnivTyVars : list Var%type)
  (dcExTyVars : list Var%type) (dcUserTyVarBinders
    : list (TyVarBndr Var%type ArgFlag)%type) (dcEqSpec : list EqSpec)
  (dcOtherTheta : ThetaType) (dcStupidTheta : ThetaType) (dcOrigArgTys
    : list Type_) (dcOrigResTy : Type_) (dcSrcBangs : list HsSrcBang) (dcFields
    : list FieldLabel.FieldLabel) (dcWorkId : Var%type) (dcRep : DataConRep)
  (dcRepArity : BasicTypes.Arity) (dcSourceArity : BasicTypes.Arity) (dcRepTyCon
    : TyCon) (dcRepType : Type_) (dcInfix : bool) (dcPromoted : TyCon)
   : DataCon
with DataConRep : Type :=
  | NoDataConRep : DataConRep
  | DCR (dcr_wrap_id : Var%type) (dcr_boxer : DataConBoxer) (dcr_arg_tys
    : list Type_) (dcr_stricts : list StrictnessMark) (dcr_bangs : list HsImplBang)
   : DataConRep
with Var : Type :=
  | Mk_Id (varName : Name.Name) (realUnique : BinNums.N) (varType : Type_)
  (idScope : IdScope) (id_details : IdDetails) (id_info : IdInfo)
   : Var
with IdDetails : Type :=
  | VanillaId : IdDetails
  | RecSelId (sel_tycon : RecSelParent) (sel_naughty : bool) : IdDetails
  | DataConWorkId : DataCon -> IdDetails
  | DataConWrapId : DataCon -> IdDetails
  | ClassOpId : Class -> IdDetails
  | PrimOpId : PrimOp -> IdDetails
  | FCallId : ForeignCall -> IdDetails
  | TickBoxOpId : TickBoxOp -> IdDetails
  | Mk_DFunId : bool -> IdDetails
  | Mk_JoinId : BasicTypes.JoinArity -> IdDetails
with RecSelParent : Type :=
  | RecSelData : TyCon -> RecSelParent
  | RecSelPatSyn : PatSyn -> RecSelParent
with PatSyn : Type :=
  | MkPatSyn (psName : Name.Name) (psUnique : Unique.Unique) (psArgs : list Type_)
  (psArity : BasicTypes.Arity) (psInfix : bool) (psFieldLabels
    : list FieldLabel.FieldLabel) (psUnivTyVars
    : list (TyVarBndr Var%type ArgFlag)%type) (psReqTheta : ThetaType) (psExTyVars
    : list (TyVarBndr Var%type ArgFlag)%type) (psProvTheta : ThetaType) (psResultTy
    : Type_) (psMatcher : (Var%type * bool)%type) (psBuilder
    : option (Var%type * bool)%type)
   : PatSyn
with EqSpec : Type := | Mk_EqSpec : Var%type -> Type_ -> EqSpec.

Definition TyVar :=
  Var%type.

Definition TyVarBinder :=
  (TyVarBndr TyVar ArgFlag)%type.

Definition TyConBinder :=
  (TyVarBndr TyVar TyConBndrVis)%type.

Definition Id :=
  Var%type.

Definition ClassOpItem :=
  (Id * DefMethInfo)%type%type.

Definition NormaliseStepper ev :=
  (RecTcChecker -> TyCon -> list Type_ -> NormaliseStepResult ev)%type.

Definition CoreBndr :=
  Var%type.

Definition InBndr :=
  CoreBndr%type.

Definition OutBndr :=
  CoreBndr%type.

Inductive TaggedBndr t : Type := | TB : CoreBndr -> t -> TaggedBndr t.

Definition DVarSet :=
  (UniqSet.UniqSet Var)%type.

Definition CoVar :=
  Id%type.

Definition CoVarSet :=
  (UniqSet.UniqSet CoVar)%type.

Definition InCoVar :=
  CoVar%type.

Definition OutCoVar :=
  CoVar%type.

Definition DFunId :=
  Id%type.

Definition DIdSet :=
  (UniqSet.UniqSet Id)%type.

Definition EvId :=
  Id%type.

Definition DictId :=
  EvId%type.

Definition EqVar :=
  EvId%type.

Definition EvVar :=
  EvId%type.

Definition IpId :=
  EvId%type.

Definition IdSet :=
  (UniqSet.UniqSet Id)%type.

Definition IdUnfoldingFun :=
  (Id -> Unfolding)%type.

Definition InId :=
  Id%type.

Definition JoinId :=
  Id%type.

Definition NcId :=
  Id%type.

Definition OutId :=
  Id%type.

Definition TyCoVar :=
  Id%type.

Definition DTyCoVarSet :=
  (UniqSet.UniqSet TyCoVar)%type.

Definition TyCoVarSet :=
  (UniqSet.UniqSet TyCoVar)%type.

Definition InVar :=
  Var%type.

Definition KindVar :=
  Var%type.

Definition OutVar :=
  Var%type.

Definition TKVar :=
  Var%type.

Definition TidyEnv :=
  (OccName.TidyOccEnv * VarEnv Var)%type%type.

Inductive PredTree : Type :=
  | ClassPred : Class -> list Type_ -> PredTree
  | EqPred : EqRel -> Type_ -> Type_ -> PredTree
  | IrredPred : PredType -> PredTree.

Definition DTyVarSet :=
  (UniqSet.UniqSet TyVar)%type.

Definition InTyVar :=
  TyVar%type.

Definition OutTyVar :=
  TyVar%type.

Inductive TyCoMapper env m : Type :=
  | Mk_TyCoMapper (tcm_smart : bool) (tcm_tyvar : env -> TyVar -> m Type_)
  (tcm_covar : env -> CoVar -> m Coercion) (tcm_hole
    : env -> CoercionHole -> m Coercion) (tcm_tybinder
    : env -> TyVar -> ArgFlag -> m (env * TyVar)%type)
   : TyCoMapper env m.

Inductive AltCon : Type :=
  | DataAlt : DataCon -> AltCon
  | LitAlt : Literal -> AltCon
  | DEFAULT : AltCon.

Inductive Expr b : Type :=
  | Mk_Var : Id -> Expr b
  | Lit : Literal -> Expr b
  | App : (Expr b) -> (Expr%type b) -> Expr b
  | Lam : b -> (Expr b) -> Expr b
  | Let : (Bind b) -> (Expr b) -> Expr b
  | Case
   : (Expr b) ->
     b ->
     Type_ -> list ((fun b_ => (AltCon * list b_ * Expr b_)%type%type) b) -> Expr b
  | Cast : (Expr b) -> Coercion -> Expr b
  | Mk_Type : Type_ -> Expr b
  | Mk_Coercion : Coercion -> Expr b
with Bind b : Type :=
  | NonRec : b -> (Expr b) -> Bind b
  | Rec : list (b * (Expr b))%type -> Bind b.

Definition Arg :=
  Expr%type.

Definition Alt :=
  fun b_ => (AltCon * list b_ * Expr b_)%type%type.

Definition CoreAlt :=
  (Alt CoreBndr)%type.

Definition InAlt :=
  CoreAlt%type.

Definition OutAlt :=
  CoreAlt%type.

Definition CoreArg :=
  (Arg CoreBndr)%type.

Definition InArg :=
  CoreArg%type.

Definition OutArg :=
  CoreArg%type.

Definition TaggedArg t :=
  (Arg (TaggedBndr t))%type.

Definition CoreBind :=
  (Bind CoreBndr)%type.

Definition CoreProgram :=
  (list CoreBind)%type.

Definition InBind :=
  CoreBind%type.

Definition OutBind :=
  CoreBind%type.

Definition TaggedBind t :=
  (Bind (TaggedBndr t))%type.

Definition CoreExpr :=
  (Expr CoreBndr)%type.

Inductive CoreVect : Type :=
  | Vect : Id -> CoreExpr -> CoreVect
  | NoVect : Id -> CoreVect
  | VectType : bool -> TyCon -> (option TyCon) -> CoreVect
  | VectClass : TyCon -> CoreVect
  | VectInst : Id -> CoreVect.

Definition InExpr :=
  CoreExpr%type.

Definition OutExpr :=
  CoreExpr%type.

Definition TaggedExpr t :=
  (Expr (TaggedBndr t))%type.

Definition TaggedAlt t :=
  (Alt (TaggedBndr t))%type.

Inductive AnnExpr' bndr annot : Type :=
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
     bndr ->
     Type_ ->
     list ((fun bndr_ annot_ =>
              (AltCon * list bndr_ *
               (fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr_
               annot_)%type%type) bndr annot) ->
     AnnExpr' bndr annot
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

Definition AnnExpr :=
  fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type.

Definition AnnAlt :=
  fun bndr_ annot_ => (AltCon * list bndr_ * AnnExpr bndr_ annot_)%type%type.

Definition TyVarSet :=
  (UniqSet.UniqSet TyVar)%type.

Definition TypeVar :=
  Var%type.

Definition VarSet :=
  (UniqSet.UniqSet Var)%type.

Inductive InScopeSet : Type := | InScope : VarSet -> nat -> InScopeSet.

Definition InScopeEnv :=
  (InScopeSet * IdUnfoldingFun)%type%type.

Definition RuleFun :=
  (DynFlags.DynFlags ->
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

Definition RuleBase :=
  (NameEnv.NameEnv (list CoreRule))%type.

Inductive RuleEnv : Type :=
  | Mk_RuleEnv (re_base : RuleBase) (re_visible_orphs : Module.ModuleSet)
   : RuleEnv.

Inductive RnEnv2 : Type :=
  | RV2 (envL : VarEnv Var) (envR : VarEnv Var) (in_scope : InScopeSet) : RnEnv2.

Inductive TCvSubst : Type :=
  | Mk_TCvSubst : InScopeSet -> TvSubstEnv -> CvSubstEnv -> TCvSubst.

Inductive LiftingContext : Type :=
  | LC : TCvSubst -> LiftCoEnv -> LiftingContext.

Arguments TvBndr {_} {_} _ _.

Arguments ProfNote {_} _ _ _.

Arguments HpcTick {_} _ _.

Arguments Breakpoint {_} _ _.

Arguments SourceNote {_} _ _.

Arguments Diverges {_}.

Arguments ThrowsExn {_}.

Arguments Dunno {_} _.

Arguments NS_Done {_}.

Arguments NS_Abort {_}.

Arguments NS_Step {_} _ _ _.

Arguments JD {_} {_} _ _.

Arguments Lazy {_}.

Arguments Mk_Str {_} _ _.

Arguments Abs {_}.

Arguments Mk_Use {_} _ _.

Arguments TB {_} _ _.

Arguments Mk_TyCoMapper {_} {_} _ _ _ _ _.

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

Instance Default__UnfoldingSource : HsToCoq.Err.Default UnfoldingSource :=
  HsToCoq.Err.Build_Default _ InlineRhs.

Instance Default__UnfoldingGuidance : HsToCoq.Err.Default UnfoldingGuidance :=
  HsToCoq.Err.Build_Default _ (UnfWhen HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default).

Instance Default__Unfolding : HsToCoq.Err.Default Unfolding :=
  HsToCoq.Err.Build_Default _ NoUnfolding.

Instance Default__TypeShape : HsToCoq.Err.Default TypeShape :=
  HsToCoq.Err.Build_Default _ TsUnk.

Instance Default__TypeOrdering : HsToCoq.Err.Default TypeOrdering :=
  HsToCoq.Err.Build_Default _ TLT.

Instance Default__TyConFlavour : HsToCoq.Err.Default TyConFlavour :=
  HsToCoq.Err.Build_Default _ ClassFlavour.

Instance Default__TickishScoping : HsToCoq.Err.Default TickishScoping :=
  HsToCoq.Err.Build_Default _ NoScope.

Instance Default__TickishPlacement : HsToCoq.Err.Default TickishPlacement :=
  HsToCoq.Err.Build_Default _ PlaceRuntime.

Instance Default__StrictnessMark : HsToCoq.Err.Default StrictnessMark :=
  HsToCoq.Err.Build_Default _ MarkedStrict.

Instance Default__SrcUnpackedness : HsToCoq.Err.Default SrcUnpackedness :=
  HsToCoq.Err.Build_Default _ SrcUnpack.

Instance Default__SrcStrictness : HsToCoq.Err.Default SrcStrictness :=
  HsToCoq.Err.Build_Default _ SrcLazy.

Instance Default__PrimElemRep : HsToCoq.Err.Default PrimElemRep :=
  HsToCoq.Err.Build_Default _ Int8ElemRep.

Instance Default__PrimRep : HsToCoq.Err.Default PrimRep :=
  HsToCoq.Err.Build_Default _ VoidRep.

Instance Default__RuntimeRepInfo : HsToCoq.Err.Default RuntimeRepInfo :=
  HsToCoq.Err.Build_Default _ NoRRI.

Instance Default__LevityInfo : HsToCoq.Err.Default LevityInfo :=
  HsToCoq.Err.Build_Default _ NoLevityInfo.

Instance Default__KillFlags : HsToCoq.Err.Default KillFlags :=
  HsToCoq.Err.Build_Default _ (Mk_KillFlags HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__IsOrphan : HsToCoq.Err.Default IsOrphan :=
  HsToCoq.Err.Build_Default _ Mk_IsOrphan.

Instance Default__Injectivity : HsToCoq.Err.Default Injectivity :=
  HsToCoq.Err.Build_Default _ NotInjective.

Instance Default__HsImplBang : HsToCoq.Err.Default HsImplBang :=
  HsToCoq.Err.Build_Default _ HsLazy.

Instance Default__FamTyConFlav : HsToCoq.Err.Default FamTyConFlav :=
  HsToCoq.Err.Build_Default _ OpenSynFamilyTyCon.

Instance Default__ExportFlag : HsToCoq.Err.Default ExportFlag :=
  HsToCoq.Err.Build_Default _ NotExported.

Instance Default__IdScope : HsToCoq.Err.Default IdScope :=
  HsToCoq.Err.Build_Default _ GlobalId.

Instance Default__ExnStr : HsToCoq.Err.Default ExnStr :=
  HsToCoq.Err.Build_Default _ VanStr.

Instance Default__EqRel : HsToCoq.Err.Default EqRel :=
  HsToCoq.Err.Build_Default _ NomEq.

Instance Default__Count : HsToCoq.Err.Default Count :=
  HsToCoq.Err.Build_Default _ One.

Instance Default__UnivCoProvenance : HsToCoq.Err.Default UnivCoProvenance :=
  HsToCoq.Err.Build_Default _ UnsafeCoerceProv.

Instance Default__CafInfo : HsToCoq.Err.Default CafInfo :=
  HsToCoq.Err.Build_Default _ MayHaveCafRefs.

Instance Default__CPRResult : HsToCoq.Err.Default CPRResult :=
  HsToCoq.Err.Build_Default _ NoCPR.

Instance Default__UseDmd : HsToCoq.Err.Default UseDmd :=
  HsToCoq.Err.Build_Default _ UHead.

Instance Default__StrDmd : HsToCoq.Err.Default StrDmd :=
  HsToCoq.Err.Build_Default _ HyperStr.

Instance Default__ArgFlag : HsToCoq.Err.Default ArgFlag :=
  HsToCoq.Err.Build_Default _ Required.

Instance Default__TyConBndrVis : HsToCoq.Err.Default TyConBndrVis :=
  HsToCoq.Err.Build_Default _ AnonTCB.

Instance Default__ClassBody : HsToCoq.Err.Default ClassBody :=
  HsToCoq.Err.Build_Default _ AbstractClass.

Instance Default__TyCon : HsToCoq.Err.Default TyCon :=
  HsToCoq.Err.Build_Default _ (FunTyCon HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default).

Instance Default__AlgTyConRhs : HsToCoq.Err.Default AlgTyConRhs :=
  HsToCoq.Err.Build_Default _ AbstractTyCon.

Instance Default__DataConRep : HsToCoq.Err.Default DataConRep :=
  HsToCoq.Err.Build_Default _ NoDataConRep.

Instance Default__IdDetails : HsToCoq.Err.Default IdDetails :=
  HsToCoq.Err.Build_Default _ VanillaId.

Instance Default__AltCon : HsToCoq.Err.Default AltCon :=
  HsToCoq.Err.Build_Default _ DEFAULT.

Definition ug_args (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_args' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs ug_args _ _ => ug_args
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_args' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_arity (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen ug_arity _ _ => ug_arity
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_arity' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_arity' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_boring_ok (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ ug_boring_ok => ug_boring_ok
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_boring_ok' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_boring_ok' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_res (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_res' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs _ _ ug_res => ug_res
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_res' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_size (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_size' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs _ ug_size _ => ug_size
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_size' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_unsat_ok (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ ug_unsat_ok _ => ug_unsat_ok
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_unsat_ok' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_unsat_ok' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition breakpointFVs {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointFVs' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointFVs' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ breakpointFVs => breakpointFVs
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointFVs' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition breakpointId {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointId' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointId' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint breakpointId _ => breakpointId
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointId' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition profNoteCC {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote profNoteCC _ _ => profNoteCC
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCC' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCC' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCC' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition profNoteCount {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ profNoteCount _ => profNoteCount
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCount' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCount' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCount' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition profNoteScope {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ profNoteScope => profNoteScope
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteScope' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteScope' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteScope' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition sourceName {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceName' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceName' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceName' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ sourceName => sourceName
  end.

Definition sourceSpan {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceSpan' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceSpan' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceSpan' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote sourceSpan _ => sourceSpan
  end.

Definition tickId {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickId' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick _ tickId => tickId
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickId' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickId' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition tickModule {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickModule' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick tickModule _ => tickModule
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickModule' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickModule' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition kf_abs (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags kf_abs _ _ := arg_0__ in
  kf_abs.

Definition kf_called_once (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags _ _ kf_called_once := arg_0__ in
  kf_called_once.

Definition kf_used_once (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags _ kf_used_once _ := arg_0__ in
  kf_used_once.

Definition sd {s} {u} (arg_0__ : JointDmd s u) :=
  let 'JD sd _ := arg_0__ in
  sd.

Definition ud {s} {u} (arg_0__ : JointDmd s u) :=
  let 'JD _ ud := arg_0__ in
  ud.

Definition arityInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo arityInfo _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  arityInfo.

Definition cafInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ cafInfo _ _ _ _ _ _ _ := arg_0__ in
  cafInfo.

Definition callArityInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ _ _ _ callArityInfo _ := arg_0__ in
  callArityInfo.

Definition demandInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ _ _ demandInfo _ _ := arg_0__ in
  demandInfo.

Definition inlinePragInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ inlinePragInfo _ _ _ _ _ := arg_0__ in
  inlinePragInfo.

Definition levityInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ _ _ _ _ levityInfo := arg_0__ in
  levityInfo.

Definition occInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ occInfo _ _ _ _ := arg_0__ in
  occInfo.

Definition oneShotInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ oneShotInfo _ _ _ _ _ _ := arg_0__ in
  oneShotInfo.

Definition ruleInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ ruleInfo _ _ _ _ _ _ _ _ _ := arg_0__ in
  ruleInfo.

Definition strictnessInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ _ strictnessInfo _ _ _ := arg_0__ in
  strictnessInfo.

Definition unfoldingInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ unfoldingInfo _ _ _ _ _ _ _ _ := arg_0__ in
  unfoldingInfo.

Definition classBody (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ _ _ classBody := arg_0__ in
  classBody.

Definition classFunDeps (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ _ classFunDeps _ := arg_0__ in
  classFunDeps.

Definition classKey (arg_0__ : Class) :=
  let 'Mk_Class _ _ classKey _ _ _ := arg_0__ in
  classKey.

Definition className (arg_0__ : Class) :=
  let 'Mk_Class _ className _ _ _ _ := arg_0__ in
  className.

Definition classTyCon (arg_0__ : Class) :=
  let 'Mk_Class classTyCon _ _ _ _ _ := arg_0__ in
  classTyCon.

Definition classTyVars (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ classTyVars _ _ := arg_0__ in
  classTyVars.

Definition classATStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classATStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ classATStuff _ _ => classATStuff
  end.

Definition classMinimalDefStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classMinimalDefStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ _ _ classMinimalDefStuff => classMinimalDefStuff
  end.

Definition classOpStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classOpStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ _ classOpStuff _ => classOpStuff
  end.

Definition classSCSels (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classSCSels' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ classSCSels _ _ _ => classSCSels
  end.

Definition classSCThetaStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classSCThetaStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass classSCThetaStuff _ _ _ _ => classSCThetaStuff
  end.

Definition algTcFields (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ algTcFields _ => algTcFields
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition algTcGadtSyntax (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ algTcGadtSyntax _ _ _ _ => algTcGadtSyntax
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition algTcRhs (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ algTcRhs _ _ => algTcRhs
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition algTcStupidTheta (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ algTcStupidTheta _ _ _ => algTcStupidTheta
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition famTcFlav (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ famTcFlav _ _ => famTcFlav
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition famTcInj (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ famTcInj => famTcInj
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition famTcParent (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ famTcParent _ => famTcParent
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition famTcResVar (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ famTcResVar _ _ _ => famTcResVar
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition isUnlifted (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ isUnlifted _ => isUnlifted
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition primRepName (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ primRepName => primRepName
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition synIsFamFree (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ synIsFamFree => synIsFamFree
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition synIsTau (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ synIsTau _ => synIsTau
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition synTcRhs (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ synTcRhs _ _ => synTcRhs
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition tcRepName (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ tcRepName => tcRepName
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ tcRepName _ => tcRepName
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition tcRoles (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRoles' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ tcRoles _ _ _ _ _ _ => tcRoles
  | SynonymTyCon _ _ _ _ _ _ _ tcRoles _ _ _ => tcRoles
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRoles' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ tcRoles _ _ => tcRoles
  | PromotedDataCon _ _ _ _ _ _ tcRoles _ _ _ => tcRoles
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRoles' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition tcTyConFlavour (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ tcTyConFlavour => tcTyConFlavour
  end.

Definition tcTyConScopedTyVars (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ tcTyConScopedTyVars _ => tcTyConScopedTyVars
  end.

Definition tyConArity (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ tyConArity _ => tyConArity
  | AlgTyCon _ _ _ _ _ _ tyConArity _ _ _ _ _ _ _ => tyConArity
  | SynonymTyCon _ _ _ _ _ _ tyConArity _ _ _ _ => tyConArity
  | FamilyTyCon _ _ _ _ _ _ tyConArity _ _ _ _ => tyConArity
  | PrimTyCon _ _ _ _ _ tyConArity _ _ _ => tyConArity
  | PromotedDataCon _ _ _ _ _ tyConArity _ _ _ _ => tyConArity
  | TcTyCon _ _ _ _ _ _ tyConArity _ _ => tyConArity
  end.

Definition tyConBinders (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ tyConBinders _ _ _ _ => tyConBinders
  | AlgTyCon _ _ tyConBinders _ _ _ _ _ _ _ _ _ _ _ => tyConBinders
  | SynonymTyCon _ _ tyConBinders _ _ _ _ _ _ _ _ => tyConBinders
  | FamilyTyCon _ _ tyConBinders _ _ _ _ _ _ _ _ => tyConBinders
  | PrimTyCon _ _ tyConBinders _ _ _ _ _ _ => tyConBinders
  | PromotedDataCon _ _ tyConBinders _ _ _ _ _ _ _ => tyConBinders
  | TcTyCon _ _ tyConBinders _ _ _ _ _ _ => tyConBinders
  end.

Definition tyConCType (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ tyConCType _ _ _ _ _ => tyConCType
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition tyConKind (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ tyConKind _ _ => tyConKind
  | AlgTyCon _ _ _ _ _ tyConKind _ _ _ _ _ _ _ _ => tyConKind
  | SynonymTyCon _ _ _ _ _ tyConKind _ _ _ _ _ => tyConKind
  | FamilyTyCon _ _ _ _ _ tyConKind _ _ _ _ _ => tyConKind
  | PrimTyCon _ _ _ _ tyConKind _ _ _ _ => tyConKind
  | PromotedDataCon _ _ _ _ tyConKind _ _ _ _ _ => tyConKind
  | TcTyCon _ _ _ _ _ tyConKind _ _ _ => tyConKind
  end.

Definition tyConName (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ tyConName _ _ _ _ _ => tyConName
  | AlgTyCon _ tyConName _ _ _ _ _ _ _ _ _ _ _ _ => tyConName
  | SynonymTyCon _ tyConName _ _ _ _ _ _ _ _ _ => tyConName
  | FamilyTyCon _ tyConName _ _ _ _ _ _ _ _ _ => tyConName
  | PrimTyCon _ tyConName _ _ _ _ _ _ _ => tyConName
  | PromotedDataCon _ tyConName _ _ _ _ _ _ _ _ => tyConName
  | TcTyCon _ tyConName _ _ _ _ _ _ _ => tyConName
  end.

Definition tyConResKind (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ tyConResKind _ _ _ => tyConResKind
  | AlgTyCon _ _ _ _ tyConResKind _ _ _ _ _ _ _ _ _ => tyConResKind
  | SynonymTyCon _ _ _ _ tyConResKind _ _ _ _ _ _ => tyConResKind
  | FamilyTyCon _ _ _ _ tyConResKind _ _ _ _ _ _ => tyConResKind
  | PrimTyCon _ _ _ tyConResKind _ _ _ _ _ => tyConResKind
  | PromotedDataCon _ _ _ tyConResKind _ _ _ _ _ _ => tyConResKind
  | TcTyCon _ _ _ _ tyConResKind _ _ _ _ => tyConResKind
  end.

Definition tyConTyVars (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConTyVars' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ tyConTyVars _ _ _ _ _ _ _ _ _ _ => tyConTyVars
  | SynonymTyCon _ _ _ tyConTyVars _ _ _ _ _ _ _ => tyConTyVars
  | FamilyTyCon _ _ _ tyConTyVars _ _ _ _ _ _ _ => tyConTyVars
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConTyVars' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConTyVars' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ tyConTyVars _ _ _ _ _ => tyConTyVars
  end.

Definition tyConUnique (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon tyConUnique _ _ _ _ _ _ => tyConUnique
  | AlgTyCon tyConUnique _ _ _ _ _ _ _ _ _ _ _ _ _ => tyConUnique
  | SynonymTyCon tyConUnique _ _ _ _ _ _ _ _ _ _ => tyConUnique
  | FamilyTyCon tyConUnique _ _ _ _ _ _ _ _ _ _ => tyConUnique
  | PrimTyCon tyConUnique _ _ _ _ _ _ _ _ => tyConUnique
  | PromotedDataCon tyConUnique _ _ _ _ _ _ _ _ _ => tyConUnique
  | TcTyCon tyConUnique _ _ _ _ _ _ _ _ => tyConUnique
  end.

Definition data_cons (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon data_cons _ => data_cons
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon data_cons => data_cons
  | NewTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

Definition is_enum (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ is_enum => is_enum
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

Definition nt_co (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ nt_co => nt_co
  end.

Definition nt_etad_rhs (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ nt_etad_rhs _ => nt_etad_rhs
  end.

Definition nt_rhs (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ nt_rhs _ _ => nt_rhs
  end.

Definition tup_sort (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ tup_sort => tup_sort
  | SumTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

Definition dcEqSpec (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ dcEqSpec _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcEqSpec.

Definition dcExTyVars (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ dcExTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcExTyVars.

Definition dcFields (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ dcFields _ _ _ _ _ _ _ _ := arg_0__ in
  dcFields.

Definition dcInfix (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcInfix _ := arg_0__ in
  dcInfix.

Definition dcName (arg_0__ : DataCon) :=
  let 'MkData dcName _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcName.

Definition dcOrigArgTys (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ dcOrigArgTys _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcOrigArgTys.

Definition dcOrigResTy (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ dcOrigResTy _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcOrigResTy.

Definition dcOtherTheta (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ dcOtherTheta _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcOtherTheta.

Definition dcPromoted (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcPromoted := arg_0__ in
  dcPromoted.

Definition dcRep (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRep _ _ _ _ _ _ := arg_0__ in
  dcRep.

Definition dcRepArity (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepArity _ _ _ _ _ := arg_0__ in
  dcRepArity.

Definition dcRepTyCon (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepTyCon _ _ _ := arg_0__ in
  dcRepTyCon.

Definition dcRepType (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepType _ _ := arg_0__ in
  dcRepType.

Definition dcSourceArity (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcSourceArity _ _ _ _ :=
    arg_0__ in
  dcSourceArity.

Definition dcSrcBangs (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ dcSrcBangs _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcSrcBangs.

Definition dcStupidTheta (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ dcStupidTheta _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcStupidTheta.

Definition dcTag (arg_0__ : DataCon) :=
  let 'MkData _ _ dcTag _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcTag.

Definition dcUnique (arg_0__ : DataCon) :=
  let 'MkData _ dcUnique _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcUnique.

Definition dcUnivTyVars (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ dcUnivTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcUnivTyVars.

Definition dcUserTyVarBinders (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ dcUserTyVarBinders _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcUserTyVarBinders.

Definition dcVanilla (arg_0__ : DataCon) :=
  let 'MkData _ _ _ dcVanilla _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcVanilla.

Definition dcWorkId (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcWorkId _ _ _ _ _ _ _ := arg_0__ in
  dcWorkId.

Definition dcr_arg_tys (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_arg_tys' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ dcr_arg_tys _ _ => dcr_arg_tys
  end.

Definition dcr_bangs (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_bangs' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ _ _ dcr_bangs => dcr_bangs
  end.

Definition dcr_boxer (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_boxer' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ dcr_boxer _ _ _ => dcr_boxer
  end.

Definition dcr_stricts (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_stricts' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ _ dcr_stricts _ => dcr_stricts
  end.

Definition idScope (arg_0__ : Var) :=
  let 'Mk_Id _ _ _ idScope _ _ := arg_0__ in
  idScope.

Definition id_details (arg_0__ : Var) :=
  let 'Mk_Id _ _ _ _ id_details _ := arg_0__ in
  id_details.

Definition realUnique (arg_0__ : Var) :=
  let 'Mk_Id _ realUnique _ _ _ _ := arg_0__ in
  realUnique.

Definition varName (arg_0__ : Var) :=
  let 'Mk_Id varName _ _ _ _ _ := arg_0__ in
  varName.

Definition varType (arg_0__ : Var) :=
  let 'Mk_Id _ _ varType _ _ _ := arg_0__ in
  varType.

Definition sel_naughty (arg_0__ : IdDetails) :=
  match arg_0__ with
  | VanillaId =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `VanillaId' of type `IdDetails'")
  | RecSelId _ sel_naughty => sel_naughty
  | DataConWorkId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `DataConWorkId' of type `IdDetails'")
  | DataConWrapId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `DataConWrapId' of type `IdDetails'")
  | ClassOpId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `ClassOpId' of type `IdDetails'")
  | PrimOpId _ =>
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
  | Mk_JoinId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `Mk_JoinId' of type `IdDetails'")
  end.

Definition psArgs (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ psArgs _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psArgs.

Definition psArity (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ psArity _ _ _ _ _ _ _ _ _ := arg_0__ in
  psArity.

Definition psBuilder (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ _ _ psBuilder := arg_0__ in
  psBuilder.

Definition psExTyVars (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ psExTyVars _ _ _ _ := arg_0__ in
  psExTyVars.

Definition psFieldLabels (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ psFieldLabels _ _ _ _ _ _ _ := arg_0__ in
  psFieldLabels.

Definition psInfix (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ psInfix _ _ _ _ _ _ _ _ := arg_0__ in
  psInfix.

Definition psMatcher (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ _ psMatcher _ := arg_0__ in
  psMatcher.

Definition psName (arg_0__ : PatSyn) :=
  let 'MkPatSyn psName _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psName.

Definition psProvTheta (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ psProvTheta _ _ _ := arg_0__ in
  psProvTheta.

Definition psReqTheta (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ psReqTheta _ _ _ _ _ := arg_0__ in
  psReqTheta.

Definition psResultTy (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ psResultTy _ _ := arg_0__ in
  psResultTy.

Definition psUnique (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ psUnique _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psUnique.

Definition psUnivTyVars (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ psUnivTyVars _ _ _ _ _ _ := arg_0__ in
  psUnivTyVars.

Definition tcm_covar {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'Mk_TyCoMapper _ _ tcm_covar _ _ := arg_0__ in
  tcm_covar.

Definition tcm_hole {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'Mk_TyCoMapper _ _ _ tcm_hole _ := arg_0__ in
  tcm_hole.

Definition tcm_smart {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'Mk_TyCoMapper tcm_smart _ _ _ _ := arg_0__ in
  tcm_smart.

Definition tcm_tybinder {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'Mk_TyCoMapper _ _ _ _ tcm_tybinder := arg_0__ in
  tcm_tybinder.

Definition tcm_tyvar {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'Mk_TyCoMapper _ tcm_tyvar _ _ _ := arg_0__ in
  tcm_tyvar.

Definition ru_act (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ ru_act _ _ _ _ _ _ _ _ _ => ru_act
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_act' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_args (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ ru_args _ _ _ _ _ => ru_args
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_args' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_auto (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ ru_auto _ _ _ => ru_auto
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_auto' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_bndrs (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ ru_bndrs _ _ _ _ _ _ => ru_bndrs
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_bndrs' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_fn (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ ru_fn _ _ _ _ _ _ _ _ => ru_fn
  | BuiltinRule _ ru_fn _ _ => ru_fn
  end.

Definition ru_local (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ ru_local => ru_local
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_local' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_name (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule ru_name _ _ _ _ _ _ _ _ _ _ => ru_name
  | BuiltinRule ru_name _ _ _ => ru_name
  end.

Definition ru_nargs (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_nargs' has no match in constructor `Rule' of type `CoreRule'")
  | BuiltinRule _ _ ru_nargs _ => ru_nargs
  end.

Definition ru_origin (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ ru_origin _ _ => ru_origin
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_origin' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_orphan (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ ru_orphan _ => ru_orphan
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_orphan' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_rough (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ ru_rough _ _ _ _ _ _ _ => ru_rough
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_rough' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_try (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_try' has no match in constructor `Rule' of type `CoreRule'")
  | BuiltinRule _ _ _ ru_try => ru_try
  end.

Definition re_base (arg_0__ : RuleEnv) :=
  let 'Mk_RuleEnv re_base _ := arg_0__ in
  re_base.

Definition re_visible_orphs (arg_0__ : RuleEnv) :=
  let 'Mk_RuleEnv _ re_visible_orphs := arg_0__ in
  re_visible_orphs.

Definition envL (arg_0__ : RnEnv2) :=
  let 'RV2 envL _ _ := arg_0__ in
  envL.

Definition envR (arg_0__ : RnEnv2) :=
  let 'RV2 _ envR _ := arg_0__ in
  envR.

Definition in_scope (arg_0__ : RnEnv2) :=
  let 'RV2 _ _ in_scope := arg_0__ in
  in_scope.

(* Midamble *)

(*  IdInfo: midamble *)

Require HsToCoq.Err.

(* --------------------- *)


(*****)

Instance Default__RuleInfo : HsToCoq.Err.Default RuleInfo :=
  HsToCoq.Err.Build_Default _ EmptyRuleInfo.

Instance Default__TickBoxOp : HsToCoq.Err.Default TickBoxOp :=
  HsToCoq.Err.Build_Default _ (TickBox HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__Termination {r} : HsToCoq.Err.Default (Termination r) :=
  HsToCoq.Err.Build_Default _ Diverges.

Instance Default__DmdType : HsToCoq.Err.Default DmdType :=
  HsToCoq.Err.Build_Default _ (Mk_DmdType HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__StrictSig : HsToCoq.Err.Default StrictSig :=
  HsToCoq.Err.Build_Default _ (Mk_StrictSig HsToCoq.Err.default).

Instance Default__JointDmd `{HsToCoq.Err.Default a} `{HsToCoq.Err.Default b} : HsToCoq.Err.Default (JointDmd a b) :=
  HsToCoq.Err.Build_Default _ (JD HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__Str {s} : HsToCoq.Err.Default (Str s) :=
  HsToCoq.Err.Build_Default _ Lazy.
Instance Default__Use {s} : HsToCoq.Err.Default (Use s) :=
  HsToCoq.Err.Build_Default _ Abs.

Instance Default__IdInfo : HsToCoq.Err.Default IdInfo :=
  HsToCoq.Err.Build_Default _ (Mk_IdInfo HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default
                         HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default
                         HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__RecSelParent : HsToCoq.Err.Default RecSelParent :=
  HsToCoq.Err.Build_Default _ (RecSelData HsToCoq.Err.default).


Instance Default__Var : HsToCoq.Err.Default Var := HsToCoq.Err.Build_Default _ (Mk_Id HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).


Instance Default__DataCon : HsToCoq.Err.Default DataCon :=
 Err.Build_Default _ (MkData HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default nil nil nil nil HsToCoq.Err.default HsToCoq.Err.default nil HsToCoq.Err.default nil nil HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
(* ---- TyCon midamble ----- *)
Instance Default__AlgTyConFlav : Err.Default AlgTyConFlav :=
  Err.Build_Default _ (VanillaAlgTyCon Err.default).
Instance Default__RuntimRepInfo : Err.Default RuntimeRepInfo :=
  Err.Build_Default _ NoRRI.



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
(* ------------- VarEnv midamble.v ------------ *)
Instance Default__InScopeSet : HsToCoq.Err.Default InScopeSet :=
  HsToCoq.Err.Build_Default _ (InScope HsToCoq.Err.default HsToCoq.Err.default).
Instance Default__RnEnv2 : HsToCoq.Err.Default RnEnv2 :=
  HsToCoq.Err.Build_Default _ (RV2 HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
Instance Default__TidyEnv : HsToCoq.Err.Default TidyEnv :=
  HsToCoq.Err.Build_Default _ (pair HsToCoq.Err.default HsToCoq.Err.default).


(* ------------- CoreSyn midamble.v ------------ *)
Require Import Coq.ZArith.ZArith.
Require Import Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

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
             omega].

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
                                         | (_,_,(_,e)) => size_AnnExpr' e
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

Instance Default__Expr {b} : HsToCoq.Err.Default (Expr b) :=
  HsToCoq.Err.Build_Default _ (Mk_Var HsToCoq.Err.default).

Instance Default__Tickish {a} : HsToCoq.Err.Default (Tickish a) :=
  HsToCoq.Err.Build_Default _ (Breakpoint HsToCoq.Err.default HsToCoq.Err.default).

Instance Default_TaggedBndr {t}`{HsToCoq.Err.Default t} : HsToCoq.Err.Default (TaggedBndr t) :=
  HsToCoq.Err.Build_Default _ (TB HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__AnnExpr' {a}{b} : HsToCoq.Err.Default (AnnExpr' a b) :=
  HsToCoq.Err.Build_Default _ (AnnVar HsToCoq.Err.default). 

Instance Default__AnnBind {a}{b} : HsToCoq.Err.Default (AnnBind a b) :=
  HsToCoq.Err.Build_Default _ (AnnRec HsToCoq.Err.default). 

Instance Default__Bind {b} : HsToCoq.Err.Default (Bind b) :=
  HsToCoq.Err.Build_Default _ (Rec HsToCoq.Err.default). 

Instance Default__CoreVect : HsToCoq.Err.Default CoreVect :=
  HsToCoq.Err.Build_Default _ (Vect HsToCoq.Err.default HsToCoq.Err.default). 

Instance Default__CoreRule : HsToCoq.Err.Default CoreRule :=
  HsToCoq.Err.Build_Default _ (BuiltinRule HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__RuleEnv : HsToCoq.Err.Default RuleEnv :=
  HsToCoq.Err.Build_Default _ (Mk_RuleEnv HsToCoq.Err.default HsToCoq.Err.default).


(* ---------------------------------- *)

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
Require Import Omega.

Ltac solve_not_zero_N := match goal with 
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] => 
    unfold GHC.Base.op_zeze__ in H;
    unfold GHC.Base.Eq_Char___ in H;
    simpl in H;
    apply N.eqb_neq in H end;
    zify;
    omega.
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
      try solve [zify; omega]
  end.

Ltac distinguish := split; intros; unfold not; intros [? ?]; discriminate.
Ltac solve_mkWorkerDemand := Tactics.program_simpl; simpl_not_zero; solve_error_sub.

Ltac solve_dmdTransform := Tactics.program_simpl; try solve_mkWorkerDemand; try distinguish.


Instance Unpeel_StrictSig : Prim.Unpeel StrictSig DmdType :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_StrictSig y => y end) Mk_StrictSig.


(* size metric, incase it is useful *)

Definition Str_size {a} (f : a -> nat) (x : Str a) : nat :=
  match x with
  | Lazy => 0
  | Mk_Str _ s => f s
  end.

Fixpoint StrDmd_size (s1 : StrDmd): nat :=
  match s1 with
  | HyperStr => 0
  | SCall s => Nat.add 1 (StrDmd_size s)
  | SProd ss => List.fold_left Nat.add (List.map (Str_size StrDmd_size) ss) 1
  | HeadStr => 0
  end.

Definition ArgStrDmd_size := Str_size StrDmd_size.

(* Converted value declarations: *)

Local Definition Eq___ArgFlag_op_zeze__ : ArgFlag -> ArgFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Required, Required => true
    | Specified, Specified => true
    | Inferred, Inferred => true
    | _, _ => false
    end.

Local Definition Eq___ArgFlag_op_zsze__ : ArgFlag -> ArgFlag -> bool :=
  fun x y => negb (Eq___ArgFlag_op_zeze__ x y).

Program Instance Eq___ArgFlag : GHC.Base.Eq_ ArgFlag :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___ArgFlag_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___ArgFlag_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__ArgFlag' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__TyVarBndr' *)

Local Definition Eq___EqRel_op_zeze__ : EqRel -> EqRel -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NomEq, NomEq => true
    | ReprEq, ReprEq => true
    | _, _ => false
    end.

Local Definition Eq___EqRel_op_zsze__ : EqRel -> EqRel -> bool :=
  fun x y => negb (Eq___EqRel_op_zeze__ x y).

Program Instance Eq___EqRel : GHC.Base.Eq_ EqRel :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___EqRel_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___EqRel_op_zsze__ |}.

Local Definition Ord__EqRel_op_zl__ : EqRel -> EqRel -> bool :=
  fun a b =>
    match a with
    | NomEq => match b with | NomEq => false | _ => true end
    | ReprEq => match b with | ReprEq => false | _ => false end
    end.

Local Definition Ord__EqRel_op_zlze__ : EqRel -> EqRel -> bool :=
  fun a b => negb (Ord__EqRel_op_zl__ b a).

Local Definition Ord__EqRel_op_zg__ : EqRel -> EqRel -> bool :=
  fun a b => Ord__EqRel_op_zl__ b a.

Local Definition Ord__EqRel_op_zgze__ : EqRel -> EqRel -> bool :=
  fun a b => negb (Ord__EqRel_op_zl__ a b).

Local Definition Ord__EqRel_compare : EqRel -> EqRel -> comparison :=
  fun a b =>
    match a with
    | NomEq => match b with | NomEq => Eq | _ => Lt end
    | ReprEq => match b with | ReprEq => Eq | _ => Gt end
    end.

Local Definition Ord__EqRel_max : EqRel -> EqRel -> EqRel :=
  fun x y => if Ord__EqRel_op_zlze__ x y : bool then y else x.

Local Definition Ord__EqRel_min : EqRel -> EqRel -> EqRel :=
  fun x y => if Ord__EqRel_op_zlze__ x y : bool then x else y.

Program Instance Ord__EqRel : GHC.Base.Ord EqRel :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__EqRel_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__EqRel_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__EqRel_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__EqRel_op_zgze__ ;
           GHC.Base.compare__ := Ord__EqRel_compare ;
           GHC.Base.max__ := Ord__EqRel_max ;
           GHC.Base.min__ := Ord__EqRel_min |}.

Local Definition Eq___TypeOrdering_op_zeze__
   : TypeOrdering -> TypeOrdering -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TLT, TLT => true
    | TEQ, TEQ => true
    | TEQX, TEQX => true
    | TGT, TGT => true
    | _, _ => false
    end.

Local Definition Eq___TypeOrdering_op_zsze__
   : TypeOrdering -> TypeOrdering -> bool :=
  fun x y => negb (Eq___TypeOrdering_op_zeze__ x y).

Program Instance Eq___TypeOrdering : GHC.Base.Eq_ TypeOrdering :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TypeOrdering_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TypeOrdering_op_zsze__ |}.

(* Skipping instance `Core.Ord__TypeOrdering' of class `GHC.Base.Ord' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Core.Enum__TypeOrdering' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Core.Bounded__TypeOrdering' *)

Local Definition Eq___Injectivity_op_zeze__
   : Injectivity -> Injectivity -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NotInjective, NotInjective => true
    | Injective a1, Injective b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___Injectivity_op_zsze__
   : Injectivity -> Injectivity -> bool :=
  fun x y => negb (Eq___Injectivity_op_zeze__ x y).

Program Instance Eq___Injectivity : GHC.Base.Eq_ Injectivity :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Injectivity_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Injectivity_op_zsze__ |}.

Local Definition Eq___PrimElemRep_op_zeze__
   : PrimElemRep -> PrimElemRep -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Int8ElemRep, Int8ElemRep => true
    | Int16ElemRep, Int16ElemRep => true
    | Int32ElemRep, Int32ElemRep => true
    | Int64ElemRep, Int64ElemRep => true
    | Word8ElemRep, Word8ElemRep => true
    | Word16ElemRep, Word16ElemRep => true
    | Word32ElemRep, Word32ElemRep => true
    | Word64ElemRep, Word64ElemRep => true
    | FloatElemRep, FloatElemRep => true
    | DoubleElemRep, DoubleElemRep => true
    | _, _ => false
    end.

Local Definition Eq___PrimElemRep_op_zsze__
   : PrimElemRep -> PrimElemRep -> bool :=
  fun x y => negb (Eq___PrimElemRep_op_zeze__ x y).

Program Instance Eq___PrimElemRep : GHC.Base.Eq_ PrimElemRep :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___PrimElemRep_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___PrimElemRep_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__PrimElemRep' *)

Local Definition Eq___PrimRep_op_zeze__ : PrimRep -> PrimRep -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | VoidRep, VoidRep => true
    | LiftedRep, LiftedRep => true
    | UnliftedRep, UnliftedRep => true
    | IntRep, IntRep => true
    | WordRep, WordRep => true
    | Int64Rep, Int64Rep => true
    | Word64Rep, Word64Rep => true
    | AddrRep, AddrRep => true
    | FloatRep, FloatRep => true
    | DoubleRep, DoubleRep => true
    | VecRep a1 a2, VecRep b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___PrimRep_op_zsze__ : PrimRep -> PrimRep -> bool :=
  fun x y => negb (Eq___PrimRep_op_zeze__ x y).

Program Instance Eq___PrimRep : GHC.Base.Eq_ PrimRep :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___PrimRep_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___PrimRep_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__PrimRep' *)

Local Definition Eq___TyConFlavour_op_zeze__
   : TyConFlavour -> TyConFlavour -> bool :=
  fun a b => false.

Local Definition Eq___TyConFlavour_op_zsze__
   : TyConFlavour -> TyConFlavour -> bool :=
  fun x y => negb (Eq___TyConFlavour_op_zeze__ x y).

Program Instance Eq___TyConFlavour : GHC.Base.Eq_ TyConFlavour :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TyConFlavour_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TyConFlavour_op_zsze__ |}.

Local Definition Eq___TyLit_op_zeze__ : TyLit -> TyLit -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NumTyLit a1, NumTyLit b1 => ((a1 GHC.Base.== b1))
    | StrTyLit a1, StrTyLit b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___TyLit_op_zsze__ : TyLit -> TyLit -> bool :=
  fun x y => negb (Eq___TyLit_op_zeze__ x y).

Program Instance Eq___TyLit : GHC.Base.Eq_ TyLit :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TyLit_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TyLit_op_zsze__ |}.

Local Definition Ord__TyLit_op_zl__ : TyLit -> TyLit -> bool :=
  fun a b =>
    match a with
    | NumTyLit a1 =>
        match b with
        | NumTyLit b1 => (a1 GHC.Base.< b1)
        | _ => true
        end
    | StrTyLit a1 =>
        match b with
        | StrTyLit b1 => (a1 GHC.Base.< b1)
        | _ => false
        end
    end.

Local Definition Ord__TyLit_op_zlze__ : TyLit -> TyLit -> bool :=
  fun a b => negb (Ord__TyLit_op_zl__ b a).

Local Definition Ord__TyLit_op_zg__ : TyLit -> TyLit -> bool :=
  fun a b => Ord__TyLit_op_zl__ b a.

Local Definition Ord__TyLit_op_zgze__ : TyLit -> TyLit -> bool :=
  fun a b => negb (Ord__TyLit_op_zl__ a b).

Local Definition Ord__TyLit_compare : TyLit -> TyLit -> comparison :=
  fun a b =>
    match a with
    | NumTyLit a1 =>
        match b with
        | NumTyLit b1 => (GHC.Base.compare a1 b1)
        | _ => Lt
        end
    | StrTyLit a1 =>
        match b with
        | StrTyLit b1 => (GHC.Base.compare a1 b1)
        | _ => Gt
        end
    end.

Local Definition Ord__TyLit_max : TyLit -> TyLit -> TyLit :=
  fun x y => if Ord__TyLit_op_zlze__ x y : bool then y else x.

Local Definition Ord__TyLit_min : TyLit -> TyLit -> TyLit :=
  fun x y => if Ord__TyLit_op_zlze__ x y : bool then x else y.

Program Instance Ord__TyLit : GHC.Base.Ord TyLit :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__TyLit_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__TyLit_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__TyLit_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__TyLit_op_zgze__ ;
           GHC.Base.compare__ := Ord__TyLit_compare ;
           GHC.Base.max__ := Ord__TyLit_max ;
           GHC.Base.min__ := Ord__TyLit_min |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__TyLit' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Coercion' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__UnivCoProvenance' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Type_' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__TyBinder' *)

Local Definition Uniquable__PatSyn_getUnique : PatSyn -> Unique.Unique :=
  psUnique.

Program Instance Uniquable__PatSyn : Unique.Uniquable PatSyn :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__PatSyn_getUnique |}.

Local Definition Eq___PatSyn_op_zeze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base.==_ Unique.getUnique.

Local Definition Eq___PatSyn_op_zsze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base./=_ Unique.getUnique.

Program Instance Eq___PatSyn : GHC.Base.Eq_ PatSyn :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___PatSyn_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___PatSyn_op_zsze__ |}.

Local Definition Uniquable__TyCon_getUnique : TyCon -> Unique.Unique :=
  fun tc => tyConUnique tc.

Program Instance Uniquable__TyCon : Unique.Uniquable TyCon :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__TyCon_getUnique |}.

Local Definition Eq___TyCon_op_zeze__ : TyCon -> TyCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

Local Definition Eq___TyCon_op_zsze__ : TyCon -> TyCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

Program Instance Eq___TyCon : GHC.Base.Eq_ TyCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TyCon_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TyCon_op_zsze__ |}.

Local Definition Eq___RecSelParent_op_zeze__
   : RecSelParent -> RecSelParent -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RecSelData a1, RecSelData b1 => ((a1 GHC.Base.== b1))
    | RecSelPatSyn a1, RecSelPatSyn b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___RecSelParent_op_zsze__
   : RecSelParent -> RecSelParent -> bool :=
  fun x y => negb (Eq___RecSelParent_op_zeze__ x y).

Program Instance Eq___RecSelParent : GHC.Base.Eq_ RecSelParent :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___RecSelParent_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___RecSelParent_op_zsze__ |}.

Local Definition Eq___CafInfo_op_zeze__ : CafInfo -> CafInfo -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MayHaveCafRefs, MayHaveCafRefs => true
    | NoCafRefs, NoCafRefs => true
    | _, _ => false
    end.

Local Definition Eq___CafInfo_op_zsze__ : CafInfo -> CafInfo -> bool :=
  fun x y => negb (Eq___CafInfo_op_zeze__ x y).

Program Instance Eq___CafInfo : GHC.Base.Eq_ CafInfo :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___CafInfo_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___CafInfo_op_zsze__ |}.

Local Definition Ord__CafInfo_op_zl__ : CafInfo -> CafInfo -> bool :=
  fun a b =>
    match a with
    | MayHaveCafRefs => match b with | MayHaveCafRefs => false | _ => true end
    | NoCafRefs => match b with | NoCafRefs => false | _ => false end
    end.

Local Definition Ord__CafInfo_op_zlze__ : CafInfo -> CafInfo -> bool :=
  fun a b => negb (Ord__CafInfo_op_zl__ b a).

Local Definition Ord__CafInfo_op_zg__ : CafInfo -> CafInfo -> bool :=
  fun a b => Ord__CafInfo_op_zl__ b a.

Local Definition Ord__CafInfo_op_zgze__ : CafInfo -> CafInfo -> bool :=
  fun a b => negb (Ord__CafInfo_op_zl__ a b).

Local Definition Ord__CafInfo_compare : CafInfo -> CafInfo -> comparison :=
  fun a b =>
    match a with
    | MayHaveCafRefs => match b with | MayHaveCafRefs => Eq | _ => Lt end
    | NoCafRefs => match b with | NoCafRefs => Eq | _ => Gt end
    end.

Local Definition Ord__CafInfo_max : CafInfo -> CafInfo -> CafInfo :=
  fun x y => if Ord__CafInfo_op_zlze__ x y : bool then y else x.

Local Definition Ord__CafInfo_min : CafInfo -> CafInfo -> CafInfo :=
  fun x y => if Ord__CafInfo_op_zlze__ x y : bool then x else y.

Program Instance Ord__CafInfo : GHC.Base.Ord CafInfo :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__CafInfo_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__CafInfo_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__CafInfo_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__CafInfo_op_zgze__ ;
           GHC.Base.compare__ := Ord__CafInfo_compare ;
           GHC.Base.max__ := Ord__CafInfo_max ;
           GHC.Base.min__ := Ord__CafInfo_min |}.

Local Definition Eq___LevityInfo_op_zeze__ : LevityInfo -> LevityInfo -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoLevityInfo, NoLevityInfo => true
    | NeverLevityPolymorphic, NeverLevityPolymorphic => true
    | _, _ => false
    end.

Local Definition Eq___LevityInfo_op_zsze__ : LevityInfo -> LevityInfo -> bool :=
  fun x y => negb (Eq___LevityInfo_op_zeze__ x y).

Program Instance Eq___LevityInfo : GHC.Base.Eq_ LevityInfo :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___LevityInfo_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___LevityInfo_op_zsze__ |}.

Local Definition Eq___JointDmd_op_zeze__ {inst_s : Type} {inst_u : Type}
  `{GHC.Base.Eq_ inst_s} `{GHC.Base.Eq_ inst_u}
   : JointDmd inst_s inst_u -> JointDmd inst_s inst_u -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD a1 a2, JD b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___JointDmd_op_zsze__ {inst_s : Type} {inst_u : Type}
  `{GHC.Base.Eq_ inst_s} `{GHC.Base.Eq_ inst_u}
   : JointDmd inst_s inst_u -> JointDmd inst_s inst_u -> bool :=
  fun x y => negb (Eq___JointDmd_op_zeze__ x y).

Local Definition Eq___ExnStr_op_zeze__ : ExnStr -> ExnStr -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | VanStr, VanStr => true
    | Mk_ExnStr, Mk_ExnStr => true
    | _, _ => false
    end.

Local Definition Eq___ExnStr_op_zsze__ : ExnStr -> ExnStr -> bool :=
  fun x y => negb (Eq___ExnStr_op_zeze__ x y).

Program Instance Eq___ExnStr : GHC.Base.Eq_ ExnStr :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___ExnStr_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___ExnStr_op_zsze__ |}.

Local Definition Eq___Str_op_zeze__ {inst_s : Type} `{GHC.Base.Eq_ inst_s}
   : Str inst_s -> Str inst_s -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Lazy, Lazy => true
    | Mk_Str a1 a2, Mk_Str b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___Str_op_zsze__ {inst_s : Type} `{GHC.Base.Eq_ inst_s}
   : Str inst_s -> Str inst_s -> bool :=
  fun x y => negb (Eq___Str_op_zeze__ x y).

Program Instance Eq___Str {s : Type} `{GHC.Base.Eq_ s} : GHC.Base.Eq_ (Str s) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Str_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Str_op_zsze__ |}.

Local Definition Eq___StrDmd_op_zeze__ : StrDmd -> StrDmd -> bool :=
  fix StrDmd_eq x y
    := let eq' : GHC.Base.Eq_ StrDmd := GHC.Base.eq_default StrDmd_eq in
       match x, y with
       | HyperStr, HyperStr => true
       | SCall a1, SCall b1 => a1 GHC.Base.== b1
       | SProd a1, SProd b1 => a1 GHC.Base.== b1
       | HeadStr, HeadStr => true
       | _, _ => false
       end.

Local Definition Eq___StrDmd_op_zsze__ : StrDmd -> StrDmd -> bool :=
  fun x y => negb (Eq___StrDmd_op_zeze__ x y).

Program Instance Eq___StrDmd : GHC.Base.Eq_ StrDmd :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___StrDmd_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___StrDmd_op_zsze__ |}.

Program Instance Eq___JointDmd {s : Type} {u : Type} `{GHC.Base.Eq_ s}
  `{GHC.Base.Eq_ u}
   : GHC.Base.Eq_ (JointDmd s u) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___JointDmd_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___JointDmd_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__JointDmd' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__ExnStr' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__Str' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__StrDmd' *)

Local Definition Eq___Count_op_zeze__ : Count -> Count -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | One, One => true
    | Many, Many => true
    | _, _ => false
    end.

Local Definition Eq___Count_op_zsze__ : Count -> Count -> bool :=
  fun x y => negb (Eq___Count_op_zeze__ x y).

Program Instance Eq___Count : GHC.Base.Eq_ Count :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Count_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Count_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__Count' *)

Local Definition Eq___Use_op_zeze__ {inst_u : Type} `{GHC.Base.Eq_ inst_u}
   : Use inst_u -> Use inst_u -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Abs, Abs => true
    | Mk_Use a1 a2, Mk_Use b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___Use_op_zsze__ {inst_u : Type} `{GHC.Base.Eq_ inst_u}
   : Use inst_u -> Use inst_u -> bool :=
  fun x y => negb (Eq___Use_op_zeze__ x y).

Program Instance Eq___Use {u : Type} `{GHC.Base.Eq_ u} : GHC.Base.Eq_ (Use u) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Use_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Use_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__Use' *)

Local Definition Eq___UseDmd_op_zeze__ : UseDmd -> UseDmd -> bool :=
  fix UseDmd_eq x y
    := let eq' : GHC.Base.Eq_ UseDmd := GHC.Base.eq_default UseDmd_eq in
       match x, y with
       | UCall a1 a2, UCall b1 b2 => andb (a1 GHC.Base.== b1) (a2 GHC.Base.== b2)
       | UProd a1, UProd b1 => a1 GHC.Base.== b1
       | UHead, UHead => true
       | Used, Used => true
       | _, _ => false
       end.

Local Definition Eq___UseDmd_op_zsze__ : UseDmd -> UseDmd -> bool :=
  fun x y => negb (Eq___UseDmd_op_zeze__ x y).

Program Instance Eq___UseDmd : GHC.Base.Eq_ UseDmd :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___UseDmd_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___UseDmd_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__UseDmd' *)

Local Definition Eq___Termination_op_zeze__ {inst_r : Type} `{GHC.Base.Eq_
  inst_r}
   : Termination inst_r -> Termination inst_r -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Diverges, Diverges => true
    | ThrowsExn, ThrowsExn => true
    | Dunno a1, Dunno b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___Termination_op_zsze__ {inst_r : Type} `{GHC.Base.Eq_
  inst_r}
   : Termination inst_r -> Termination inst_r -> bool :=
  fun x y => negb (Eq___Termination_op_zeze__ x y).

Program Instance Eq___Termination {r : Type} `{GHC.Base.Eq_ r}
   : GHC.Base.Eq_ (Termination r) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Termination_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Termination_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__Termination' *)

Local Definition Eq___CPRResult_op_zeze__ : CPRResult -> CPRResult -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoCPR, NoCPR => true
    | RetProd, RetProd => true
    | RetSum a1, RetSum b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___CPRResult_op_zsze__ : CPRResult -> CPRResult -> bool :=
  fun x y => negb (Eq___CPRResult_op_zeze__ x y).

Program Instance Eq___CPRResult : GHC.Base.Eq_ CPRResult :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___CPRResult_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___CPRResult_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__CPRResult' *)

Local Definition Eq___DmdType_op_zeze__ : DmdType -> DmdType -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_DmdType fv1 ds1 res1, Mk_DmdType fv2 ds2 res2 =>
        andb (UniqFM.nonDetUFMToList fv1 GHC.Base.== UniqFM.nonDetUFMToList fv2) (andb
              (ds1 GHC.Base.== ds2) (res1 GHC.Base.== res2))
    end.

Local Definition Eq___DmdType_op_zsze__ : DmdType -> DmdType -> bool :=
  fun x y => negb (Eq___DmdType_op_zeze__ x y).

Program Instance Eq___DmdType : GHC.Base.Eq_ DmdType :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___DmdType_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___DmdType_op_zsze__ |}.

Local Definition Eq___StrictSig_op_zeze__ : StrictSig -> StrictSig -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___StrictSig_op_zsze__ : StrictSig -> StrictSig -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___StrictSig : GHC.Base.Eq_ StrictSig :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___StrictSig_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___StrictSig_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__HsImplBang' *)

Local Definition Eq___SrcStrictness_op_zeze__
   : SrcStrictness -> SrcStrictness -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | SrcLazy, SrcLazy => true
    | SrcStrict, SrcStrict => true
    | NoSrcStrict, NoSrcStrict => true
    | _, _ => false
    end.

Local Definition Eq___SrcStrictness_op_zsze__
   : SrcStrictness -> SrcStrictness -> bool :=
  fun x y => negb (Eq___SrcStrictness_op_zeze__ x y).

Program Instance Eq___SrcStrictness : GHC.Base.Eq_ SrcStrictness :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___SrcStrictness_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___SrcStrictness_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__SrcStrictness' *)

Local Definition Eq___SrcUnpackedness_op_zeze__
   : SrcUnpackedness -> SrcUnpackedness -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | SrcUnpack, SrcUnpack => true
    | SrcNoUnpack, SrcNoUnpack => true
    | NoSrcUnpack, NoSrcUnpack => true
    | _, _ => false
    end.

Local Definition Eq___SrcUnpackedness_op_zsze__
   : SrcUnpackedness -> SrcUnpackedness -> bool :=
  fun x y => negb (Eq___SrcUnpackedness_op_zeze__ x y).

Program Instance Eq___SrcUnpackedness : GHC.Base.Eq_ SrcUnpackedness :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___SrcUnpackedness_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___SrcUnpackedness_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__SrcUnpackedness' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__HsSrcBang' *)

Local Definition Uniquable__DataCon_getUnique : DataCon -> Unique.Unique :=
  dcUnique.

Program Instance Uniquable__DataCon : Unique.Uniquable DataCon :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__DataCon_getUnique |}.

Local Definition Eq___DataCon_op_zsze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

Local Definition Eq___DataCon_op_zeze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

Program Instance Eq___DataCon : GHC.Base.Eq_ DataCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___DataCon_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___DataCon_op_zsze__ |}.

Local Definition Eq___AltCon_op_zeze__ : AltCon -> AltCon -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | DataAlt a1, DataAlt b1 => ((a1 GHC.Base.== b1))
    | LitAlt a1, LitAlt b1 => ((a1 GHC.Base.== b1))
    | DEFAULT, DEFAULT => true
    | _, _ => false
    end.

Local Definition Eq___AltCon_op_zsze__ : AltCon -> AltCon -> bool :=
  fun x y => negb (Eq___AltCon_op_zeze__ x y).

Program Instance Eq___AltCon : GHC.Base.Eq_ AltCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___AltCon_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___AltCon_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__AltCon' *)

Local Definition Eq___Tickish_op_zeze__ {inst_id : Type} `{GHC.Base.Eq_ inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | ProfNote a1 a2 a3, ProfNote b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    | HpcTick a1 a2, HpcTick b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | Breakpoint a1 a2, Breakpoint b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | SourceNote a1 a2, SourceNote b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___Tickish_op_zsze__ {inst_id : Type} `{GHC.Base.Eq_ inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => negb (Eq___Tickish_op_zeze__ x y).

Program Instance Eq___Tickish {id : Type} `{GHC.Base.Eq_ id}
   : GHC.Base.Eq_ (Tickish id) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Tickish_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Tickish_op_zsze__ |}.

Local Definition Ord__Tickish_compare {inst_id : Type} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> comparison :=
  fun a b =>
    match a with
    | ProfNote a1 a2 a3 =>
        match b with
        | ProfNote b1 b2 b3 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => Lt
            | Eq =>
                match (GHC.Base.compare a2 b2) with
                | Lt => Lt
                | Eq => (GHC.Base.compare a3 b3)
                | Gt => Gt
                end
            | Gt => Gt
            end
        | _ => Lt
        end
    | HpcTick a1 a2 =>
        match b with
        | ProfNote _ _ _ => Gt
        | HpcTick b1 b2 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => Lt
            | Eq => (GHC.Base.compare a2 b2)
            | Gt => Gt
            end
        | _ => Lt
        end
    | Breakpoint a1 a2 =>
        match b with
        | SourceNote _ _ => Lt
        | Breakpoint b1 b2 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => Lt
            | Eq => (GHC.Base.compare a2 b2)
            | Gt => Gt
            end
        | _ => Gt
        end
    | SourceNote a1 a2 =>
        match b with
        | SourceNote b1 b2 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => Lt
            | Eq => (GHC.Base.compare a2 b2)
            | Gt => Gt
            end
        | _ => Gt
        end
    end.

Local Definition Ord__Tickish_op_zl__ {inst_id : Type} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => Ord__Tickish_compare x y GHC.Base.== Lt.

Local Definition Ord__Tickish_op_zlze__ {inst_id : Type} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => Ord__Tickish_compare x y GHC.Base./= Gt.

Local Definition Ord__Tickish_op_zg__ {inst_id : Type} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => Ord__Tickish_compare x y GHC.Base.== Gt.

Local Definition Ord__Tickish_op_zgze__ {inst_id : Type} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => Ord__Tickish_compare x y GHC.Base./= Lt.

Local Definition Ord__Tickish_max {inst_id : Type} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> Tickish inst_id :=
  fun x y => if Ord__Tickish_op_zlze__ x y : bool then y else x.

Local Definition Ord__Tickish_min {inst_id : Type} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> Tickish inst_id :=
  fun x y => if Ord__Tickish_op_zlze__ x y : bool then x else y.

Program Instance Ord__Tickish {id : Type} `{GHC.Base.Ord id}
   : GHC.Base.Ord (Tickish id) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Tickish_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Tickish_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Tickish_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Tickish_op_zgze__ ;
           GHC.Base.compare__ := Ord__Tickish_compare ;
           GHC.Base.max__ := Ord__Tickish_max ;
           GHC.Base.min__ := Ord__Tickish_min |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Tickish' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Expr' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Bind' *)

Local Definition Eq___TickishScoping_op_zeze__
   : TickishScoping -> TickishScoping -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoScope, NoScope => true
    | SoftScope, SoftScope => true
    | CostCentreScope, CostCentreScope => true
    | _, _ => false
    end.

Local Definition Eq___TickishScoping_op_zsze__
   : TickishScoping -> TickishScoping -> bool :=
  fun x y => negb (Eq___TickishScoping_op_zeze__ x y).

Program Instance Eq___TickishScoping : GHC.Base.Eq_ TickishScoping :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TickishScoping_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TickishScoping_op_zsze__ |}.

Local Definition Eq___TickishPlacement_op_zeze__
   : TickishPlacement -> TickishPlacement -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | PlaceRuntime, PlaceRuntime => true
    | PlaceNonLam, PlaceNonLam => true
    | PlaceCostCentre, PlaceCostCentre => true
    | _, _ => false
    end.

Local Definition Eq___TickishPlacement_op_zsze__
   : TickishPlacement -> TickishPlacement -> bool :=
  fun x y => negb (Eq___TickishPlacement_op_zeze__ x y).

Program Instance Eq___TickishPlacement : GHC.Base.Eq_ TickishPlacement :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TickishPlacement_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TickishPlacement_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__IsOrphan' *)

Local Definition Eq___UnfoldingGuidance_op_zeze__
   : UnfoldingGuidance -> UnfoldingGuidance -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UnfWhen a1 a2 a3, UnfWhen b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    | UnfIfGoodArgs a1 a2 a3, UnfIfGoodArgs b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    | UnfNever, UnfNever => true
    | _, _ => false
    end.

Local Definition Eq___UnfoldingGuidance_op_zsze__
   : UnfoldingGuidance -> UnfoldingGuidance -> bool :=
  fun x y => negb (Eq___UnfoldingGuidance_op_zeze__ x y).

Program Instance Eq___UnfoldingGuidance : GHC.Base.Eq_ UnfoldingGuidance :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___UnfoldingGuidance_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___UnfoldingGuidance_op_zsze__ |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__EqSpec' *)

Local Definition NamedThing__DataCon_getName : DataCon -> Name.Name :=
  dcName.

Local Definition NamedThing__DataCon_getOccName : DataCon -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__DataCon_getName n).

Program Instance NamedThing__DataCon : Name.NamedThing DataCon :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__DataCon_getName ;
           Name.getOccName__ := NamedThing__DataCon_getOccName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__DataCon' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `Core.OutputableBndr__DataCon' *)

(* Skipping all instances of class `Data.Data.Data', including
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
   `Core.Binary__SrcStrictness' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__SrcUnpackedness' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__JointDmd' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__StrDmd' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__ArgStr' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__ArgUse' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__UseDmd' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Count' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TypeShape' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Termination' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__CPRResult' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__DmdType' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__StrictSig' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__StrDmd' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__ExnStr' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__ArgStr' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__Count' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__ArgUse' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__UseDmd' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__JointDmd' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__StrictSig' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__DmdType' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__DmdResult' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__CPRResult' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__RecSelParent' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__IdDetails' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__CafInfo' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TickBoxOp' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__LevityInfo' *)

Axiom patSynName : PatSyn -> Name.Name.

Local Definition NamedThing__PatSyn_getName : PatSyn -> Name.Name :=
  patSynName.

Local Definition NamedThing__PatSyn_getOccName : PatSyn -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__PatSyn_getName n).

Program Instance NamedThing__PatSyn : Name.NamedThing PatSyn :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__PatSyn_getName ;
           Name.getOccName__ := NamedThing__PatSyn_getOccName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__PatSyn' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `Core.OutputableBndr__PatSyn' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__PatSyn' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Var' *)

Local Definition NamedThing__Var_getName : Var -> Name.Name :=
  varName.

Local Definition NamedThing__Var_getOccName : Var -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__Var_getName n).

Program Instance NamedThing__Var : Name.NamedThing Var :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__Var_getName ;
           Name.getOccName__ := NamedThing__Var_getOccName |}.

Definition varUnique : Var -> Unique.Unique :=
  fun var => Unique.mkUniqueGrimily (realUnique var).

Local Definition Uniquable__Var_getUnique : Var -> Unique.Unique :=
  varUnique.

Program Instance Uniquable__Var : Unique.Uniquable Var :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__Var_getUnique |}.

Local Definition Eq___Var_op_zeze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.== realUnique b.

Local Definition Eq___Var_op_zsze__ : Var -> Var -> bool :=
  fun x y => negb (Eq___Var_op_zeze__ x y).

Program Instance Eq___Var : GHC.Base.Eq_ Var :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Var_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Var_op_zsze__ |}.

Local Definition Ord__Var_op_zl__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.< realUnique b.

Local Definition Ord__Var_op_zlze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.<= realUnique b.

Local Definition Ord__Var_op_zg__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.> realUnique b.

Local Definition Ord__Var_op_zgze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.>= realUnique b.

Definition nonDetCmpVar : Var -> Var -> comparison :=
  fun a b => Unique.nonDetCmpUnique (varUnique a) (varUnique b).

Local Definition Ord__Var_compare : Var -> Var -> comparison :=
  fun a b => nonDetCmpVar a b.

Local Definition Ord__Var_max : Var -> Var -> Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then y else x.

Local Definition Ord__Var_min : Var -> Var -> Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then x else y.

Program Instance Ord__Var : GHC.Base.Ord Var :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Var_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Var_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Var_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Var_op_zgze__ ;
           GHC.Base.compare__ := Ord__Var_compare ;
           GHC.Base.max__ := Ord__Var_max ;
           GHC.Base.min__ := Ord__Var_min |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Var' *)

Local Definition HasOccName__Var_occName : Var -> OccName.OccName :=
  Name.nameOccName GHC.Base.∘ varName.

Program Instance HasOccName__Var : OccName.HasOccName Var :=
  fun _ k__ => k__ {| OccName.occName__ := HasOccName__Var_occName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyVarBndr__ArgFlag__11' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__ArgFlag' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__TyVarBndr' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__ArgFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__InScopeSet' *)

Axiom dataConTag : DataCon -> BasicTypes.ConTag.

Axiom dataConTyCon : DataCon -> TyCon.

Local Definition Ord__AltCon_compare : AltCon -> AltCon -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | DataAlt con1, DataAlt con2 =>
        if andb Util.debugIsOn (negb (dataConTyCon con1 GHC.Base.==
                                      dataConTyCon con2)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreSyn.hs")
              #319)
        else GHC.Base.compare (dataConTag con1) (dataConTag con2)
    | DataAlt _, _ => Gt
    | _, DataAlt _ => Lt
    | LitAlt l1, LitAlt l2 => GHC.Base.compare l1 l2
    | LitAlt _, DEFAULT => Gt
    | DEFAULT, DEFAULT => Eq
    | DEFAULT, _ => Lt
    end.

Local Definition Ord__AltCon_op_zl__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base.== Lt.

Local Definition Ord__AltCon_op_zlze__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base./= Gt.

Local Definition Ord__AltCon_op_zg__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base.== Gt.

Local Definition Ord__AltCon_op_zgze__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base./= Lt.

Local Definition Ord__AltCon_max : AltCon -> AltCon -> AltCon :=
  fun x y => if Ord__AltCon_op_zlze__ x y : bool then y else x.

Local Definition Ord__AltCon_min : AltCon -> AltCon -> AltCon :=
  fun x y => if Ord__AltCon_op_zlze__ x y : bool then x else y.

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

Local Definition Eq___Class_op_zeze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.== classKey c2.

Local Definition Eq___Class_op_zsze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base./= classKey c2.

Program Instance Eq___Class : GHC.Base.Eq_ Class :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Class_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Class_op_zsze__ |}.

Local Definition Uniquable__Class_getUnique : Class -> Unique.Unique :=
  fun c => classKey c.

Program Instance Uniquable__Class : Unique.Uniquable Class :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__Class_getUnique |}.

Local Definition NamedThing__Class_getName : Class -> Name.Name :=
  fun clas => className clas.

Local Definition NamedThing__Class_getOccName : Class -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__Class_getName n).

Program Instance NamedThing__Class : Name.NamedThing Class :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__Class_getName ;
           Name.getOccName__ := NamedThing__Class_getOccName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Class' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Class' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__LiftingContext' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyThing' *)

(* Skipping instance `Core.NamedThing__TyThing' of class `Name.NamedThing' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__UnivCoProvenance' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__CoercionHole' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__CoercionHole' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TCvSubst' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Type_' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyLit' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyBinder' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Coercion' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyVarBndr__TyConBndrVis__11' *)

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

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyCon' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyConFlavour' *)

Local Definition NamedThing__TyCon_getName : TyCon -> Name.Name :=
  tyConName.

Local Definition NamedThing__TyCon_getOccName : TyCon -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__TyCon_getName n).

Program Instance NamedThing__TyCon : Name.NamedThing TyCon :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__TyCon_getName ;
           Name.getOccName__ := NamedThing__TyCon_getOccName |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__TyCon' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__Injectivity' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__EqRel' *)

Axiom mkEqSpec : TyVar -> Type_ -> EqSpec.

Axiom eqSpecTyVar : EqSpec -> TyVar.

Axiom eqSpecType : EqSpec -> Type_.

Axiom eqSpecPair : EqSpec -> (TyVar * Type_)%type.

Axiom eqSpecPreds : list EqSpec -> ThetaType.

Axiom substEqSpec : TCvSubst -> EqSpec -> EqSpec.

Axiom filterEqSpec : list EqSpec -> list TyVar -> list TyVar.

Axiom eqHsBang : HsImplBang -> HsImplBang -> bool.

Axiom isBanged : HsImplBang -> bool.

Axiom isSrcStrict : SrcStrictness -> bool.

Axiom isSrcUnpacked : SrcUnpackedness -> bool.

Axiom isMarkedStrict : StrictnessMark -> bool.

Axiom mkDataCon : Name.Name ->
                  bool ->
                  TyConRepName ->
                  list HsSrcBang ->
                  list FieldLabel.FieldLabel ->
                  list TyVar ->
                  list TyVar ->
                  list TyVarBinder ->
                  list EqSpec ->
                  ThetaType ->
                  list Type_ ->
                  Type_ -> RuntimeRepInfo -> TyCon -> ThetaType -> Id -> DataConRep -> DataCon.

(* Skipping definition `Core.mkCleanAnonTyConBinders' *)

(* Skipping definition `Core.freshNames' *)

Axiom dataConName : DataCon -> Name.Name.

Axiom dataConTagZ : DataCon -> BasicTypes.ConTagZ.

Axiom dataConOrigTyCon : DataCon -> TyCon.

Axiom dataConRepType : DataCon -> Type_.

Axiom dataConIsInfix : DataCon -> bool.

Axiom dataConUnivTyVars : DataCon -> list TyVar.

Axiom dataConExTyVars : DataCon -> list TyVar.

Axiom dataConUnivAndExTyVars : DataCon -> list TyVar.

Axiom dataConUserTyVars : DataCon -> list TyVar.

Axiom dataConUserTyVarBinders : DataCon -> list TyVarBinder.

Axiom dataConEqSpec : DataCon -> list EqSpec.

Axiom dataConTheta : DataCon -> ThetaType.

Axiom dataConWorkId : DataCon -> Id.

Axiom dataConWrapId_maybe : DataCon -> option Id.

Axiom dataConWrapId : DataCon -> Id.

Axiom dataConImplicitTyThings : DataCon -> list TyThing.

Axiom dataConFieldLabels : DataCon -> list FieldLabel.FieldLabel.

Axiom dataConFieldType : DataCon -> FieldLabel.FieldLabelString -> Type_.

Axiom dataConFieldType_maybe : DataCon ->
                               FieldLabel.FieldLabelString -> option (FieldLabel.FieldLabel * Type_)%type.

Axiom dataConSrcBangs : DataCon -> list HsSrcBang.

Axiom dataConSourceArity : DataCon -> BasicTypes.Arity.

Axiom dataConRepArity : DataCon -> BasicTypes.Arity.

Axiom isNullarySrcDataCon : DataCon -> bool.

Axiom isNullaryRepDataCon : DataCon -> bool.

Axiom dataConRepStrictness : DataCon -> list StrictnessMark.

Axiom dataConImplBangs : DataCon -> list HsImplBang.

Axiom dataConBoxer : DataCon -> option DataConBoxer.

Axiom dataConSig : DataCon ->
                   (list TyVar * ThetaType * list Type_ * Type_)%type.

Axiom dataConInstSig : DataCon ->
                       list Type_ -> (list TyVar * ThetaType * list Type_)%type.

Axiom dataConFullSig : DataCon ->
                       (list TyVar * list TyVar * list EqSpec * ThetaType * list Type_ * Type_)%type.

Axiom dataConOrigResTy : DataCon -> Type_.

Axiom dataConStupidTheta : DataCon -> ThetaType.

Axiom dataConUserType : DataCon -> Type_.

Axiom dataConInstArgTys : DataCon -> list Type_ -> list Type_.

Axiom dataConInstOrigArgTys : DataCon -> list Type_ -> list Type_.

Axiom dataConOrigArgTys : DataCon -> list Type_.

Axiom dataConRepArgTys : DataCon -> list Type_.

(* Skipping definition `Core.dataConIdentity' *)

Axiom isTupleDataCon : DataCon -> bool.

Axiom isUnboxedTupleCon : DataCon -> bool.

Axiom isUnboxedSumCon : DataCon -> bool.

Axiom isVanillaDataCon : DataCon -> bool.

Axiom specialPromotedDc : DataCon -> bool.

Axiom isLegacyPromotableDataCon : DataCon -> bool.

Axiom isLegacyPromotableTyCon : TyCon -> bool.

Axiom classDataCon : Class -> DataCon.

Axiom dataConCannotMatch : list Type_ -> DataCon -> bool.

Axiom dataConUserTyVarsArePermuted : DataCon -> bool.

Axiom promoteDataCon : DataCon -> TyCon.

Axiom splitDataProductType_maybe : Type_ ->
                                   option (TyCon * list Type_ * DataCon * list Type_)%type.

Axiom buildAlgTyCon : Name.Name ->
                      list TyVar ->
                      list Role ->
                      option CType -> ThetaType -> AlgTyConRhs -> bool -> AlgTyConFlav -> TyCon.

Axiom buildSynTyCon : Name.Name ->
                      list TyConBinder -> Kind -> list Role -> Type_ -> TyCon.

Axiom getStrDmd : forall {s : Type}, forall {u : Type}, JointDmd s u -> s.

Axiom getUseDmd : forall {s : Type}, forall {u : Type}, JointDmd s u -> u.

Axiom mkJointDmd : forall {s} {u}, s -> u -> JointDmd s u.

Axiom mkJointDmds : forall {s} {u}, list s -> list u -> list (JointDmd s u).

Axiom strBot : ArgStr.

Axiom strTop : ArgStr.

Axiom mkSCall : StrDmd -> StrDmd.

Axiom mkSProd : list ArgStr -> StrDmd.

Axiom isLazy : ArgStr -> bool.

Axiom isHyperStr : ArgStr -> bool.

Axiom lubArgStr : ArgStr -> ArgStr -> ArgStr.

Axiom lubExnStr : ExnStr -> ExnStr -> ExnStr.

Axiom lubStr : StrDmd -> StrDmd -> StrDmd.

Axiom bothArgStr : ArgStr -> ArgStr -> ArgStr.

Axiom bothExnStr : ExnStr -> ExnStr -> ExnStr.

Axiom bothStr : StrDmd -> StrDmd -> StrDmd.

Definition seqStrDmd : StrDmd -> unit :=
  fun x => tt.

Definition seqStrDmdList : list ArgStr -> unit :=
  fun x => tt.

Definition seqArgStr : ArgStr -> unit :=
  fun x => tt.

Axiom splitArgStrProdDmd : nat -> ArgStr -> option (list ArgStr).

Axiom splitStrProdDmd : nat -> StrDmd -> option (list ArgStr).

Axiom useBot : ArgUse.

Axiom useTop : ArgUse.

Axiom mkUCall : Count -> UseDmd -> UseDmd.

Axiom mkUProd : list ArgUse -> UseDmd.

Axiom lubCount : Count -> Count -> Count.

Axiom lubArgUse : ArgUse -> ArgUse -> ArgUse.

Axiom lubUse : UseDmd -> UseDmd -> UseDmd.

Axiom bothArgUse : ArgUse -> ArgUse -> ArgUse.

Axiom bothUse : UseDmd -> UseDmd -> UseDmd.

Axiom peelUseCall : UseDmd -> option (Count * UseDmd)%type.

(* Skipping definition `Core.addCaseBndrDmd' *)

Axiom markReusedDmd : ArgUse -> ArgUse.

Axiom markReused : UseDmd -> UseDmd.

Axiom isUsedMU : ArgUse -> bool.

Axiom isUsedU : UseDmd -> bool.

Definition seqUseDmd : UseDmd -> unit :=
  fun x => tt.

Definition seqArgUseList : list ArgUse -> unit :=
  fun x => tt.

Definition seqArgUse : ArgUse -> unit :=
  fun x => tt.

Axiom splitUseProdDmd : nat -> UseDmd -> option (list ArgUse).

Axiom useCount : forall {u : Type}, Use u -> Count.

Axiom bothCleanDmd : CleanDemand -> CleanDemand -> CleanDemand.

Axiom mkHeadStrict : CleanDemand -> CleanDemand.

Axiom mkOnceUsedDmd : CleanDemand -> Demand.

Axiom mkManyUsedDmd : CleanDemand -> Demand.

Axiom evalDmd : Demand.

Axiom mkProdDmd : list Demand -> CleanDemand.

Axiom mkCallDmd : CleanDemand -> CleanDemand.

Axiom mkWorkerDemand : nat -> Demand.

Axiom cleanEvalDmd : CleanDemand.

Axiom cleanEvalProdDmd : BasicTypes.Arity -> CleanDemand.

Axiom lubDmd : Demand -> Demand -> Demand.

Axiom bothDmd : Demand -> Demand -> Demand.

Axiom strictApply1Dmd : Demand.

Axiom catchArgDmd : Demand.

Axiom lazyApply1Dmd : Demand.

Axiom lazyApply2Dmd : Demand.

Axiom absDmd : Demand.

Axiom topDmd : Demand.

Axiom botDmd : Demand.

Axiom seqDmd : Demand.

Axiom oneifyDmd : Demand -> Demand.

Axiom isTopDmd : Demand -> bool.

Axiom isAbsDmd : Demand -> bool.

Axiom isSeqDmd : Demand -> bool.

Axiom isUsedOnce : Demand -> bool.

Definition seqDemand : Demand -> unit :=
  fun x => tt.

Definition seqDemandList : list Demand -> unit :=
  fun x => tt.

Axiom isStrictDmd : Demand -> bool.

Axiom isWeakDmd : Demand -> bool.

Axiom cleanUseDmd_maybe : Demand -> option UseDmd.

Axiom splitFVs : bool -> DmdEnv -> (DmdEnv * DmdEnv)%type.

(* Skipping definition `Core.trimToType' *)

Axiom splitProdDmd_maybe : Demand -> option (list Demand).

Axiom lubCPR : CPRResult -> CPRResult -> CPRResult.

Axiom lubDmdResult : DmdResult -> DmdResult -> DmdResult.

Axiom bothDmdResult : DmdResult -> Termination unit -> DmdResult.

Definition seqDmdResult : DmdResult -> unit :=
  fun x => tt.

Definition seqCPRResult : CPRResult -> unit :=
  fun x => tt.

Axiom topRes : DmdResult.

Axiom exnRes : DmdResult.

Axiom botRes : DmdResult.

Axiom cprSumRes : BasicTypes.ConTag -> DmdResult.

Axiom cprProdRes : list DmdType -> DmdResult.

Axiom vanillaCprProdRes : BasicTypes.Arity -> DmdResult.

Axiom isTopRes : DmdResult -> bool.

Axiom isBotRes : DmdResult -> bool.

Axiom trimCPRInfo : bool -> bool -> DmdResult -> DmdResult.

Axiom returnsCPR_maybe : DmdResult -> option BasicTypes.ConTag.

Axiom retCPR_maybe : CPRResult -> option BasicTypes.ConTag.

Axiom defaultDmd : forall {r}, Termination r -> Demand.

Axiom resTypeArgDmd : forall {r}, Termination r -> Demand.

Axiom lubDmdType : DmdType -> DmdType -> DmdType.

Axiom mkBothDmdArg : DmdEnv -> BothDmdArg.

Axiom toBothDmdArg : DmdType -> BothDmdArg.

Axiom bothDmdType : DmdType -> BothDmdArg -> DmdType.

Axiom emptyDmdEnv : VarEnv Demand.

Axiom nopDmdType : DmdType.

Axiom botDmdType : DmdType.

Axiom exnDmdType : DmdType.

Axiom cprProdDmdType : BasicTypes.Arity -> DmdType.

Axiom isTopDmdType : DmdType -> bool.

Axiom mkDmdType : DmdEnv -> list Demand -> DmdResult -> DmdType.

Axiom dmdTypeDepth : DmdType -> BasicTypes.Arity.

Axiom removeDmdTyArgs : DmdType -> DmdType.

Axiom ensureArgs : BasicTypes.Arity -> DmdType -> DmdType.

Definition seqDmdType : DmdType -> unit :=
  fun x => tt.

Definition seqDmdEnv : DmdEnv -> unit :=
  fun x => tt.

Axiom splitDmdTy : DmdType -> (Demand * DmdType)%type.

Axiom deferAfterIO : DmdType -> DmdType.

Axiom strictenDmd : Demand -> CleanDemand.

(* Skipping definition `Core.toCleanDmd' *)

Axiom postProcessDmdType : DmdShell -> DmdType -> BothDmdArg.

Axiom postProcessDmdResult : Str unit -> DmdResult -> DmdResult.

Axiom postProcessDmdEnv : DmdShell -> DmdEnv -> DmdEnv.

Axiom reuseEnv : DmdEnv -> DmdEnv.

Axiom postProcessUnsat : DmdShell -> DmdType -> DmdType.

Axiom postProcessDmd : DmdShell -> Demand -> Demand.

Axiom markExnStr : ArgStr -> ArgStr.

Axiom peelCallDmd : CleanDemand -> (CleanDemand * DmdShell)%type.

Axiom peelManyCalls : nat -> CleanDemand -> DmdShell.

Axiom peelFV : DmdType -> Var -> (DmdType * Demand)%type.

Axiom addDemand : Demand -> DmdType -> DmdType.

Axiom findIdDemand : DmdType -> Var -> Demand.

(* Skipping definition `Core.pprIfaceStrictSig' *)

Axiom mkStrictSig : DmdType -> StrictSig.

Axiom mkClosedStrictSig : list Demand -> DmdResult -> StrictSig.

Axiom splitStrictSig : StrictSig -> (list Demand * DmdResult)%type.

Axiom increaseStrictSigArity : nat -> StrictSig -> StrictSig.

Axiom isTopSig : StrictSig -> bool.

Axiom hasDemandEnvSig : StrictSig -> bool.

Axiom strictSigDmdEnv : StrictSig -> DmdEnv.

Axiom isBottomingSig : StrictSig -> bool.

Axiom nopSig : StrictSig.

Axiom botSig : StrictSig.

Axiom exnSig : StrictSig.

Axiom cprProdSig : BasicTypes.Arity -> StrictSig.

Definition seqStrictSig : StrictSig -> unit :=
  fun x => tt.

Axiom dmdTransformSig : StrictSig -> CleanDemand -> DmdType.

Axiom dmdTransformDataConSig : BasicTypes.Arity ->
                               StrictSig -> CleanDemand -> DmdType.

Axiom dmdTransformDictSelSig : StrictSig -> CleanDemand -> DmdType.

Axiom argsOneShots : StrictSig ->
                     BasicTypes.Arity -> list (list BasicTypes.OneShotInfo).

Axiom saturatedByOneShots : nat -> Demand -> bool.

Axiom argOneShots : Demand -> list BasicTypes.OneShotInfo.

Axiom appIsBottom : StrictSig -> nat -> bool.

Axiom zapUsageEnvSig : StrictSig -> StrictSig.

Axiom zapUsageDemand : Demand -> Demand.

Axiom zapUsedOnceDemand : Demand -> Demand.

Axiom zapUsedOnceSig : StrictSig -> StrictSig.

Axiom killUsageDemand : DynFlags.DynFlags -> Demand -> Demand.

Axiom killUsageSig : DynFlags.DynFlags -> StrictSig -> StrictSig.

Axiom killFlags : DynFlags.DynFlags -> option KillFlags.

Axiom kill_usage : KillFlags -> Demand -> Demand.

Axiom zap_musg : KillFlags -> ArgUse -> ArgUse.

Axiom zap_usg : KillFlags -> UseDmd -> UseDmd.

(* Skipping definition `Core.strictifyDictDmd' *)

Axiom mkPatSyn : Name.Name ->
                 bool ->
                 (list TyVarBinder * ThetaType)%type ->
                 (list TyVarBinder * ThetaType)%type ->
                 list Type_ ->
                 Type_ ->
                 (Id * bool)%type ->
                 option (Id * bool)%type -> list FieldLabel.FieldLabel -> PatSyn.

Axiom patSynIsInfix : PatSyn -> bool.

Axiom patSynArity : PatSyn -> BasicTypes.Arity.

Axiom patSynArgs : PatSyn -> list Type_.

Axiom patSynFieldLabels : PatSyn -> list FieldLabel.FieldLabel.

Axiom patSynFieldType : PatSyn -> FieldLabel.FieldLabelString -> Type_.

Axiom patSynUnivTyVarBinders : PatSyn -> list TyVarBinder.

Axiom patSynExTyVars : PatSyn -> list TyVar.

Axiom patSynExTyVarBinders : PatSyn -> list TyVarBinder.

Axiom patSynSig : PatSyn ->
                  (list TyVar * ThetaType * list TyVar * ThetaType * list Type_ * Type_)%type.

Axiom patSynMatcher : PatSyn -> (Id * bool)%type.

Axiom patSynBuilder : PatSyn -> option (Id * bool)%type.

Axiom tidyPatSynIds : (Id -> Id) -> PatSyn -> PatSyn.

Axiom patSynInstArgTys : PatSyn -> list Type_ -> list Type_.

Axiom patSynInstResTy : PatSyn -> list Type_ -> Type_.

(* Skipping definition `Core.pprPatSynType' *)

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

(* Skipping definition `Core.classSCSelId' *)

Axiom classMethods : Class -> list Id.

Axiom classOpItems : Class -> list ClassOpItem.

Axiom classATs : Class -> list TyCon.

Axiom classATItems : Class -> list ClassATItem.

Axiom classSCTheta : Class -> list PredType.

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

Axiom pprCoAxiom : forall {br : BranchFlag}, CoAxiom br -> GHC.Base.String.

Axiom pprCoAxBranch : forall {br : BranchFlag},
                      CoAxiom br -> CoAxBranch -> GHC.Base.String.

Axiom pprCoAxBranchHdr : forall {br : BranchFlag},
                         CoAxiom br -> BranchIndex -> GHC.Base.String.

Axiom ppr_co_ax_branch : forall {br},
                         (TyCon -> Type_ -> GHC.Base.String) ->
                         CoAxiom br -> CoAxBranch -> GHC.Base.String.

Axiom decomposeCo : BasicTypes.Arity -> Coercion -> list Coercion.

Axiom decomposeFunCo : Coercion -> (Coercion * Coercion)%type.

Axiom getCoVar_maybe : Coercion -> option CoVar.

Axiom splitTyConAppCo_maybe : Coercion -> option (TyCon * list Coercion)%type.

Axiom splitAppCo_maybe : Coercion -> option (Coercion * Coercion)%type.

Axiom splitFunCo_maybe : Coercion -> option (Coercion * Coercion)%type.

Axiom splitForAllCo_maybe : Coercion ->
                            option (TyVar * Coercion * Coercion)%type.

Axiom coVarTypes : CoVar -> Pair.Pair Type_.

Axiom coVarKindsTypesRole : CoVar -> (Kind * Kind * Type_ * Type_ * Role)%type.

Axiom coVarKind : CoVar -> Type_.

Axiom coVarRole : CoVar -> Role.

Axiom mkCoercionType : Role -> Type_ -> Type_ -> Type_.

Axiom mkHeteroCoercionType : Role -> Kind -> Kind -> Type_ -> Type_ -> Type_.

Axiom mkRuntimeRepCo : forall `{Util.HasDebugCallStack}, Coercion -> Coercion.

Axiom isReflCoVar_maybe : CoVar -> option Coercion.

Axiom isReflCo : Coercion -> bool.

Axiom isReflCo_maybe : Coercion -> option (Type_ * Role)%type.

Axiom isReflexiveCo : Coercion -> bool.

Axiom isReflexiveCo_maybe : Coercion -> option (Type_ * Role)%type.

Axiom mkReflCo : Role -> Type_ -> Coercion.

Axiom mkRepReflCo : Type_ -> Coercion.

Axiom mkNomReflCo : Type_ -> Coercion.

Axiom mkTyConAppCo : forall `{Util.HasDebugCallStack},
                     Role -> TyCon -> list Coercion -> Coercion.

Axiom mkFunCo : Role -> Coercion -> Coercion -> Coercion.

Axiom mkFunCos : Role -> list Coercion -> Coercion -> Coercion.

Axiom mkAppCo : Coercion -> Coercion -> Coercion.

Axiom mkAppCos : Coercion -> list Coercion -> Coercion.

Axiom mkTransAppCo : Role ->
                     Coercion ->
                     Type_ -> Type_ -> Role -> Coercion -> Type_ -> Type_ -> Role -> Coercion.

Axiom mkForAllCo : TyVar -> Coercion -> Coercion -> Coercion.

Axiom mkForAllCos : list (TyVar * Coercion)%type -> Coercion -> Coercion.

Axiom mkHomoForAllCos : list TyVar -> Coercion -> Coercion.

Axiom mkHomoForAllCos_NoRefl : list TyVar -> Coercion -> Coercion.

(* Skipping definition `Core.mkCoVarCo' *)

(* Skipping definition `Core.mkCoVarCos' *)

Axiom isCoVar_maybe : Coercion -> option CoVar.

Axiom mkAxInstCo : forall {br : BranchFlag},
                   Role -> CoAxiom br -> BranchIndex -> list Type_ -> list Coercion -> Coercion.

Axiom mkAxiomInstCo : CoAxiom Branched ->
                      BranchIndex -> list Coercion -> Coercion.

Axiom mkUnbranchedAxInstCo : Role ->
                             CoAxiom Unbranched -> list Type_ -> list Coercion -> Coercion.

Axiom mkAxInstRHS : forall {br : BranchFlag},
                    CoAxiom br -> BranchIndex -> list Type_ -> list Coercion -> Type_.

Axiom mkUnbranchedAxInstRHS : CoAxiom Unbranched ->
                              list Type_ -> list Coercion -> Type_.

Axiom mkAxInstLHS : forall {br : BranchFlag},
                    CoAxiom br -> BranchIndex -> list Type_ -> list Coercion -> Type_.

Axiom mkUnbranchedAxInstLHS : CoAxiom Unbranched ->
                              list Type_ -> list Coercion -> Type_.

Axiom mkUnsafeCo : Role -> Type_ -> Type_ -> Coercion.

Axiom mkHoleCo : CoercionHole -> Coercion.

Axiom mkUnivCo : UnivCoProvenance -> Role -> Type_ -> Type_ -> Coercion.

Axiom mkSymCo : Coercion -> Coercion.

Axiom mkTransCo : Coercion -> Coercion -> Coercion.

Axiom mkNthCoRole : Role -> nat -> Coercion -> Coercion.

Axiom mkNthCo : nat -> Coercion -> Coercion.

Axiom mkLRCo : BasicTypes.LeftOrRight -> Coercion -> Coercion.

Axiom mkInstCo : Coercion -> Coercion -> Coercion.

Axiom mkCoherenceCo : Coercion -> Coercion -> Coercion.

Axiom mkCoherenceRightCo : Coercion -> Coercion -> Coercion.

Axiom mkCoherenceLeftCo : Coercion -> Coercion -> Coercion.

Axiom mkKindCo : Coercion -> Coercion.

Axiom mkSubCo : Coercion -> Coercion.

Axiom downgradeRole_maybe : Role -> Role -> Coercion -> option Coercion.

Axiom downgradeRole : Role -> Role -> Coercion -> Coercion.

(* Skipping definition `Core.maybeSubCo' *)

Axiom mkAxiomRuleCo : CoAxiomRule -> list Coercion -> Coercion.

Axiom mkProofIrrelCo : Role -> Coercion -> Coercion -> Coercion -> Coercion.

Axiom setNominalRole_maybe : Coercion -> option Coercion.

Axiom mkPhantomCo : Coercion -> Type_ -> Type_ -> Coercion.

Axiom mkHomoPhantomCo : Type_ -> Type_ -> Coercion.

Axiom toPhantomCo : Coercion -> Coercion.

Axiom applyRoles : TyCon -> list Coercion -> list Coercion.

Axiom tyConRolesX : Role -> TyCon -> list Role.

Axiom tyConRolesRepresentational : TyCon -> list Role.

Axiom nthRole : Role -> TyCon -> nat -> Role.

Axiom ltRole : Role -> Role -> bool.

Axiom promoteCoercion : Coercion -> Coercion.

Axiom instCoercion : Pair.Pair Type_ -> Coercion -> Coercion -> option Coercion.

Axiom instCoercions : Coercion -> list Coercion -> option Coercion.

Axiom castCoercionKind : Coercion -> Coercion -> Coercion -> Coercion.

Axiom mkPiCos : Role -> list Var -> Coercion -> Coercion.

Axiom mkPiCo : Role -> Var -> Coercion -> Coercion.

Axiom mkCoCast : Coercion -> Coercion -> Coercion.

Axiom instNewTyCon_maybe : TyCon ->
                           list Type_ -> option (Type_ * Coercion)%type.

Axiom mapStepResult : forall {ev1 : Type},
                      forall {ev2 : Type},
                      (ev1 -> ev2) -> NormaliseStepResult ev1 -> NormaliseStepResult ev2.

Axiom composeSteppers : forall {ev : Type},
                        NormaliseStepper ev -> NormaliseStepper ev -> NormaliseStepper ev.

Axiom unwrapNewTypeStepper : NormaliseStepper Coercion.

Axiom topNormaliseTypeX : forall {ev : Type},
                          NormaliseStepper ev -> (ev -> ev -> ev) -> Type_ -> option (ev * Type_)%type.

Axiom topNormaliseNewType_maybe : Type_ -> option (Coercion * Type_)%type.

Axiom eqCoercion : Coercion -> Coercion -> bool.

Axiom eqCoercionX : RnEnv2 -> Coercion -> Coercion -> bool.

Axiom liftCoSubstWithEx : Role ->
                          list TyVar ->
                          list Coercion ->
                          list TyVar -> list Type_ -> ((Type_ -> Coercion) * list Type_)%type.

Axiom liftCoSubstWith : Role ->
                        list TyCoVar -> list Coercion -> Type_ -> Coercion.

Axiom liftCoSubst : forall `{Util.HasDebugCallStack},
                    Role -> LiftingContext -> Type_ -> Coercion.

Axiom emptyLiftingContext : InScopeSet -> LiftingContext.

Axiom mkLiftingContext : list (TyCoVar * Coercion)%type -> LiftingContext.

Axiom mkSubstLiftingContext : TCvSubst -> LiftingContext.

Axiom extendLiftingContext : LiftingContext ->
                             TyVar -> Coercion -> LiftingContext.

Axiom extendLiftingContextEx : LiftingContext ->
                               list (TyVar * Type_)%type -> LiftingContext.

Axiom zapLiftingContext : LiftingContext -> LiftingContext.

Axiom substForAllCoBndrCallbackLC : bool ->
                                    (Coercion -> Coercion) ->
                                    LiftingContext -> TyVar -> Coercion -> (LiftingContext * TyVar * Coercion)%type.

Axiom ty_co_subst : LiftingContext -> Role -> Type_ -> Coercion.

Axiom liftCoSubstTyVar : LiftingContext -> Role -> TyVar -> option Coercion.

Axiom liftCoSubstVarBndr : LiftingContext ->
                           TyVar -> (LiftingContext * TyVar * Coercion)%type.

Axiom liftCoSubstVarBndrCallback : forall {a : Type},
                                   (LiftingContext -> Type_ -> (Coercion * a)%type) ->
                                   LiftingContext -> TyVar -> (LiftingContext * TyVar * Coercion * a)%type.

Axiom isMappedByLC : TyCoVar -> LiftingContext -> bool.

Axiom substLeftCo : LiftingContext -> Coercion -> Coercion.

Axiom substRightCo : LiftingContext -> Coercion -> Coercion.

Axiom swapLiftCoEnv : LiftCoEnv -> LiftCoEnv.

Axiom lcSubstLeft : LiftingContext -> TCvSubst.

Axiom lcSubstRight : LiftingContext -> TCvSubst.

Axiom liftEnvSubstLeft : TCvSubst -> LiftCoEnv -> TCvSubst.

Axiom liftEnvSubstRight : TCvSubst -> LiftCoEnv -> TCvSubst.

Axiom liftEnvSubst : (forall {a}, Pair.Pair a -> a) ->
                     TCvSubst -> LiftCoEnv -> TCvSubst.

Axiom lcTCvSubst : LiftingContext -> TCvSubst.

Axiom lcInScopeSet : LiftingContext -> InScopeSet.

Axiom seqCo : Coercion -> unit.

Axiom seqProv : UnivCoProvenance -> unit.

Axiom seqCos : list Coercion -> unit.

Axiom coercionType : Coercion -> Type_.

Axiom coercionKind : Coercion -> Pair.Pair Type_.

Axiom coercionKinds : list Coercion -> Pair.Pair (list Type_).

Axiom coercionKindRole : Coercion -> (Pair.Pair Type_ * Role)%type.

Axiom coercionRole : Coercion -> Role.

Axiom pprShortTyThing : TyThing -> GHC.Base.String.

Axiom pprTyThingCategory : TyThing -> GHC.Base.String.

Axiom tyThingCategory : TyThing -> GHC.Base.String.

Axiom delBinderVar : VarSet -> TyVarBinder -> VarSet.

Axiom isInvisibleBinder : TyBinder -> bool.

Axiom isVisibleBinder : TyBinder -> bool.

(* Skipping definition `Core.mkTyVarTy' *)

(* Skipping definition `Core.mkTyVarTys' *)

Axiom mkFunTy : Type_ -> Type_ -> Type_.

Axiom mkFunTys : list Type_ -> Type_ -> Type_.

Axiom mkForAllTy : TyVar -> ArgFlag -> Type_ -> Type_.

Axiom mkForAllTys : list TyVarBinder -> Type_ -> Type_.

Axiom mkPiTy : TyBinder -> Type_ -> Type_.

Axiom mkPiTys : list TyBinder -> Type_ -> Type_.

Axiom isCoercionType : Type_ -> bool.

Axiom mkTyConTy : TyCon -> Type_.

Axiom is_TYPE : (Type_ -> bool) -> Kind -> bool.

Axiom isLiftedTypeKind : Kind -> bool.

Axiom isUnliftedTypeKind : Kind -> bool.

Axiom isRuntimeRepTy : Type_ -> bool.

Axiom isRuntimeRepVar : TyVar -> bool.

Axiom coHoleCoVar : CoercionHole -> CoVar.

Axiom tyCoVarsOfType : Type_ -> TyCoVarSet.

Axiom tyCoVarsOfTypeDSet : Type_ -> DTyCoVarSet.

Axiom tyCoVarsOfTypeList : Type_ -> list TyCoVar.

(* Skipping definition `Core.tyCoFVsOfType' *)

(* Skipping definition `Core.tyCoFVsBndr' *)

Axiom tyCoVarsOfTypes : list Type_ -> TyCoVarSet.

Axiom tyCoVarsOfTypesSet : TyVarEnv Type_ -> TyCoVarSet.

Axiom tyCoVarsOfTypesDSet : list Type_ -> DTyCoVarSet.

Axiom tyCoVarsOfTypesList : list Type_ -> list TyCoVar.

(* Skipping definition `Core.tyCoFVsOfTypes' *)

Axiom tyCoVarsOfCo : Coercion -> TyCoVarSet.

Axiom tyCoVarsOfCoDSet : Coercion -> DTyCoVarSet.

Axiom tyCoVarsOfCoList : Coercion -> list TyCoVar.

(* Skipping definition `Core.tyCoFVsOfCo' *)

(* Skipping definition `Core.tyCoFVsOfCoVar' *)

Axiom tyCoVarsOfProv : UnivCoProvenance -> TyCoVarSet.

(* Skipping definition `Core.tyCoFVsOfProv' *)

Axiom tyCoVarsOfCos : list Coercion -> TyCoVarSet.

Axiom tyCoVarsOfCosSet : CoVarEnv Coercion -> TyCoVarSet.

(* Skipping definition `Core.tyCoFVsOfCos' *)

Axiom coVarsOfType : Type_ -> CoVarSet.

Axiom coVarsOfTypes : list Type_ -> TyCoVarSet.

Axiom coVarsOfCo : Coercion -> CoVarSet.

Axiom coVarsOfCoVar : CoVar -> CoVarSet.

Axiom coVarsOfProv : UnivCoProvenance -> CoVarSet.

Axiom coVarsOfCos : list Coercion -> CoVarSet.

Axiom closeOverKinds : TyVarSet -> TyVarSet.

(* Skipping definition `Core.closeOverKindsFV' *)

Axiom closeOverKindsList : list TyVar -> list TyVar.

Axiom closeOverKindsDSet : DTyVarSet -> DTyVarSet.

(* Skipping definition `Core.injectiveVarsOfBinder' *)

(* Skipping definition `Core.injectiveVarsOfType' *)

Axiom noFreeVarsOfType : Type_ -> bool.

Axiom noFreeVarsOfCo : Coercion -> bool.

Axiom noFreeVarsOfProv : UnivCoProvenance -> bool.

Axiom emptyTvSubstEnv : TvSubstEnv.

Axiom emptyCvSubstEnv : CvSubstEnv.

Axiom composeTCvSubstEnv : InScopeSet ->
                           (TvSubstEnv * CvSubstEnv)%type ->
                           (TvSubstEnv * CvSubstEnv)%type -> (TvSubstEnv * CvSubstEnv)%type.

Axiom composeTCvSubst : TCvSubst -> TCvSubst -> TCvSubst.

Axiom emptyTCvSubst : TCvSubst.

Axiom mkEmptyTCvSubst : InScopeSet -> TCvSubst.

Axiom isEmptyTCvSubst : TCvSubst -> bool.

Axiom mkTCvSubst : InScopeSet -> (TvSubstEnv * CvSubstEnv)%type -> TCvSubst.

Axiom mkTvSubst : InScopeSet -> TvSubstEnv -> TCvSubst.

Axiom getTvSubstEnv : TCvSubst -> TvSubstEnv.

Axiom getCvSubstEnv : TCvSubst -> CvSubstEnv.

Axiom getTCvInScope : TCvSubst -> InScopeSet.

Axiom getTCvSubstRangeFVs : TCvSubst -> VarSet.

Axiom isInScope : Var -> TCvSubst -> bool.

Axiom notElemTCvSubst : Var -> TCvSubst -> bool.

Axiom setTvSubstEnv : TCvSubst -> TvSubstEnv -> TCvSubst.

Axiom setCvSubstEnv : TCvSubst -> CvSubstEnv -> TCvSubst.

Axiom zapTCvSubst : TCvSubst -> TCvSubst.

Axiom extendTCvInScope : TCvSubst -> Var -> TCvSubst.

Axiom extendTCvInScopeList : TCvSubst -> list Var -> TCvSubst.

Axiom extendTCvInScopeSet : TCvSubst -> VarSet -> TCvSubst.

Axiom extendTCvSubst : TCvSubst -> TyCoVar -> Type_ -> TCvSubst.

Axiom extendTvSubst : TCvSubst -> TyVar -> Type_ -> TCvSubst.

Axiom extendTvSubstBinderAndInScope : TCvSubst -> TyBinder -> Type_ -> TCvSubst.

Axiom extendTvSubstWithClone : TCvSubst -> TyVar -> TyVar -> TCvSubst.

Axiom extendCvSubst : TCvSubst -> CoVar -> Coercion -> TCvSubst.

Axiom extendCvSubstWithClone : TCvSubst -> CoVar -> CoVar -> TCvSubst.

Axiom extendTvSubstAndInScope : TCvSubst -> TyVar -> Type_ -> TCvSubst.

Axiom extendTvSubstList : TCvSubst -> list Var -> list Type_ -> TCvSubst.

Axiom unionTCvSubst : TCvSubst -> TCvSubst -> TCvSubst.

Axiom mkTyCoInScopeSet : list Type_ -> list Coercion -> InScopeSet.

Axiom zipTvSubst : list TyVar -> list Type_ -> TCvSubst.

Axiom zipCvSubst : list CoVar -> list Coercion -> TCvSubst.

Axiom mkTvSubstPrs : list (TyVar * Type_)%type -> TCvSubst.

Axiom zipTyEnv : list TyVar -> list Type_ -> TvSubstEnv.

Axiom zipCoEnv : list CoVar -> list Coercion -> CvSubstEnv.

Axiom substTyWith : forall `{Util.HasDebugCallStack},
                    list TyVar -> list Type_ -> Type_ -> Type_.

Axiom substTyWithUnchecked : list TyVar -> list Type_ -> Type_ -> Type_.

Axiom substTyWithInScope : InScopeSet ->
                           list TyVar -> list Type_ -> Type_ -> Type_.

Axiom substCoWith : forall `{Util.HasDebugCallStack},
                    list TyVar -> list Type_ -> Coercion -> Coercion.

Axiom substCoWithUnchecked : list TyVar -> list Type_ -> Coercion -> Coercion.

Axiom substTyWithCoVars : list CoVar -> list Coercion -> Type_ -> Type_.

Axiom substTysWith : list TyVar -> list Type_ -> list Type_ -> list Type_.

Axiom substTysWithCoVars : list CoVar ->
                           list Coercion -> list Type_ -> list Type_.

Axiom substTyAddInScope : TCvSubst -> Type_ -> Type_.

Axiom isValidTCvSubst : TCvSubst -> bool.

Axiom checkValidSubst : forall {a : Type},
                        forall `{Util.HasDebugCallStack},
                        TCvSubst -> list Type_ -> list Coercion -> a -> a.

Axiom substTy : forall `{Util.HasDebugCallStack}, TCvSubst -> Type_ -> Type_.

Axiom substTyUnchecked : TCvSubst -> Type_ -> Type_.

Axiom substTys : forall `{Util.HasDebugCallStack},
                 TCvSubst -> list Type_ -> list Type_.

Axiom substTysUnchecked : TCvSubst -> list Type_ -> list Type_.

Axiom substTheta : forall `{Util.HasDebugCallStack},
                   TCvSubst -> ThetaType -> ThetaType.

Axiom substThetaUnchecked : TCvSubst -> ThetaType -> ThetaType.

Axiom subst_ty : TCvSubst -> Type_ -> Type_.

Axiom substTyVar : TCvSubst -> TyVar -> Type_.

Axiom substTyVars : TCvSubst -> list TyVar -> list Type_.

Axiom lookupTyVar : TCvSubst -> TyVar -> option Type_.

Axiom substCo : forall `{Util.HasDebugCallStack},
                TCvSubst -> Coercion -> Coercion.

Axiom substCoUnchecked : TCvSubst -> Coercion -> Coercion.

Axiom substCos : forall `{Util.HasDebugCallStack},
                 TCvSubst -> list Coercion -> list Coercion.

Axiom subst_co : TCvSubst -> Coercion -> Coercion.

Axiom substForAllCoBndr : TCvSubst ->
                          TyVar -> Coercion -> (TCvSubst * TyVar * Coercion)%type.

Axiom substForAllCoBndrUnchecked : TCvSubst ->
                                   TyVar -> Coercion -> (TCvSubst * TyVar * Coercion)%type.

Axiom substForAllCoBndrCallback : bool ->
                                  (Coercion -> Coercion) ->
                                  TCvSubst -> TyVar -> Coercion -> (TCvSubst * TyVar * Coercion)%type.

Axiom substCoVar : TCvSubst -> CoVar -> Coercion.

Axiom substCoVars : TCvSubst -> list CoVar -> list Coercion.

Axiom lookupCoVar : TCvSubst -> Var -> option Coercion.

Axiom substTyVarBndr : forall `{Util.HasDebugCallStack},
                       TCvSubst -> TyVar -> (TCvSubst * TyVar)%type.

Axiom substTyVarBndrUnchecked : TCvSubst -> TyVar -> (TCvSubst * TyVar)%type.

Axiom substTyVarBndrCallback : (TCvSubst -> Type_ -> Type_) ->
                               TCvSubst -> TyVar -> (TCvSubst * TyVar)%type.

Axiom substCoVarBndr : TCvSubst -> CoVar -> (TCvSubst * CoVar)%type.

Axiom cloneTyVarBndr : TCvSubst ->
                       TyVar -> Unique.Unique -> (TCvSubst * TyVar)%type.

Axiom cloneTyVarBndrs : TCvSubst ->
                        list TyVar -> UniqSupply.UniqSupply -> (TCvSubst * list TyVar)%type.

Axiom pprType : Type_ -> GHC.Base.String.

Axiom pprParendType : Type_ -> GHC.Base.String.

Axiom pprPrecType : BasicTypes.TyPrec -> Type_ -> GHC.Base.String.

Axiom pprTyLit : TyLit -> GHC.Base.String.

Axiom pprKind : Kind -> GHC.Base.String.

Axiom pprParendKind : Kind -> GHC.Base.String.

(* Skipping definition `Core.tidyToIfaceTypeSty' *)

(* Skipping definition `Core.tidyToIfaceType' *)

Axiom pprCo : Coercion -> GHC.Base.String.

Axiom pprParendCo : Coercion -> GHC.Base.String.

(* Skipping definition `Core.tidyToIfaceCoSty' *)

(* Skipping definition `Core.tidyToIfaceCo' *)

Axiom pprClassPred : Class -> list Type_ -> GHC.Base.String.

Axiom pprTheta : ThetaType -> GHC.Base.String.

Axiom pprParendTheta : ThetaType -> GHC.Base.String.

Axiom pprThetaArrowTy : ThetaType -> GHC.Base.String.

Axiom pprSigmaType : Type_ -> GHC.Base.String.

Axiom pprForAll : list TyVarBinder -> GHC.Base.String.

Axiom pprUserForAll : list TyVarBinder -> GHC.Base.String.

Axiom pprTvBndrs : list TyVarBinder -> GHC.Base.String.

Axiom pprTvBndr : TyVarBinder -> GHC.Base.String.

Axiom pprTyVars : list TyVar -> GHC.Base.String.

Axiom pprTyVar : TyVar -> GHC.Base.String.

Axiom debugPprType : Type_ -> GHC.Base.String.

Axiom debug_ppr_ty : BasicTypes.TyPrec -> Type_ -> GHC.Base.String.

Axiom pprDataCons : TyCon -> GHC.Base.String.

Axiom pprDataConWithArgs : DataCon -> GHC.Base.String.

Axiom pprTypeApp : TyCon -> list Type_ -> GHC.Base.String.

Axiom ppSuggestExplicitKinds : GHC.Base.String.

Axiom tidyTyCoVarBndrs : TidyEnv ->
                         list TyCoVar -> (TidyEnv * list TyCoVar)%type.

Axiom tidyTyCoVarBndr : TidyEnv -> TyCoVar -> (TidyEnv * TyCoVar)%type.

Axiom getHelpfulOccName : TyCoVar -> OccName.OccName.

Axiom tidyTyVarBinder : forall {vis : Type},
                        TidyEnv -> TyVarBndr TyVar vis -> (TidyEnv * TyVarBndr TyVar vis)%type.

Axiom tidyTyVarBinders : forall {vis : Type},
                         TidyEnv ->
                         list (TyVarBndr TyVar vis) -> (TidyEnv * list (TyVarBndr TyVar vis))%type.

Axiom tidyFreeTyCoVars : TidyEnv -> list TyCoVar -> TidyEnv.

Axiom tidyOpenTyCoVars : TidyEnv ->
                         list TyCoVar -> (TidyEnv * list TyCoVar)%type.

Axiom tidyOpenTyCoVar : TidyEnv -> TyCoVar -> (TidyEnv * TyCoVar)%type.

Axiom tidyTyVarOcc : TidyEnv -> TyVar -> TyVar.

Axiom tidyTypes : TidyEnv -> list Type_ -> list Type_.

Axiom tidyType : TidyEnv -> Type_ -> Type_.

Axiom mkForAllTys' : list (TyVar * ArgFlag)%type -> Type_ -> Type_.

Axiom splitForAllTys' : Type_ -> (list TyVar * list ArgFlag * Type_)%type.

Axiom tidyOpenTypes : TidyEnv -> list Type_ -> (TidyEnv * list Type_)%type.

Axiom tidyOpenType : TidyEnv -> Type_ -> (TidyEnv * Type_)%type.

Axiom tidyTopType : Type_ -> Type_.

Axiom tidyOpenKind : TidyEnv -> Kind -> (TidyEnv * Kind)%type.

Axiom tidyKind : TidyEnv -> Kind -> Kind.

Axiom tidyCo : TidyEnv -> Coercion -> Coercion.

Axiom tidyCos : TidyEnv -> list Coercion -> list Coercion.

Axiom typeSize : Type_ -> nat.

Axiom coercionSize : Coercion -> nat.

Axiom provSize : UnivCoProvenance -> nat.

Axiom mkAnonTyConBinder : TyVar -> TyConBinder.

Axiom mkAnonTyConBinders : list TyVar -> list TyConBinder.

Axiom mkNamedTyConBinder : ArgFlag -> TyVar -> TyConBinder.

Axiom mkNamedTyConBinders : ArgFlag -> list TyVar -> list TyConBinder.

Axiom tyConBinderArgFlag : TyConBinder -> ArgFlag.

Axiom isNamedTyConBinder : TyConBinder -> bool.

Axiom isVisibleTyConBinder : forall {tv : Type},
                             TyVarBndr tv TyConBndrVis -> bool.

Axiom isVisibleTcbVis : TyConBndrVis -> bool.

Axiom isInvisibleTyConBinder : forall {tv : Type},
                               TyVarBndr tv TyConBndrVis -> bool.

Axiom mkTyConKind : list TyConBinder -> Kind -> Kind.

Axiom tyConTyVarBinders : list TyConBinder -> list TyVarBinder.

Axiom tyConVisibleTyVars : TyCon -> list TyVar.

Axiom visibleDataCons : AlgTyConRhs -> list DataCon.

Axiom okParent : Name.Name -> AlgTyConFlav -> bool.

Axiom isNoParent : AlgTyConFlav -> bool.

Axiom tyConRepName_maybe : TyCon -> option TyConRepName.

Axiom mkPrelTyConRepName : Name.Name -> TyConRepName.

Axiom tyConRepModOcc : Module.Module ->
                       OccName.OccName -> (Module.Module * OccName.OccName)%type.

Axiom isVoidRep : PrimRep -> bool.

Axiom isGcPtrRep : PrimRep -> bool.

(* Skipping definition `Core.primRepSizeB' *)

Axiom primElemRepSizeB : PrimElemRep -> nat.

Axiom primRepIsFloat : PrimRep -> option bool.

Axiom tyConFieldLabels : TyCon -> list FieldLabel.FieldLabel.

Axiom tyConFieldLabelEnv : TyCon -> FieldLabel.FieldLabelEnv.

Axiom lookupTyConFieldLabel : FieldLabel.FieldLabelString ->
                              TyCon -> option FieldLabel.FieldLabel.

Axiom fieldsOfAlgTcRhs : AlgTyConRhs -> FieldLabel.FieldLabelEnv.

Axiom mkFunTyCon : Name.Name -> list TyConBinder -> Name.Name -> TyCon.

Axiom mkAlgTyCon : Name.Name ->
                   list TyConBinder ->
                   Kind ->
                   list Role ->
                   option CType -> list PredType -> AlgTyConRhs -> AlgTyConFlav -> bool -> TyCon.

Axiom mkClassTyCon : Name.Name ->
                     list TyConBinder -> list Role -> AlgTyConRhs -> Class -> Name.Name -> TyCon.

Axiom mkTupleTyCon : Name.Name ->
                     list TyConBinder ->
                     Kind ->
                     BasicTypes.Arity -> DataCon -> BasicTypes.TupleSort -> AlgTyConFlav -> TyCon.

Axiom mkSumTyCon : Name.Name ->
                   list TyConBinder ->
                   Kind -> BasicTypes.Arity -> list TyVar -> list DataCon -> AlgTyConFlav -> TyCon.

Axiom mkTcTyCon : Name.Name ->
                  list TyConBinder ->
                  Kind -> list (Name.Name * TyVar)%type -> TyConFlavour -> TyCon.

Axiom mkPrimTyCon : Name.Name -> list TyConBinder -> Kind -> list Role -> TyCon.

Axiom mkKindTyCon : Name.Name ->
                    list TyConBinder -> Kind -> list Role -> Name.Name -> TyCon.

Axiom mkLiftedPrimTyCon : Name.Name ->
                          list TyConBinder -> Kind -> list Role -> TyCon.

Axiom mkPrimTyCon' : Name.Name ->
                     list TyConBinder -> Kind -> list Role -> bool -> option TyConRepName -> TyCon.

Axiom mkSynonymTyCon : Name.Name ->
                       list TyConBinder -> Kind -> list Role -> Type_ -> bool -> bool -> TyCon.

Axiom mkFamilyTyCon : Name.Name ->
                      list TyConBinder ->
                      Kind ->
                      option Name.Name -> FamTyConFlav -> option Class -> Injectivity -> TyCon.

Axiom mkPromotedDataCon : DataCon ->
                          Name.Name ->
                          TyConRepName ->
                          list TyConBinder -> Kind -> list Role -> RuntimeRepInfo -> TyCon.

Axiom isFunTyCon : TyCon -> bool.

Axiom isAbstractTyCon : TyCon -> bool.

Axiom makeRecoveryTyCon : TyCon -> TyCon.

Axiom isPrimTyCon : TyCon -> bool.

Axiom isUnliftedTyCon : TyCon -> bool.

Axiom isAlgTyCon : TyCon -> bool.

Axiom isVanillaAlgTyCon : TyCon -> bool.

Axiom isDataTyCon : TyCon -> bool.

Axiom isInjectiveTyCon : TyCon -> Role -> bool.

Axiom isGenerativeTyCon : TyCon -> Role -> bool.

Axiom isGenInjAlgRhs : AlgTyConRhs -> bool.

Axiom isNewTyCon : TyCon -> bool.

Axiom unwrapNewTyCon_maybe : TyCon ->
                             option (list TyVar * Type_ * CoAxiom Unbranched)%type.

Axiom unwrapNewTyConEtad_maybe : TyCon ->
                                 option (list TyVar * Type_ * CoAxiom Unbranched)%type.

Axiom isProductTyCon : TyCon -> bool.

Axiom isDataProductTyCon_maybe : TyCon -> option DataCon.

Axiom isDataSumTyCon_maybe : TyCon -> option (list DataCon).

Axiom isTypeSynonymTyCon : TyCon -> bool.

Axiom isTauTyCon : TyCon -> bool.

Axiom isFamFreeTyCon : TyCon -> bool.

Axiom mightBeUnsaturatedTyCon : TyCon -> bool.

Axiom isGadtSyntaxTyCon : TyCon -> bool.

Axiom isEnumerationTyCon : TyCon -> bool.

Axiom isFamilyTyCon : TyCon -> bool.

Axiom isOpenFamilyTyCon : TyCon -> bool.

Axiom isTypeFamilyTyCon : TyCon -> bool.

Axiom isDataFamilyTyCon : TyCon -> bool.

Axiom isOpenTypeFamilyTyCon : TyCon -> bool.

Axiom isClosedSynFamilyTyConWithAxiom_maybe : TyCon ->
                                              option (CoAxiom Branched).

Axiom tyConInjectivityInfo : TyCon -> Injectivity.

Axiom isBuiltInSynFamTyCon_maybe : TyCon -> option BuiltInSynFamily.

Axiom isDataFamFlav : FamTyConFlav -> bool.

Axiom isTyConAssoc : TyCon -> bool.

Axiom tyConAssoc_maybe : TyCon -> option Class.

Axiom isTupleTyCon : TyCon -> bool.

Axiom tyConTuple_maybe : TyCon -> option BasicTypes.TupleSort.

Axiom isUnboxedTupleTyCon : TyCon -> bool.

Axiom isBoxedTupleTyCon : TyCon -> bool.

Axiom isUnboxedSumTyCon : TyCon -> bool.

Axiom isPromotedTupleTyCon : TyCon -> bool.

Axiom isPromotedDataCon : TyCon -> bool.

Axiom isPromotedDataCon_maybe : TyCon -> option DataCon.

Axiom isKindTyCon : TyCon -> bool.

Axiom kindTyConKeys : UniqSet.UniqSet Unique.Unique.

Axiom isLiftedTypeKindTyConName : Name.Name -> bool.

Axiom isImplicitTyCon : TyCon -> bool.

Axiom tyConCType_maybe : TyCon -> option CType.

Axiom isTcTyCon : TyCon -> bool.

Axiom isTcLevPoly : TyCon -> bool.

Axiom expandSynTyCon_maybe : forall {tyco : Type},
                             TyCon ->
                             list tyco -> option (list (TyVar * tyco)%type * Type_ * list tyco)%type.

Axiom isTyConWithSrcDataCons : TyCon -> bool.

Axiom tyConDataCons : TyCon -> list DataCon.

Axiom tyConDataCons_maybe : TyCon -> option (list DataCon).

Axiom tyConSingleDataCon_maybe : TyCon -> option DataCon.

Axiom tyConSingleDataCon : TyCon -> DataCon.

Axiom tyConSingleAlgDataCon_maybe : TyCon -> option DataCon.

Axiom tyConFamilySize : TyCon -> nat.

Axiom tyConFamilySizeAtMost : TyCon -> nat -> bool.

Axiom algTyConRhs : TyCon -> AlgTyConRhs.

Axiom tyConFamilyResVar_maybe : TyCon -> option Name.Name.

Axiom tyConRoles : TyCon -> list Role.

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

Axiom tyConRuntimeRepInfo : TyCon -> RuntimeRepInfo.

Axiom tyConFlavour : TyCon -> TyConFlavour.

Axiom tcFlavourCanBeUnsaturated : TyConFlavour -> bool.

Axiom tcFlavourIsOpen : TyConFlavour -> bool.

Axiom pprPromotionQuote : TyCon -> GHC.Base.String.

Axiom initRecTc : RecTcChecker.

Axiom checkRecTc : RecTcChecker -> TyCon -> option RecTcChecker.

Axiom tyConSkolem : TyCon -> bool.

Axiom coreView : Type_ -> option Type_.

Axiom tcView : Type_ -> option Type_.

Axiom expandTypeSynonyms : Type_ -> Type_.

Axiom mapType : forall {m : Type -> Type},
                forall {env : Type},
                forall `{GHC.Base.Monad m}, TyCoMapper env m -> env -> Type_ -> m Type_.

Axiom mapCoercion : forall {m : Type -> Type},
                    forall {env : Type},
                    forall `{GHC.Base.Monad m}, TyCoMapper env m -> env -> Coercion -> m Coercion.

Axiom getTyVar : GHC.Base.String -> Type_ -> TyVar.

Axiom isTyVarTy : Type_ -> bool.

Axiom getTyVar_maybe : Type_ -> option TyVar.

Axiom getCastedTyVar_maybe : Type_ -> option (TyVar * CoercionN)%type.

Axiom repGetTyVar_maybe : Type_ -> option TyVar.

Axiom mkAppTy : Type_ -> Type_ -> Type_.

Axiom mkAppTys : Type_ -> list Type_ -> Type_.

Axiom splitAppTy_maybe : Type_ -> option (Type_ * Type_)%type.

Axiom repSplitAppTy_maybe : forall `{Util.HasDebugCallStack},
                            Type_ -> option (Type_ * Type_)%type.

Axiom tcRepSplitAppTy_maybe : Type_ -> option (Type_ * Type_)%type.

Axiom tcSplitTyConApp_maybe : forall `{Util.HasDebugCallStack},
                              Type_ -> option (TyCon * list Type_)%type.

Axiom tcRepSplitTyConApp_maybe : forall `{Util.HasDebugCallStack},
                                 Type_ -> option (TyCon * list Type_)%type.

Axiom splitAppTy : Type_ -> (Type_ * Type_)%type.

Axiom splitAppTys : Type_ -> (Type_ * list Type_)%type.

Axiom repSplitAppTys : forall `{Util.HasDebugCallStack},
                       Type_ -> (Type_ * list Type_)%type.

Axiom mkNumLitTy : GHC.Num.Integer -> Type_.

Axiom isNumLitTy : Type_ -> option GHC.Num.Integer.

Axiom mkStrLitTy : FastString.FastString -> Type_.

Axiom isStrLitTy : Type_ -> option FastString.FastString.

Axiom userTypeError_maybe : Type_ -> option Type_.

Axiom pprUserTypeErrorTy : Type_ -> GHC.Base.String.

Axiom isFunTy : Type_ -> bool.

Axiom splitFunTy : Type_ -> (Type_ * Type_)%type.

Axiom splitFunTy_maybe : Type_ -> option (Type_ * Type_)%type.

Axiom splitFunTys : Type_ -> (list Type_ * Type_)%type.

Axiom funResultTy : Type_ -> Type_.

Axiom funArgTy : Type_ -> Type_.

Axiom piResultTy : forall `{Util.HasDebugCallStack}, Type_ -> Type_ -> Type_.

Axiom piResultTy_maybe : Type_ -> Type_ -> option Type_.

Axiom piResultTys : forall `{Util.HasDebugCallStack},
                    Type_ -> list Type_ -> Type_.

Axiom applyTysX : list TyVar -> Type_ -> list Type_ -> Type_.

Axiom mkTyConApp : TyCon -> list Type_ -> Type_.

Axiom tyConAppTyConPicky_maybe : Type_ -> option TyCon.

Axiom tyConAppTyCon_maybe : Type_ -> option TyCon.

Axiom tyConAppTyCon : Type_ -> TyCon.

Axiom tyConAppArgs_maybe : Type_ -> option (list Type_).

Axiom tyConAppArgs : Type_ -> list Type_.

Axiom tyConAppArgN : nat -> Type_ -> Type_.

Axiom splitTyConApp : Type_ -> (TyCon * list Type_)%type.

Axiom splitTyConApp_maybe : forall `{Util.HasDebugCallStack},
                            Type_ -> option (TyCon * list Type_)%type.

Axiom repSplitTyConApp_maybe : forall `{Util.HasDebugCallStack},
                               Type_ -> option (TyCon * list Type_)%type.

Axiom splitListTyConApp_maybe : Type_ -> option Type_.

Axiom nextRole : Type_ -> Role.

Axiom newTyConInstRhs : TyCon -> list Type_ -> Type_.

Axiom splitCastTy_maybe : Type_ -> option (Type_ * Coercion)%type.

Axiom mkCastTy : Type_ -> Coercion -> Type_.

Axiom tyConBindersTyBinders : list TyConBinder -> list TyBinder.

Axiom mkCoercionTy : Coercion -> Type_.

Axiom isCoercionTy : Type_ -> bool.

Axiom isCoercionTy_maybe : Type_ -> option Coercion.

Axiom stripCoercionTy : Type_ -> Coercion.

Axiom mkInvForAllTy : TyVar -> Type_ -> Type_.

Axiom mkInvForAllTys : list TyVar -> Type_ -> Type_.

Axiom mkSpecForAllTys : list TyVar -> Type_ -> Type_.

Axiom mkVisForAllTys : list TyVar -> Type_ -> Type_.

Axiom mkLamType : Var -> Type_ -> Type_.

Axiom mkLamTypes : list Var -> Type_ -> Type_.

Axiom mkTyConBindersPreferAnon : list TyVar -> Type_ -> list TyConBinder.

Axiom splitForAllTys : Type_ -> (list TyVar * Type_)%type.

Axiom splitForAllTyVarBndrs : Type_ -> (list TyVarBinder * Type_)%type.

Axiom isForAllTy : Type_ -> bool.

Axiom isPiTy : Type_ -> bool.

Axiom splitForAllTy : Type_ -> (TyVar * Type_)%type.

Axiom dropForAlls : Type_ -> Type_.

Axiom splitForAllTy_maybe : Type_ -> option (TyVar * Type_)%type.

Axiom splitPiTy_maybe : Type_ -> option (TyBinder * Type_)%type.

Axiom splitPiTy : Type_ -> (TyBinder * Type_)%type.

Axiom splitPiTys : Type_ -> (list TyBinder * Type_)%type.

Axiom splitPiTysInvisible : Type_ -> (list TyBinder * Type_)%type.

Axiom filterOutInvisibleTypes : TyCon -> list Type_ -> list Type_.

Axiom partitionInvisibles : forall {a : Type},
                            TyCon -> (a -> Type_) -> list a -> (list a * list a)%type.

Axiom isTauTy : Type_ -> bool.

Axiom mkAnonBinder : Type_ -> TyBinder.

Axiom isAnonTyBinder : TyBinder -> bool.

Axiom isNamedTyBinder : TyBinder -> bool.

Axiom tyBinderType : TyBinder -> Type_.

Axiom binderRelevantType_maybe : TyBinder -> option Type_.

Axiom caseBinder : forall {a : Type},
                   TyBinder -> (TyVarBinder -> a) -> (Type_ -> a) -> a.

Axiom isPredTy : Type_ -> bool.

Axiom isClassPred : PredType -> bool.

Axiom isEqPred : PredType -> bool.

Axiom isNomEqPred : PredType -> bool.

Axiom isIPPred : PredType -> bool.

Axiom isIPTyCon : TyCon -> bool.

Axiom isIPClass : Class -> bool.

Axiom isCTupleClass : Class -> bool.

Axiom isIPPred_maybe : Type_ -> option (FastString.FastString * Type_)%type.

Axiom mkPrimEqPredRole : Role -> Type_ -> Type_ -> PredType.

Axiom mkPrimEqPred : Type_ -> Type_ -> Type_.

Axiom mkHeteroPrimEqPred : Kind -> Kind -> Type_ -> Type_ -> Type_.

Axiom mkHeteroReprPrimEqPred : Kind -> Kind -> Type_ -> Type_ -> Type_.

Axiom splitCoercionType_maybe : Type_ -> option (Type_ * Type_)%type.

Axiom mkReprPrimEqPred : Type_ -> Type_ -> Type_.

Axiom equalityTyCon : Role -> TyCon.

Axiom mkClassPred : Class -> list Type_ -> PredType.

Axiom isDictTy : Type_ -> bool.

Axiom isDictLikeTy : Type_ -> bool.

Axiom eqRelRole : EqRel -> Role.

Axiom classifyPredType : PredType -> PredTree.

Axiom getClassPredTys : PredType -> (Class * list Type_)%type.

Axiom getClassPredTys_maybe : PredType -> option (Class * list Type_)%type.

Axiom getEqPredTys : PredType -> (Type_ * Type_)%type.

Axiom getEqPredTys_maybe : PredType -> option (Role * Type_ * Type_)%type.

Axiom getEqPredRole : PredType -> Role.

Axiom predTypeEqRel : PredType -> EqRel.

Axiom toposortTyVars : list TyCoVar -> list TyCoVar.

Axiom dVarSetElemsWellScoped : DVarSet -> list Var.

Axiom tyCoVarsOfTypeWellScoped : Type_ -> list TyVar.

Axiom tyCoVarsOfTypesWellScoped : list Type_ -> list TyVar.

Axiom mkFamilyTyConApp : TyCon -> list Type_ -> Type_.

Axiom coAxNthLHS : forall {br : BranchFlag}, CoAxiom br -> nat -> Type_.

Axiom pprSourceTyCon : TyCon -> GHC.Base.String.

Axiom isFamFreeTy : Type_ -> bool.

Axiom isLiftedType_maybe : forall `{Util.HasDebugCallStack},
                           Type_ -> option bool.

Axiom isUnliftedType : forall `{Util.HasDebugCallStack}, Type_ -> bool.

Axiom isRuntimeRepKindedTy : Type_ -> bool.

Axiom dropRuntimeRepArgs : list Type_ -> list Type_.

Axiom getRuntimeRep_maybe : forall `{Util.HasDebugCallStack},
                            Type_ -> option Type_.

Axiom getRuntimeRep : forall `{Util.HasDebugCallStack}, Type_ -> Type_.

Axiom getRuntimeRepFromKind : forall `{Util.HasDebugCallStack}, Type_ -> Type_.

Axiom getRuntimeRepFromKind_maybe : forall `{Util.HasDebugCallStack},
                                    Type_ -> option Type_.

Axiom isUnboxedTupleType : Type_ -> bool.

Axiom isUnboxedSumType : Type_ -> bool.

Axiom isAlgType : Type_ -> bool.

Axiom isDataFamilyAppType : Type_ -> bool.

Axiom isStrictType : forall `{Util.HasDebugCallStack}, Type_ -> bool.

Axiom isPrimitiveType : Type_ -> bool.

Axiom isValidJoinPointType : BasicTypes.JoinArity -> Type_ -> bool.

Axiom seqType : Type_ -> unit.

Axiom seqTypes : list Type_ -> unit.

Axiom eqType : Type_ -> Type_ -> bool.

Axiom eqTypeX : RnEnv2 -> Type_ -> Type_ -> bool.

Axiom eqTypes : list Type_ -> list Type_ -> bool.

Axiom eqVarBndrs : RnEnv2 -> list Var -> list Var -> option RnEnv2.

Axiom nonDetCmpType : Type_ -> Type_ -> comparison.

Axiom nonDetCmpTypes : list Type_ -> list Type_ -> comparison.

Axiom nonDetCmpTypeX : RnEnv2 -> Type_ -> Type_ -> comparison.

Axiom nonDetCmpTypesX : RnEnv2 -> list Type_ -> list Type_ -> comparison.

Axiom nonDetCmpTc : TyCon -> TyCon -> comparison.

Axiom typeKind : forall `{Util.HasDebugCallStack}, Type_ -> Kind.

Axiom typeLiteralKind : TyLit -> Kind.

Axiom isTypeLevPoly : Type_ -> bool.

Axiom resultIsLevPoly : Type_ -> bool.

Axiom tyConsOfType : Type_ -> UniqSet.UniqSet TyCon.

Axiom synTyConResKind : TyCon -> Kind.

Axiom splitVisVarsOfType : Type_ -> Pair.Pair TyCoVarSet.

Axiom splitVisVarsOfTypes : list Type_ -> Pair.Pair TyCoVarSet.

Axiom modifyJoinResTy : nat -> (Type_ -> Type_) -> Type_ -> Type_.

Axiom setJoinResTy : nat -> Type_ -> Type_ -> Type_.

(* Skipping definition `Core.coVarDetails' *)

Definition isCoVarDetails : IdDetails -> bool :=
  fun arg_0__ => false.

Definition isJoinIdDetails_maybe : IdDetails -> option BasicTypes.JoinArity :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_JoinId join_arity => Some join_arity
    | _ => None
    end.

(* Skipping definition `Core.pprIdDetails' *)

Definition setRuleInfo : IdInfo -> RuleInfo -> IdInfo :=
  fun info sp =>
    GHC.Prim.seq sp (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ sp unfoldingInfo_2__ cafInfo_3__ oneShotInfo_4__
                            inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
                            callArityInfo_9__ levityInfo_10__).

Definition setInlinePragInfo : IdInfo -> BasicTypes.InlinePragma -> IdInfo :=
  fun info pr =>
    GHC.Prim.seq pr (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                            oneShotInfo_4__ pr occInfo_6__ strictnessInfo_7__ demandInfo_8__
                            callArityInfo_9__ levityInfo_10__).

Definition setOccInfo : IdInfo -> BasicTypes.OccInfo -> IdInfo :=
  fun info oc =>
    GHC.Prim.seq oc (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                            oneShotInfo_4__ inlinePragInfo_5__ oc strictnessInfo_7__ demandInfo_8__
                            callArityInfo_9__ levityInfo_10__).

Definition setUnfoldingInfo : IdInfo -> Unfolding -> IdInfo :=
  fun info uf =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ uf cafInfo_3__ oneShotInfo_4__
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

Definition setArityInfo : IdInfo -> ArityInfo -> IdInfo :=
  fun info ar =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo ar ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__ oneShotInfo_4__
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

Definition setCallArityInfo : IdInfo -> ArityInfo -> IdInfo :=
  fun info ar =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
              oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              ar levityInfo_10__.

Definition setCafInfo : IdInfo -> CafInfo -> IdInfo :=
  fun info caf =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ caf oneShotInfo_4__
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

Definition setOneShotInfo : IdInfo -> BasicTypes.OneShotInfo -> IdInfo :=
  fun info lb =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__ lb
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

Definition setDemandInfo : IdInfo -> Demand -> IdInfo :=
  fun info dd =>
    GHC.Prim.seq dd (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                            oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ dd
                            callArityInfo_9__ levityInfo_10__).

Definition setStrictnessInfo : IdInfo -> StrictSig -> IdInfo :=
  fun info dd =>
    GHC.Prim.seq dd (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                            oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ dd demandInfo_8__
                            callArityInfo_9__ levityInfo_10__).

Definition emptyRuleInfo :=
  EmptyRuleInfo.

Definition noUnfolding : Unfolding :=
  NoUnfolding.

Definition unknownArity : BasicTypes.Arity :=
  #0.

Definition vanillaCafInfo : CafInfo :=
  MayHaveCafRefs.

Definition vanillaIdInfo : IdInfo :=
  Mk_IdInfo unknownArity emptyRuleInfo noUnfolding vanillaCafInfo
            BasicTypes.NoOneShotInfo BasicTypes.defaultInlinePragma BasicTypes.noOccInfo
            nopSig topDmd unknownArity NoLevityInfo.

Definition noCafIdInfo : IdInfo :=
  setCafInfo vanillaIdInfo NoCafRefs.

(* Skipping definition `Core.ppArityInfo' *)

(* Skipping definition `Core.pprStrictness' *)

Definition isEmptyRuleInfo : RuleInfo -> bool :=
  fun x => true.

Definition emptyDVarSet : DVarSet :=
  UniqSet.emptyUniqSet.

Definition ruleInfoFreeVars : RuleInfo -> DVarSet :=
  fun x => emptyDVarSet.

Definition ruleInfoRules : RuleInfo -> list CoreRule :=
  fun x => nil.

Definition setRuleInfoHead : Name.Name -> RuleInfo -> RuleInfo :=
  fun x y => EmptyRuleInfo.

Definition mayHaveCafRefs : CafInfo -> bool :=
  fun arg_0__ => match arg_0__ with | MayHaveCafRefs => true | _ => false end.

(* Skipping definition `Core.ppCafInfo' *)

Definition zapLamInfo : IdInfo -> option IdInfo :=
  fun '((Mk_IdInfo _ _ _ _ _ _ occ _ demand _ _ as info)) =>
    let is_safe_dmd := fun dmd => negb (isStrictDmd dmd) in
    let safe_occ :=
      match occ with
      | BasicTypes.OneOcc _ _ _ _ =>
          match occ with
          | BasicTypes.ManyOccs _ =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          | BasicTypes.IAmDead =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          | BasicTypes.OneOcc occ_in_lam_2__ occ_one_br_3__ occ_int_cxt_4__
          occ_tail_5__ =>
              BasicTypes.OneOcc true occ_one_br_3__ occ_int_cxt_4__ BasicTypes.NoTailCallInfo
          | BasicTypes.IAmALoopBreaker _ _ =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          end
      | BasicTypes.IAmALoopBreaker _ _ =>
          match occ with
          | BasicTypes.ManyOccs occ_tail_12__ =>
              BasicTypes.ManyOccs BasicTypes.NoTailCallInfo
          | BasicTypes.IAmDead =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          | BasicTypes.OneOcc occ_in_lam_13__ occ_one_br_14__ occ_int_cxt_15__
          occ_tail_16__ =>
              BasicTypes.OneOcc occ_in_lam_13__ occ_one_br_14__ occ_int_cxt_15__
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
        | BasicTypes.OneOcc in_lam _ _ _ => in_lam
        | _other => true
        end in
    if andb (is_safe_occ occ) (is_safe_dmd demand) : bool then None else
    Some (let 'Mk_IdInfo arityInfo_31__ ruleInfo_32__ unfoldingInfo_33__
             cafInfo_34__ oneShotInfo_35__ inlinePragInfo_36__ occInfo_37__
             strictnessInfo_38__ demandInfo_39__ callArityInfo_40__ levityInfo_41__ :=
            info in
          Mk_IdInfo arityInfo_31__ ruleInfo_32__ unfoldingInfo_33__ cafInfo_34__
                    oneShotInfo_35__ inlinePragInfo_36__ safe_occ strictnessInfo_38__ topDmd
                    callArityInfo_40__ levityInfo_41__).

Definition zapDemandInfo : IdInfo -> option IdInfo :=
  fun info =>
    Some (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
             oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
             callArityInfo_9__ levityInfo_10__ := info in
          Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                    oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ topDmd
                    callArityInfo_9__ levityInfo_10__).

Definition zapUsageInfo : IdInfo -> option IdInfo :=
  fun info =>
    Some (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
             oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
             callArityInfo_9__ levityInfo_10__ := info in
          Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                    oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                    (zapUsageDemand (demandInfo info)) callArityInfo_9__ levityInfo_10__).

Definition zapUsageEnvInfo : IdInfo -> option IdInfo :=
  fun info =>
    if hasDemandEnvSig (strictnessInfo info) : bool
    then Some (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                  cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                  demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
               Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                         oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ (zapUsageEnvSig (strictnessInfo
                                                                                         info)) demandInfo_8__
                         callArityInfo_9__ levityInfo_10__) else
    None.

Definition zapUsedOnceInfo : IdInfo -> option IdInfo :=
  fun info =>
    Some (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
             oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
             callArityInfo_9__ levityInfo_10__ := info in
          Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                    oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ (zapUsedOnceSig (strictnessInfo
                                                                                    info)) (zapUsedOnceDemand
                     (demandInfo info)) callArityInfo_9__ levityInfo_10__).

Definition isFragileUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

Definition zapFragileUnfolding : Unfolding -> Unfolding :=
  fun unf => if isFragileUnfolding unf : bool then noUnfolding else unf.

Definition zapFragileInfo : IdInfo -> option IdInfo :=
  fun '((Mk_IdInfo _ _ unf _ _ _ occ _ _ _ _ as info)) =>
    let new_unf := zapFragileUnfolding unf in
    GHC.Prim.seq new_unf (Some (setOccInfo (setUnfoldingInfo (setRuleInfo info
                                                                          emptyRuleInfo) new_unf)
                                           (BasicTypes.zapFragileOcc occ))).

Definition zapTailCallInfo : IdInfo -> option IdInfo :=
  fun info =>
    let 'occ := occInfo info in
    let safe_occ :=
      match occ with
      | BasicTypes.ManyOccs occ_tail_1__ =>
          BasicTypes.ManyOccs BasicTypes.NoTailCallInfo
      | BasicTypes.IAmDead =>
          GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
      | BasicTypes.OneOcc occ_in_lam_2__ occ_one_br_3__ occ_int_cxt_4__
      occ_tail_5__ =>
          BasicTypes.OneOcc occ_in_lam_2__ occ_one_br_3__ occ_int_cxt_4__
                            BasicTypes.NoTailCallInfo
      | BasicTypes.IAmALoopBreaker occ_rules_only_6__ occ_tail_7__ =>
          BasicTypes.IAmALoopBreaker occ_rules_only_6__ BasicTypes.NoTailCallInfo
      end in
    if BasicTypes.isAlwaysTailCalled occ : bool
    then Some (setOccInfo info safe_occ) else
    None.

Definition zapCallArityInfo : IdInfo -> IdInfo :=
  fun info => setCallArityInfo info #0.

Definition setNeverLevPoly `{Util.HasDebugCallStack}
   : IdInfo -> Type_ -> IdInfo :=
  fun info ty =>
    if andb Util.debugIsOn (negb (negb (resultIsLevPoly ty))) : bool
    then (GHC.Err.error Panic.someSDoc)
    else let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
            oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
            callArityInfo_9__ levityInfo_10__ := info in
         Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                   oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
                   callArityInfo_9__ NeverLevityPolymorphic.

(* Skipping definition `Core.setLevityInfoWithType' *)

Definition isNeverLevPolyIdInfo : IdInfo -> bool :=
  fun info =>
    match levityInfo info with
    | NeverLevityPolymorphic => true
    | _ => false
    end.

(* Skipping definition `Core.ppr_debug' *)

(* Skipping definition `Core.ppr_id_scope' *)

Definition setVarUnique : Var -> Unique.Unique -> Var :=
  fun var uniq =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
       id_info_5__ := var in
    Mk_Id (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq) varType_2__
          idScope_3__ id_details_4__ id_info_5__.

Definition setVarName : Var -> Name.Name -> Var :=
  fun var new_name =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
       id_info_5__ := var in
    Mk_Id new_name (Unique.getKey (Unique.getUnique new_name)) varType_2__
          idScope_3__ id_details_4__ id_info_5__.

Definition setVarType : Id -> Type_ -> Id :=
  fun id ty =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
       id_info_5__ := id in
    Mk_Id varName_0__ realUnique_1__ ty idScope_3__ id_details_4__ id_info_5__.

Definition updateVarType : (Type_ -> Type_) -> Id -> Id :=
  fun f id =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
       id_info_5__ := id in
    Mk_Id varName_0__ realUnique_1__ (f (varType id)) idScope_3__ id_details_4__
          id_info_5__.

Definition updateVarTypeM {m : Type -> Type} `{GHC.Base.Monad m}
   : (Type_ -> m Type_) -> Id -> m Id :=
  fun f id =>
    f (varType id) GHC.Base.>>=
    (fun ty' =>
       GHC.Base.return_ (let 'Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__
                            id_details_4__ id_info_5__ := id in
                         Mk_Id varName_0__ realUnique_1__ ty' idScope_3__ id_details_4__ id_info_5__)).

Definition isVisibleArgFlag : ArgFlag -> bool :=
  fun arg_0__ => match arg_0__ with | Required => true | _ => false end.

Definition isInvisibleArgFlag : ArgFlag -> bool :=
  negb GHC.Base.∘ isVisibleArgFlag.

Definition sameVis : ArgFlag -> ArgFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Required, Required => true
    | Required, _ => false
    | _, Required => false
    | _, _ => true
    end.

Definition binderVar {tv : Type} {argf : Type} : TyVarBndr tv argf -> tv :=
  fun '(TvBndr v _) => v.

Definition binderVars {tv : Type} {argf : Type}
   : list (TyVarBndr tv argf) -> list tv :=
  fun tvbs => GHC.Base.map binderVar tvbs.

Definition binderArgFlag {tv : Type} {argf : Type}
   : TyVarBndr tv argf -> argf :=
  fun '(TvBndr _ argf) => argf.

Definition tyVarKind : TyVar -> Kind :=
  varType.

Definition binderKind {argf : Type} : TyVarBndr TyVar argf -> Kind :=
  fun '(TvBndr tv _) => tyVarKind tv.

Definition mkTyVarBinder : ArgFlag -> Var -> TyVarBinder :=
  fun vis var => TvBndr var vis.

Definition mkTyVarBinders : ArgFlag -> list TyVar -> list TyVarBinder :=
  fun vis => GHC.Base.map (mkTyVarBinder vis).

Definition tyVarName : TyVar -> Name.Name :=
  varName.

Definition setTyVarUnique : TyVar -> Unique.Unique -> TyVar :=
  setVarUnique.

Definition setTyVarName : TyVar -> Name.Name -> TyVar :=
  setVarName.

Definition setTyVarKind : TyVar -> Kind -> TyVar :=
  fun tv k =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
       id_info_5__ := tv in
    Mk_Id varName_0__ realUnique_1__ k idScope_3__ id_details_4__ id_info_5__.

Definition updateTyVarKind : (Kind -> Kind) -> TyVar -> TyVar :=
  fun update tv =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
       id_info_5__ := tv in
    Mk_Id varName_0__ realUnique_1__ (update (tyVarKind tv)) idScope_3__
          id_details_4__ id_info_5__.

Definition updateTyVarKindM {m : Type -> Type} `{GHC.Base.Monad m}
   : (Kind -> m Kind) -> TyVar -> m TyVar :=
  fun update tv =>
    update (tyVarKind tv) GHC.Base.>>=
    (fun k' =>
       GHC.Base.return_ (let 'Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__
                            id_details_4__ id_info_5__ := tv in
                         Mk_Id varName_0__ realUnique_1__ k' idScope_3__ id_details_4__ id_info_5__)).

(* Skipping definition `Core.mkTyVar' *)

(* Skipping definition `Core.mkTcTyVar' *)

(* Skipping definition `Core.tcTyVarDetails' *)

(* Skipping definition `Core.setTcTyVarDetails' *)

Definition idInfo `{Util.HasDebugCallStack} : Id -> IdInfo :=
  fun '(Mk_Id _ _ _ _ _ info) => info.

Definition idDetails : Id -> IdDetails :=
  fun '(Mk_Id _ _ _ _ details _) => details.

Definition mk_id : Name.Name -> Type_ -> IdScope -> IdDetails -> IdInfo -> Id :=
  fun name ty scope details info =>
    Mk_Id name (Unique.getKey (Name.nameUnique name)) ty scope details info.

Definition mkGlobalVar : IdDetails -> Name.Name -> Type_ -> IdInfo -> Id :=
  fun details name ty info => mk_id name ty GlobalId details info.

Definition mkLocalVar : IdDetails -> Name.Name -> Type_ -> IdInfo -> Id :=
  fun details name ty info => mk_id name ty (LocalId NotExported) details info.

(* Skipping definition `Core.mkCoVar' *)

Definition mkExportedLocalVar
   : IdDetails -> Name.Name -> Type_ -> IdInfo -> Id :=
  fun details name ty info => mk_id name ty (LocalId Exported) details info.

Definition lazySetIdInfo : Id -> IdInfo -> Var :=
  fun id info =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
       id_info_5__ := id in
    Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__ info.

Definition setIdDetails : Id -> IdDetails -> Id :=
  fun id details =>
    let 'Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
       id_info_5__ := id in
    Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ details id_info_5__.

(* Skipping definition `Core.globaliseId' *)

(* Skipping definition `Core.setIdExported' *)

(* Skipping definition `Core.setIdNotExported' *)

Definition isTyVar : Var -> bool :=
  fun arg_0__ => false.

Definition isTcTyVar : Var -> bool :=
  fun arg_0__ => false.

Definition isCoVar : Var -> bool :=
  fun '(Mk_Id _ _ _ _ details _) => isCoVarDetails details.

Definition isTyCoVar : Var -> bool :=
  fun v => orb (isTyVar v) (isCoVar v).

Definition isId : Var -> bool :=
  fun '(Mk_Id _ _ _ _ _ _) => true.

Definition isNonCoVarId : Var -> bool :=
  fun '(Mk_Id _ _ _ _ details _) => negb (isCoVarDetails details).

Definition isLocalId : Var -> bool :=
  fun v => Unique.isLocalUnique (varUnique v).

Definition isGlobalId : Var -> bool :=
  fun v => negb (Unique.isLocalUnique (varUnique v)).

Definition isLocalVar : Var -> bool :=
  fun v => negb (isGlobalId v).

Definition mustHaveLocalBinding : Var -> bool :=
  fun var => isLocalVar var.

Axiom isExportedId : Var -> bool.

Definition emptyVarSet : VarSet :=
  UniqSet.emptyUniqSet.

Definition emptyInScopeSet : InScopeSet :=
  InScope emptyVarSet #1.

Definition getInScopeVars : InScopeSet -> VarSet :=
  fun '(InScope vs _) => vs.

Definition mkInScopeSet : VarSet -> InScopeSet :=
  fun in_scope => InScope in_scope #1.

Definition extendDVarEnv {a : Type} : DVarEnv a -> Var -> a -> DVarEnv a :=
  UniqFM.addToUFM.

Definition extendVarEnv {a : Type} : VarEnv a -> Var -> a -> VarEnv a :=
  UniqFM.addToUFM.

Definition extendDVarEnvList {a : Type}
   : DVarEnv a -> list (Var * a)%type -> DVarEnv a :=
  UniqFM.addListToUFM.

Definition extendVarEnvList {a : Type}
   : VarEnv a -> list (Var * a)%type -> VarEnv a :=
  UniqFM.addListToUFM.

Definition extendDVarEnv_C {a : Type}
   : (a -> a -> a) -> DVarEnv a -> Var -> a -> DVarEnv a :=
  UniqFM.addToUFM_C.

Definition extendVarEnv_Acc {a : Type} {b : Type}
   : (a -> b -> b) -> (a -> b) -> VarEnv b -> Var -> a -> VarEnv b :=
  UniqFM.addToUFM_Acc.

Definition extendVarEnv_C {a : Type}
   : (a -> a -> a) -> VarEnv a -> Var -> a -> VarEnv a :=
  UniqFM.addToUFM_C.

Definition extendVarEnv_Directly {a : Type}
   : VarEnv a -> Unique.Unique -> a -> VarEnv a :=
  UniqFM.addToUFM_Directly.

Definition extendVarSet : VarSet -> Var -> VarSet :=
  UniqSet.addOneToUniqSet.

Definition extendInScopeSet : InScopeSet -> Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, v => InScope (extendVarSet in_scope v) (n GHC.Num.+ #1)
    end.

Definition extendInScopeSetList : InScopeSet -> list Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, vs =>
        InScope (Data.Foldable.foldl (fun s v => extendVarSet s v) in_scope vs) (n
                                                                                 GHC.Num.+
                                                                                 Coq.Lists.List.length vs)
    end.

Definition unionVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.unionUniqSets.

Definition extendInScopeSetSet : InScopeSet -> VarSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, vs =>
        InScope (unionVarSet in_scope vs) (n GHC.Num.+ UniqSet.sizeUniqSet vs)
    end.

Definition alterDVarEnv {a : Type}
   : (option a -> option a) -> DVarEnv a -> Var -> DVarEnv a :=
  UniqFM.alterUFM.

Definition alterVarEnv {a : Type}
   : (option a -> option a) -> VarEnv a -> Var -> VarEnv a :=
  UniqFM.alterUFM.

Definition delDVarEnv {a : Type} : DVarEnv a -> Var -> DVarEnv a :=
  UniqFM.delFromUFM.

Definition delVarEnv {a : Type} : VarEnv a -> Var -> VarEnv a :=
  UniqFM.delFromUFM.

Definition delDVarEnvList {a : Type} : DVarEnv a -> list Var -> DVarEnv a :=
  UniqFM.delListFromUFM.

Definition delVarEnvList {a : Type} : VarEnv a -> list Var -> VarEnv a :=
  UniqFM.delListFromUFM.

Definition delDVarSet : DVarSet -> Var -> DVarSet :=
  UniqSet.delOneFromUniqSet.

Definition delVarSet : VarSet -> Var -> VarSet :=
  UniqSet.delOneFromUniqSet.

Definition delInScopeSet : InScopeSet -> Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, v => InScope (delVarSet in_scope v) n
    end.

Definition delDVarSetList : DVarSet -> list Var -> DVarSet :=
  UniqSet.delListFromUniqSet.

Definition delVarSetList : VarSet -> list Var -> VarSet :=
  UniqSet.delListFromUniqSet.

Definition delVarEnv_Directly {a : Type}
   : VarEnv a -> Unique.Unique -> VarEnv a :=
  UniqFM.delFromUFM_Directly.

Definition delVarSetByKey : VarSet -> Unique.Unique -> VarSet :=
  UniqSet.delOneFromUniqSet_Directly.

Definition elemDVarEnv {a : Type} : Var -> DVarEnv a -> bool :=
  UniqFM.elemUFM.

Definition elemVarEnv {a : Type} : Var -> VarEnv a -> bool :=
  UniqFM.elemUFM.

Definition elemDVarSet : Var -> DVarSet -> bool :=
  UniqSet.elementOfUniqSet.

Definition elemVarSet : Var -> VarSet -> bool :=
  UniqSet.elementOfUniqSet.

Definition elemInScopeSet : Var -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, InScope in_scope _ => elemVarSet v in_scope
    end.

Definition lookupDVarEnv {a : Type} : DVarEnv a -> Var -> option a :=
  UniqFM.lookupUFM.

Definition lookupVarEnv {a : Type} : VarEnv a -> Var -> option a :=
  UniqFM.lookupUFM.

Definition lookupVarEnv_Directly {a : Type}
   : VarEnv a -> Unique.Unique -> option a :=
  UniqFM.lookupUFM_Directly.

Definition lookupVarEnv_NF {a} `{_ : HsToCoq.Err.Default a} (env : VarEnv a) id
   : a :=
  match lookupVarEnv env id with
  | Some xx => xx
  | None => HsToCoq.Err.default
  end.

Definition lookupVarSet : VarSet -> Var -> option Var :=
  UniqSet.lookupUniqSet.

Definition lookupInScope : InScopeSet -> Var -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope _, v => lookupVarSet in_scope v
    end.

Definition lookupVarSetByName : VarSet -> Name.Name -> option Var :=
  UniqSet.lookupUniqSet.

Definition lookupVarSet_Directly : VarSet -> Unique.Unique -> option Var :=
  UniqSet.lookupUniqSet_Directly.

Definition lookupInScope_Directly : InScopeSet -> Unique.Unique -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope _, uniq => lookupVarSet_Directly in_scope uniq
    end.

Definition unionInScope : InScopeSet -> InScopeSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope s1 _, InScope s2 n2 => InScope (unionVarSet s1 s2) n2
    end.

Definition isEmptyVarSet : VarSet -> bool :=
  UniqSet.isEmptyUniqSet.

Definition minusVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.minusUniqSet.

Definition subVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => isEmptyVarSet (minusVarSet s1 s2).

Definition varSetInScope : VarSet -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | vars, InScope s1 _ => subVarSet vars s1
    end.

Axiom uniqAway : InScopeSet -> Var -> Var.

Definition elemVarSetByKey : Unique.Unique -> VarSet -> bool :=
  UniqSet.elemUniqSet_Directly.

Definition mkDVarEnv {a : Type} : list (Var * a)%type -> DVarEnv a :=
  UniqFM.listToUFM.

Definition mkVarEnv {a : Type} : list (Var * a)%type -> VarEnv a :=
  UniqFM.listToUFM.

Definition mkDVarSet : list Var -> DVarSet :=
  UniqSet.mkUniqSet.

Definition mkVarSet : list Var -> VarSet :=
  UniqSet.mkUniqSet.

Definition uniqAway' : InScopeSet -> Var -> Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope set n, var =>
        let orig_unique := Unique.getUnique var in
        let try :=
          HsToCoq.DeferredFix.deferredFix1 (fun try k =>
                                              let uniq :=
                                                Unique.deriveUnique orig_unique (BinNat.N.of_nat n GHC.Num.* k) in
                                              let msg :=
                                                GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend Panic.someSDoc
                                                                                                     (Datatypes.id
                                                                                                      (GHC.Base.hs_string__
                                                                                                       "tries")))
                                                                                   Panic.someSDoc) Panic.someSDoc in
                                              if andb Util.debugIsOn (k GHC.Base.> #1000) : bool
                                              then Panic.panicStr (GHC.Base.hs_string__ "uniqAway loop:") msg else
                                              if elemVarSetByKey uniq set : bool then try (k GHC.Num.+ #1) else
                                              if k GHC.Base.> #3 : bool then setVarUnique var uniq else
                                              setVarUnique var uniq) in
        try #1
    end.

Definition emptyVarEnv {a : Type} : VarEnv a :=
  UniqFM.emptyUFM.

Definition mkRnEnv2 : InScopeSet -> RnEnv2 :=
  fun vars => RV2 emptyVarEnv emptyVarEnv vars.

Definition addRnInScopeSet : RnEnv2 -> VarSet -> RnEnv2 :=
  fun env vs =>
    if isEmptyVarSet vs : bool then env else
    let 'RV2 envL_0__ envR_1__ in_scope_2__ := env in
    RV2 envL_0__ envR_1__ (extendInScopeSetSet (in_scope env) vs).

Definition rnInScope : Var -> RnEnv2 -> bool :=
  fun x env => elemInScopeSet x (in_scope env).

Definition rnInScopeSet : RnEnv2 -> InScopeSet :=
  in_scope.

Definition rnEnvL : RnEnv2 -> VarEnv Var :=
  envL.

Definition rnEnvR : RnEnv2 -> VarEnv Var :=
  envR.

Definition rnBndr2_var : RnEnv2 -> Var -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | RV2 envL envR in_scope, bL, bR =>
        let new_b :=
          if negb (elemInScopeSet bL in_scope) : bool then bL else
          if negb (elemInScopeSet bR in_scope) : bool then bR else
          uniqAway' in_scope bL in
        pair (RV2 (extendVarEnv envL bL new_b) (extendVarEnv envR bR new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

Definition rnBndr2 : RnEnv2 -> Var -> Var -> RnEnv2 :=
  fun env bL bR => Data.Tuple.fst (rnBndr2_var env bL bR).

Definition rnBndrs2 : RnEnv2 -> list Var -> list Var -> RnEnv2 :=
  fun env bsL bsR => Util.foldl2 rnBndr2 env bsL bsR.

Definition rnBndrL : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bL =>
        let new_b := uniqAway in_scope bL in
        pair (RV2 (extendVarEnv envL bL new_b) envR (extendInScopeSet in_scope new_b))
             new_b
    end.

Definition rnBndrR : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bR =>
        let new_b := uniqAway in_scope bR in
        pair (RV2 envL (extendVarEnv envR bR new_b) (extendInScopeSet in_scope new_b))
             new_b
    end.

Definition rnEtaL : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bL =>
        let new_b := uniqAway in_scope bL in
        pair (RV2 (extendVarEnv envL bL new_b) (extendVarEnv envR new_b new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

Definition rnEtaR : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bR =>
        let new_b := uniqAway in_scope bR in
        pair (RV2 (extendVarEnv envL new_b new_b) (extendVarEnv envR bR new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

Definition delBndrL : RnEnv2 -> Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 env _ in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 (delVarEnv env v) envR_3__ (extendInScopeSet in_scope v)
    end.

Definition delBndrR : RnEnv2 -> Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 _ env in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 envL_2__ (delVarEnv env v) (extendInScopeSet in_scope v)
    end.

Definition delBndrsL : RnEnv2 -> list Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 env _ in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 (delVarEnvList env v) envR_3__ (extendInScopeSetList in_scope v)
    end.

Definition delBndrsR : RnEnv2 -> list Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 _ env in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 envL_2__ (delVarEnvList env v) (extendInScopeSetList in_scope v)
    end.

Definition rnOccL : RnEnv2 -> Var -> Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => Maybes.orElse (lookupVarEnv env v) v
    end.

Definition rnOccR : RnEnv2 -> Var -> Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => Maybes.orElse (lookupVarEnv env v) v
    end.

Definition rnOccL_maybe : RnEnv2 -> Var -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => lookupVarEnv env v
    end.

Definition rnOccR_maybe : RnEnv2 -> Var -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => lookupVarEnv env v
    end.

Definition inRnEnvL : RnEnv2 -> Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => elemVarEnv v env
    end.

Definition inRnEnvR : RnEnv2 -> Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => elemVarEnv v env
    end.

Definition lookupRnInScope : RnEnv2 -> Var -> Var :=
  fun env v => Maybes.orElse (lookupInScope (in_scope env) v) v.

Definition nukeRnEnvL : RnEnv2 -> RnEnv2 :=
  fun '(RV2 envL_0__ envR_1__ in_scope_2__) =>
    RV2 emptyVarEnv envR_1__ in_scope_2__.

Definition nukeRnEnvR : RnEnv2 -> RnEnv2 :=
  fun '(RV2 envL_0__ envR_1__ in_scope_2__) =>
    RV2 envL_0__ emptyVarEnv in_scope_2__.

Definition rnSwap : RnEnv2 -> RnEnv2 :=
  fun '(RV2 envL envR in_scope) => RV2 envR envL in_scope.

Definition emptyTidyEnv : TidyEnv :=
  pair OccName.emptyTidyOccEnv emptyVarEnv.

Definition elemVarEnvByKey {a : Type} : Unique.Unique -> VarEnv a -> bool :=
  UniqFM.elemUFM_Directly.

Definition disjointVarEnv {a : Type} : VarEnv a -> VarEnv a -> bool :=
  UniqFM.disjointUFM.

Definition plusVarEnv_C {a : Type}
   : (a -> a -> a) -> VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM_C.

Definition plusVarEnv_CD {a : Type}
   : (a -> a -> a) -> VarEnv a -> a -> VarEnv a -> a -> VarEnv a :=
  UniqFM.plusUFM_CD.

Definition plusMaybeVarEnv_C {a : Type}
   : (a -> a -> option a) -> VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusMaybeUFM_C.

Definition minusVarEnv {a : Type} {b : Type}
   : VarEnv a -> VarEnv b -> VarEnv a :=
  UniqFM.minusUFM.

Definition isEmptyVarEnv {a : Type} : VarEnv a -> bool :=
  UniqFM.isNullUFM.

Definition intersectsVarEnv {a : Type} : VarEnv a -> VarEnv a -> bool :=
  fun e1 e2 => negb (isEmptyVarEnv (UniqFM.intersectUFM e1 e2)).

Definition plusVarEnv {a : Type} : VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM.

Definition plusVarEnvList {a : Type} : list (VarEnv a) -> VarEnv a :=
  UniqFM.plusUFMList.

Definition filterVarEnv {a : Type} : (a -> bool) -> VarEnv a -> VarEnv a :=
  UniqFM.filterUFM.

Definition lookupWithDefaultVarEnv {a : Type} : VarEnv a -> a -> Var -> a :=
  UniqFM.lookupWithDefaultUFM.

Definition mapVarEnv {a : Type} {b : Type} : (a -> b) -> VarEnv a -> VarEnv b :=
  UniqFM.mapUFM.

Definition mkVarEnv_Directly {a : Type}
   : list (Unique.Unique * a)%type -> VarEnv a :=
  UniqFM.listToUFM_Directly.

Definition unitDVarEnv {a : Type} : Var -> a -> DVarEnv a :=
  UniqFM.unitUFM.

Definition unitVarEnv {a : Type} : Var -> a -> VarEnv a :=
  UniqFM.unitUFM.

Definition filterVarEnv_Directly {a : Type}
   : (Unique.Unique -> a -> bool) -> VarEnv a -> VarEnv a :=
  UniqFM.filterUFM_Directly.

Definition partitionVarEnv {a : Type}
   : (a -> bool) -> VarEnv a -> (VarEnv a * VarEnv a)%type :=
  UniqFM.partitionUFM.

Definition restrictVarEnv {a : Type} : VarEnv a -> VarSet -> VarEnv a :=
  fun env vs =>
    let keep :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | u, _ => elemVarSetByKey u vs
        end in
    filterVarEnv_Directly keep env.

Definition zipVarEnv {a : Type} : list Var -> list a -> VarEnv a :=
  fun tyvars tys =>
    mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipVarEnv") tyvars tys).

Definition modifyVarEnv {a : Type} : (a -> a) -> VarEnv a -> Var -> VarEnv a :=
  fun mangle_fn env key =>
    match (lookupVarEnv env key) with
    | None => env
    | Some xx => extendVarEnv env key (mangle_fn xx)
    end.

Definition modifyVarEnv_Directly {a : Type}
   : (a -> a) -> UniqFM.UniqFM a -> Unique.Unique -> UniqFM.UniqFM a :=
  fun mangle_fn env key =>
    match (UniqFM.lookupUFM_Directly env key) with
    | None => env
    | Some xx => UniqFM.addToUFM_Directly env key (mangle_fn xx)
    end.

Definition emptyDVarEnv {a : Type} : DVarEnv a :=
  UniqFM.emptyUFM.

Definition dVarEnvElts {a : Type} : DVarEnv a -> list a :=
  UniqFM.eltsUFM.

Definition minusDVarEnv {a : Type} {a' : Type}
   : DVarEnv a -> DVarEnv a' -> DVarEnv a :=
  UniqFM.minusUFM.

Definition foldDVarEnv {a : Type} {b : Type}
   : (a -> b -> b) -> b -> DVarEnv a -> b :=
  UniqFM.nonDetFoldUFM.

Definition mapDVarEnv {a : Type} {b : Type}
   : (a -> b) -> DVarEnv a -> DVarEnv b :=
  UniqFM.mapUFM.

Definition filterDVarEnv {a : Type} : (a -> bool) -> DVarEnv a -> DVarEnv a :=
  UniqFM.filterUFM.

Definition plusDVarEnv {a : Type} : DVarEnv a -> DVarEnv a -> DVarEnv a :=
  UniqFM.plusUFM.

Definition plusDVarEnv_C {a : Type}
   : (a -> a -> a) -> DVarEnv a -> DVarEnv a -> DVarEnv a :=
  UniqFM.plusUFM_C.

Definition isEmptyDVarEnv {a : Type} : DVarEnv a -> bool :=
  UniqFM.isNullUFM.

Definition modifyDVarEnv {a : Type}
   : (a -> a) -> DVarEnv a -> Var -> DVarEnv a :=
  fun mangle_fn env key =>
    match (lookupDVarEnv env key) with
    | None => env
    | Some xx => extendDVarEnv env key (mangle_fn xx)
    end.

Definition partitionDVarEnv {a : Type}
   : (a -> bool) -> DVarEnv a -> (DVarEnv a * DVarEnv a)%type :=
  UniqFM.partitionUFM.

Definition anyDVarEnv {a : Type} : (a -> bool) -> DVarEnv a -> bool :=
  UniqFM.anyUFM.

Definition unitDVarSet : Var -> DVarSet :=
  UniqSet.unitUniqSet.

Definition unitVarSet : Var -> VarSet :=
  UniqSet.unitUniqSet.

Definition extendDVarSet : DVarSet -> Var -> DVarSet :=
  UniqSet.addOneToUniqSet.

Definition extendDVarSetList : DVarSet -> list Var -> DVarSet :=
  UniqSet.addListToUniqSet.

Definition extendVarSetList : VarSet -> list Var -> VarSet :=
  UniqSet.addListToUniqSet.

Definition intersectVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.intersectUniqSets.

Definition unionVarSets : list VarSet -> VarSet :=
  UniqSet.unionManyUniqSets.

Definition sizeVarSet : VarSet -> nat :=
  UniqSet.sizeUniqSet.

Definition filterVarSet : (Var -> bool) -> VarSet -> VarSet :=
  UniqSet.filterUniqSet.

(* Skipping definition `Core.partitionVarSet' *)

Definition mapUnionVarSet {a : Type} : (a -> VarSet) -> list a -> VarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionVarSet GHC.Base.∘ get_set) emptyVarSet xs.

Definition disjointVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => UniqFM.disjointUFM (UniqSet.getUniqSet s1) (UniqSet.getUniqSet s2).

Definition intersectsVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => negb (disjointVarSet s1 s2).

Definition anyVarSet : (Var -> bool) -> VarSet -> bool :=
  UniqSet.uniqSetAny.

Definition allVarSet : (Var -> bool) -> VarSet -> bool :=
  UniqSet.uniqSetAll.

(* Skipping definition `Core.mapVarSet' *)

Definition fixVarSet : (VarSet -> VarSet) -> VarSet -> VarSet :=
  HsToCoq.DeferredFix.deferredFix2 (fun fixVarSet
                                    (fn : VarSet -> VarSet)
                                    (vars : VarSet) =>
                                      let new_vars := fn vars in
                                      if subVarSet new_vars vars : bool then vars else
                                      fixVarSet fn new_vars).

Definition transCloVarSet : (VarSet -> VarSet) -> VarSet -> VarSet :=
  fun fn seeds =>
    let go : VarSet -> VarSet -> VarSet :=
      HsToCoq.DeferredFix.deferredFix1 (fun go (acc candidates : VarSet) =>
                                          let new_vs := minusVarSet (fn candidates) acc in
                                          if isEmptyVarSet new_vs : bool then acc else
                                          go (unionVarSet acc new_vs) new_vs) in
    go seeds seeds.

Definition seqVarSet : VarSet -> unit :=
  fun s => GHC.Prim.seq (sizeVarSet s) tt.

(* Skipping definition `Core.pluralVarSet' *)

(* Skipping definition `Core.pprVarSet' *)

Definition dVarSetElems : DVarSet -> list Var :=
  UniqSet.nonDetEltsUniqSet.

Definition isEmptyDVarSet : DVarSet -> bool :=
  UniqSet.isEmptyUniqSet.

Definition minusDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqSet.minusUniqSet.

Definition subDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => isEmptyDVarSet (minusDVarSet s1 s2).

Definition unionDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqSet.unionUniqSets.

Definition unionDVarSets : list DVarSet -> DVarSet :=
  UniqSet.unionManyUniqSets.

Definition mapUnionDVarSet {a : Type} : (a -> DVarSet) -> list a -> DVarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionDVarSet GHC.Base.∘ get_set) emptyDVarSet xs.

Definition intersectDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqSet.intersectUniqSets.

Definition dVarSetIntersectVarSet : DVarSet -> VarSet -> DVarSet :=
  UniqSet.intersectUniqSets.

Definition disjointDVarSet :=
  disjointVarSet.

Definition intersectsDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => negb (disjointDVarSet s1 s2).

Definition dVarSetMinusVarSet : DVarSet -> VarSet -> DVarSet :=
  UniqSet.minusUniqSet.

Definition foldDVarSet {a : Type} : (Var -> a -> a) -> a -> DVarSet -> a :=
  UniqSet.nonDetFoldUniqSet.

Definition anyDVarSet :=
  anyVarSet.

Definition allDVarSet :=
  allVarSet.

Definition filterDVarSet : (Var -> bool) -> DVarSet -> DVarSet :=
  UniqSet.filterUniqSet.

Definition sizeDVarSet : DVarSet -> nat :=
  UniqSet.sizeUniqSet.

Definition partitionDVarSet
   : (Var -> bool) -> DVarSet -> (DVarSet * DVarSet)%type :=
  UniqSet.partitionUniqSet.

Definition seqDVarSet : DVarSet -> unit :=
  fun s => GHC.Prim.seq (sizeDVarSet s) tt.

Definition dVarSetToVarSet : DVarSet -> VarSet :=
  fun x => x.

Definition transCloDVarSet : (DVarSet -> DVarSet) -> DVarSet -> DVarSet :=
  fun fn seeds =>
    let go : DVarSet -> DVarSet -> DVarSet :=
      HsToCoq.DeferredFix.deferredFix1 (fun go (acc candidates : DVarSet) =>
                                          let new_vs := minusDVarSet (fn candidates) acc in
                                          if isEmptyDVarSet new_vs : bool then acc else
                                          go (unionDVarSet acc new_vs) new_vs) in
    go seeds seeds.

Axiom tickishCounts : forall {id : Type}, Tickish id -> bool.

Definition tickishScoped {id : Type} : Tickish id -> TickishScoping :=
  fun arg_0__ =>
    match arg_0__ with
    | (ProfNote _ _ _ as n) =>
        if profNoteScope n : bool then CostCentreScope else
        NoScope
    | HpcTick _ _ => NoScope
    | Breakpoint _ _ => CostCentreScope
    | SourceNote _ _ => SoftScope
    end.

Definition tickishScopesLike {id : Type}
   : Tickish id -> TickishScoping -> bool :=
  fun t scope =>
    let like :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | NoScope, _ => true
        | _, NoScope => false
        | SoftScope, _ => true
        | _, SoftScope => false
        | CostCentreScope, _ => true
        end in
    like (tickishScoped t) scope.

Definition tickishFloatable {id : Type} : Tickish id -> bool :=
  fun t => andb (tickishScopesLike t SoftScope) (negb (tickishCounts t)).

(* Skipping definition `Core.tickishCanSplit' *)

(* Skipping definition `Core.mkNoCount' *)

(* Skipping definition `Core.mkNoScope' *)

Axiom tickishIsCode : forall {id : Type}, Tickish id -> bool.

Definition tickishPlace {id : Type} : Tickish id -> TickishPlacement :=
  fun arg_0__ =>
    match arg_0__ with
    | (ProfNote _ _ _ as n) =>
        if profNoteCount n : bool then PlaceRuntime else
        PlaceCostCentre
    | HpcTick _ _ => PlaceRuntime
    | Breakpoint _ _ => PlaceRuntime
    | SourceNote _ _ => PlaceNonLam
    end.

(* Skipping definition `Core.tickishContains' *)

Definition isOrphan : IsOrphan -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_IsOrphan => true | _ => false end.

Definition notOrphan : IsOrphan -> bool :=
  fun arg_0__ => match arg_0__ with | NotOrphan _ => true | _ => false end.

Definition chooseOrphanAnchor (local_names : list Name.Name) : IsOrphan :=
  match GHC.Base.map Name.nameOccName local_names with
  | cons hd tl => NotOrphan (Data.Foldable.foldr GHC.Base.min hd tl)
  | nil => Mk_IsOrphan
  end.

Definition mkRuleEnv : RuleBase -> list Module.Module -> RuleEnv :=
  fun rules vis_orphs => Mk_RuleEnv rules (Module.mkModuleSet vis_orphs).

Definition emptyRuleEnv : RuleEnv :=
  Mk_RuleEnv NameEnv.emptyNameEnv Module.emptyModuleSet.

Definition isBuiltinRule : CoreRule -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => true
    | _ => false
    end.

Definition isAutoRule : CoreRule -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => false
    | Rule _ _ _ _ _ _ _ is_auto _ _ _ => is_auto
    end.

Definition ruleArity : CoreRule -> nat :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ n _ => n
    | Rule _ _ _ _ _ args _ _ _ _ _ => Coq.Lists.List.length args
    end.

Definition ruleName : CoreRule -> BasicTypes.RuleName :=
  ru_name.

Definition ruleModule : CoreRule -> option Module.Module :=
  fun arg_0__ =>
    match arg_0__ with
    | Rule _ _ _ _ _ _ _ _ ru_origin _ _ => Some ru_origin
    | BuiltinRule _ _ _ _ => None
    end.

Definition ruleActivation : CoreRule -> BasicTypes.Activation :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => BasicTypes.AlwaysActive
    | Rule _ act _ _ _ _ _ _ _ _ _ => act
    end.

Definition ruleIdName : CoreRule -> Name.Name :=
  ru_fn.

Definition isLocalRule : CoreRule -> bool :=
  ru_local.

Definition setRuleIdName : Name.Name -> CoreRule -> CoreRule :=
  fun nm ru =>
    match ru with
    | Rule ru_name_0__ ru_act_1__ ru_fn_2__ ru_rough_3__ ru_bndrs_4__ ru_args_5__
    ru_rhs_6__ ru_auto_7__ ru_origin_8__ ru_orphan_9__ ru_local_10__ =>
        Rule ru_name_0__ ru_act_1__ nm ru_rough_3__ ru_bndrs_4__ ru_args_5__ ru_rhs_6__
             ru_auto_7__ ru_origin_8__ ru_orphan_9__ ru_local_10__
    | BuiltinRule ru_name_11__ ru_fn_12__ ru_nargs_13__ ru_try_14__ =>
        BuiltinRule ru_name_11__ nm ru_nargs_13__ ru_try_14__
    end.

Definition needSaturated : bool :=
  false.

Definition unSaturatedOk : bool :=
  true.

Definition boringCxtOk : bool :=
  true.

Definition boringCxtNotOk : bool :=
  false.

(* Skipping definition `Core.evaldUnfolding' *)

(* Skipping definition `Core.bootUnfolding' *)

(* Skipping definition `Core.mkOtherCon' *)

Definition isStableSource : UnfoldingSource -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | InlineCompulsory => true
    | InlineStable => true
    | InlineRhs => false
    end.

Axiom unfoldingTemplate : Unfolding -> CoreExpr.

Definition maybeUnfoldingTemplate : Unfolding -> option CoreExpr :=
  fun arg_0__ => None.

Definition otherCons : Unfolding -> list AltCon :=
  fun arg_0__ => nil.

Definition isValueUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

Definition isEvaldUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

Definition isConLikeUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

Definition isCheapUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

Definition isExpandableUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

Definition expandUnfolding_maybe : Unfolding -> option CoreExpr :=
  fun arg_0__ => None.

Definition isCompulsoryUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

Definition isStableUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

Definition hasSomeUnfolding : Unfolding -> bool :=
  fun '(NoUnfolding) => false.

Definition isBootUnfolding : Unfolding -> bool :=
  fun arg_0__ => false.

Definition neverUnfoldGuidance : UnfoldingGuidance -> bool :=
  fun arg_0__ => match arg_0__ with | UnfNever => true | _ => false end.

Definition canUnfold : Unfolding -> bool :=
  fun arg_0__ => false.

Definition cmpAltCon : AltCon -> AltCon -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | DEFAULT, DEFAULT => Eq
    | DEFAULT, _ => Lt
    | DataAlt d1, DataAlt d2 => GHC.Base.compare (dataConTag d1) (dataConTag d2)
    | DataAlt _, DEFAULT => Gt
    | LitAlt l1, LitAlt l2 => GHC.Base.compare l1 l2
    | LitAlt _, DEFAULT => Gt
    | con1, con2 =>
        Panic.warnPprTrace (true) (GHC.Base.hs_string__
                            "ghc/compiler/coreSyn/CoreSyn.hs") #1700 (GHC.Base.mappend (GHC.Base.mappend
                                                                                        (Datatypes.id
                                                                                         (GHC.Base.hs_string__
                                                                                          "Comparing incomparable AltCons"))
                                                                                        Panic.someSDoc) Panic.someSDoc)
        Lt
    end.

Definition cmpAlt {a : Type} {b : Type}
   : (AltCon * a * b)%type -> (AltCon * a * b)%type -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair (pair con1 _) _, pair (pair con2 _) _ => cmpAltCon con1 con2
    end.

Definition ltAlt {a : Type} {b : Type}
   : (AltCon * a * b)%type -> (AltCon * a * b)%type -> bool :=
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
       let 'pair (pair con bndrs) rhs := arg_0__ in
       pair (pair con (let cont_1__ arg_2__ := let 'TB b _ := arg_2__ in cons b nil in
                   Coq.Lists.List.flat_map cont_1__ bndrs)) (deTagExpr rhs) in
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

Definition deTagBind {t} : TaggedBind t -> CoreBind :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec (TB b _) rhs => NonRec b (deTagExpr rhs)
    | Rec prs =>
        Rec (let cont_2__ arg_3__ :=
               let 'pair (TB b _) rhs := arg_3__ in
               cons (pair b (deTagExpr rhs)) nil in
             Coq.Lists.List.flat_map cont_2__ prs)
    end.

Definition deTagAlt {t} : TaggedAlt t -> CoreAlt :=
  fun '(pair (pair con bndrs) rhs) =>
    pair (pair con (let cont_1__ arg_2__ := let 'TB b _ := arg_2__ in cons b nil in
                Coq.Lists.List.flat_map cont_1__ bndrs)) (deTagExpr rhs).

Definition mkApps {b : Type} : Expr b -> list (Arg b) -> Expr b :=
  fun f args => Data.Foldable.foldl App f args.

Definition mkCoApps {b : Type} : Expr b -> list Coercion -> Expr b :=
  fun f args => Data.Foldable.foldl (fun e a => App e (Mk_Coercion a)) f args.

Definition varToCoreExpr {b : Type} : CoreBndr -> Expr b :=
  fun v =>
    if andb Util.debugIsOn (negb (true)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreSyn.hs")
          #1920)
    else Mk_Var v.

Definition mkVarApps {b : Type} : Expr b -> list Var -> Expr b :=
  fun f vars => Data.Foldable.foldl (fun e a => App e (varToCoreExpr a)) f vars.

Definition mkConApp {b : Type} : DataCon -> list (Arg b) -> Expr b :=
  fun con args => mkApps (Mk_Var (dataConWorkId con)) args.

Definition mkTyArg {b : Type} : Type_ -> Expr b :=
  fun ty =>
    match isCoercionTy_maybe ty with
    | Some co => Mk_Coercion co
    | _ => Mk_Type ty
    end.

Definition mkTyApps {b : Type} : Expr b -> list Type_ -> Expr b :=
  fun f args => Data.Foldable.foldl (fun e a => App e (mkTyArg a)) f args.

Definition mkConApp2 {b : Type} : DataCon -> list Type_ -> list Var -> Expr b :=
  fun con tys arg_ids =>
    mkApps (mkApps (Mk_Var (dataConWorkId con)) (GHC.Base.map Mk_Type tys))
           (GHC.Base.map varToCoreExpr arg_ids).

(* Skipping definition `Core.mkIntLit' *)

(* Skipping definition `Core.mkIntLitInt' *)

(* Skipping definition `Core.mkWordLit' *)

(* Skipping definition `Core.mkWordLitWord' *)

(* Skipping definition `Core.mkWord64LitWord64' *)

(* Skipping definition `Core.mkInt64LitInt64' *)

Definition mkCharLit {b : Type} : GHC.Char.Char -> Expr b :=
  fun c => Lit (mkMachChar c).

Definition mkStringLit {b : Type} : GHC.Base.String -> Expr b :=
  fun s => Lit (mkMachString s).

Definition mkFloatLit {b : Type} : GHC.Real.Rational -> Expr b :=
  fun f => Lit (mkMachFloat f).

(* Skipping definition `Core.mkFloatLitFloat' *)

Definition mkDoubleLit {b : Type} : GHC.Real.Rational -> Expr b :=
  fun d => Lit (mkMachDouble d).

(* Skipping definition `Core.mkDoubleLitDouble' *)

Definition mkLams {b : Type} : list b -> Expr b -> Expr b :=
  fun binders body => Data.Foldable.foldr Lam body binders.

Definition mkLet {b : Type} : Bind b -> Expr b -> Expr b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Rec nil, body => body
    | bind, body => Let bind body
    end.

Definition mkLets {b : Type} : list (Bind b) -> Expr b -> Expr b :=
  fun binds body => Data.Foldable.foldr mkLet body binds.

Definition mkLetNonRec {b : Type} : b -> Expr b -> Expr b -> Expr b :=
  fun b rhs body => Let (NonRec b rhs) body.

Definition mkLetRec {b : Type} : list (b * Expr b)%type -> Expr b -> Expr b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | nil, body => body
    | bs, body => Let (Rec bs) body
    end.

Definition mkTyBind : TyVar -> Type_ -> CoreBind :=
  fun tv ty => NonRec tv (Mk_Type ty).

Definition mkCoBind : CoVar -> Coercion -> CoreBind :=
  fun cv co => NonRec cv (Mk_Coercion co).

Definition varsToCoreExprs {b : Type} : list CoreBndr -> list (Expr b) :=
  fun vs => GHC.Base.map varToCoreExpr vs.

(* Skipping definition `Core.applyTypeToArg' *)

(* Skipping definition `Core.exprToType' *)

Definition exprToCoercion_maybe : CoreExpr -> option Coercion :=
  fun arg_0__ => match arg_0__ with | Mk_Coercion co => Some co | _ => None end.

Definition bindersOf {b : Type} : Bind b -> list b :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec binder _ => cons binder nil
    | Rec pairs =>
        let cont_2__ arg_3__ := let 'pair binder _ := arg_3__ in cons binder nil in
        Coq.Lists.List.flat_map cont_2__ pairs
    end.

Definition bindersOfBinds {b : Type} : list (Bind b) -> list b :=
  fun binds =>
    Data.Foldable.foldr (Coq.Init.Datatypes.app GHC.Base.∘ bindersOf) nil binds.

Definition rhssOfBind {b : Type} : Bind b -> list (Expr b) :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec _ rhs => cons rhs nil
    | Rec pairs =>
        let cont_2__ arg_3__ := let 'pair _ rhs := arg_3__ in cons rhs nil in
        Coq.Lists.List.flat_map cont_2__ pairs
    end.

Definition rhssOfAlts {b : Type} : list (Alt b) -> list (Expr b) :=
  fun alts =>
    let cont_0__ arg_1__ := let 'pair (pair _ _) e := arg_1__ in cons e nil in
    Coq.Lists.List.flat_map cont_0__ alts.

Fixpoint flattenBinds {b : Type} (arg_0__ : list (Bind b)) : list (b *
                                                                   Expr b)%type
  := match arg_0__ with
     | cons (NonRec b r) binds => cons (pair b r) (flattenBinds binds)
     | cons (Rec prs1) binds => Coq.Init.Datatypes.app prs1 (flattenBinds binds)
     | nil => nil
     end.

Definition collectBinders {b : Type} : Expr b -> (list b * Expr b)%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | bs, Lam b e => go (cons b bs) e
         | bs, e => pair (GHC.List.reverse bs) e
         end in
    go nil expr.

Definition collectTyBinders : CoreExpr -> (list TyVar * CoreExpr)%type :=
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

Definition collectValBinders : CoreExpr -> (list Id * CoreExpr)%type :=
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

Definition collectTyAndValBinders
   : CoreExpr -> (list TyVar * list Id * CoreExpr)%type :=
  fun expr =>
    let 'pair tvs body1 := collectTyBinders expr in
    let 'pair ids body := collectValBinders body1 in
    pair (pair tvs ids) body.

Definition collectNBinders {b : Type}
   : nat -> Expr b -> (list b * Expr b)%type :=
  fun orig_n orig_expr =>
    let fix go arg_0__ arg_1__ arg_2__
      := match arg_0__, arg_1__, arg_2__ with
         | num_3__, bs, expr =>
             if num_3__ GHC.Base.== #0 : bool then pair (GHC.List.reverse bs) expr else
             match arg_0__, arg_1__, arg_2__ with
             | n, bs, Lam b e => go (n GHC.Num.- #1) (cons b bs) e
             | _, _, _ =>
                 Panic.panicStr (GHC.Base.hs_string__ "collectNBinders") Panic.someSDoc
             end
         end in
    go orig_n nil orig_expr.

Definition collectArgs {b : Type} : Expr b -> (Expr b * list (Arg b))%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | App f a, as_ => go f (cons a as_)
         | e, as_ => pair e as_
         end in
    go expr nil.

Definition collectArgsTicks {b : Type}
   : (Tickish Id -> bool) ->
     Expr b -> (Expr b * list (Arg b) * list (Tickish Id))%type :=
  fun skipTick expr =>
    let fix go arg_0__ arg_1__ arg_2__
      := match arg_0__, arg_1__, arg_2__ with
         | App f a, as_, ts => go f (cons a as_) ts
         | e, as_, ts => pair (pair e as_) (GHC.List.reverse ts)
         end in
    go expr nil nil.

Definition isRuntimeVar : Var -> bool :=
  isId.

Definition isTypeArg {b : Type} : Expr b -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_Type _ => true | _ => false end.

Definition isValArg {b : Type} : Expr b -> bool :=
  fun e => negb (isTypeArg e).

Definition isRuntimeArg : CoreExpr -> bool :=
  isValArg.

Definition isTyCoArg {b : Type} : Expr b -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Type _ => true
    | Mk_Coercion _ => true
    | _ => false
    end.

Definition valBndrCount : list CoreBndr -> nat :=
  Util.count isId.

Definition valArgCount {b : Type} : list (Arg b) -> nat :=
  Util.count isValArg.

Program Definition collectAnnArgs {b : Type} {a : Type}
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

Program Definition collectAnnArgsTicks {b : Type} {a : Type}
   : (Tickish Var -> bool) ->
     AnnExpr b a -> (AnnExpr b a * list (AnnExpr b a) * list (Tickish Var))%type :=
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

Definition deAnnotate'
   : forall {bndr : Type} {annot : Type}, AnnExpr' bndr annot -> Expr bndr :=
  fix deAnnotate' {bndr annot : Type} (arg_0__ : AnnExpr' bndr annot) : Expr bndr
    := let deAnnotate {bndr annot : Type} (arg_0__ : AnnExpr bndr annot)
        : Expr bndr :=
         let 'pair _ e := arg_0__ in
         deAnnotate' e in
       let deAnnAlt {bndr annot : Type} (arg_0__ : AnnAlt bndr annot) : Alt bndr :=
         let 'pair (pair con args) rhs := arg_0__ in
         pair (pair con args) (deAnnotate rhs) in
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

Definition deAnnotate {bndr : Type} {annot : Type}
   : AnnExpr bndr annot -> Expr bndr :=
  fun '(pair _ e) => deAnnotate' e.

Definition deAnnAlt {bndr : Type} {annot : Type}
   : AnnAlt bndr annot -> Alt bndr :=
  fun '(pair (pair con args) rhs) => pair (pair con args) (deAnnotate rhs).

Definition deAnnBind
   : forall {b : Type} {annot : Type}, AnnBind b annot -> Bind b :=
  fix deAnnotate' {bndr annot : Type} (arg_0__ : AnnExpr' bndr annot) : Expr bndr
    := let deAnnotate {bndr annot : Type} (arg_0__ : AnnExpr bndr annot)
        : Expr bndr :=
         let 'pair _ e := arg_0__ in
         deAnnotate' e in
       let deAnnAlt {bndr annot : Type} (arg_0__ : AnnAlt bndr annot) : Alt bndr :=
         let 'pair (pair con args) rhs := arg_0__ in
         pair (pair con args) (deAnnotate rhs) in
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

Program Definition collectAnnBndrs {bndr : Type} {annot : Type}
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

(* External variables:
     BranchFlag BranchIndex Branched BuiltInSynFamily CType CoAxBranch CoAxiom
     CoAxiomRule Coercion CostCentre DataConBoxer Eq ForeignCall Gt Kind Literal Lt
     None PredType PrimOp Role Some ThetaType TyBinder TyThing Type Type_ Unbranched
     andb bool comparison cons false list mkMachChar mkMachDouble mkMachFloat
     mkMachString nat negb nil op_zt__ option orb pair size_AnnExpr' snd true tt unit
     BasicTypes.Activation BasicTypes.AlwaysActive BasicTypes.Arity BasicTypes.Boxity
     BasicTypes.ConTag BasicTypes.ConTagZ BasicTypes.DefMethSpec
     BasicTypes.IAmALoopBreaker BasicTypes.IAmDead BasicTypes.InlinePragma
     BasicTypes.JoinArity BasicTypes.LeftOrRight BasicTypes.ManyOccs
     BasicTypes.NoOneShotInfo BasicTypes.NoTailCallInfo BasicTypes.OccInfo
     BasicTypes.OneOcc BasicTypes.OneShotInfo BasicTypes.RuleName
     BasicTypes.SourceText BasicTypes.TupleSort BasicTypes.TyPrec
     BasicTypes.defaultInlinePragma BasicTypes.isAlwaysTailCalled
     BasicTypes.noOccInfo BasicTypes.zapFragileOcc BinNat.N.of_nat BinNums.N
     BooleanFormula.BooleanFormula Coq.Init.Datatypes.app Coq.Init.Peano.lt
     Coq.Lists.List.flat_map Coq.Lists.List.length Data.Foldable.foldl
     Data.Foldable.foldr Data.Function.on Data.Tuple.fst Datatypes.id
     DynFlags.DynFlags FastString.FastString FieldLabel.FieldLabel
     FieldLabel.FieldLabelEnv FieldLabel.FieldLabelString GHC.Base.Eq_ GHC.Base.Monad
     GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.compare__
     GHC.Base.eq_default GHC.Base.map GHC.Base.mappend GHC.Base.max__ GHC.Base.min
     GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zg__ GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____
     GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlze__
     GHC.Base.op_zlze____ GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Base.return_
     GHC.Char.Char GHC.Err.error GHC.List.reverse GHC.Num.Integer GHC.Num.fromInteger
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.coerce GHC.Prim.seq
     GHC.Real.Rational HsToCoq.DeferredFix.deferredFix1
     HsToCoq.DeferredFix.deferredFix2 HsToCoq.Err.Build_Default HsToCoq.Err.Default
     HsToCoq.Err.default HsToCoq.Wf.wfFix2 HsToCoq.Wf.wfFix3 Maybes.orElse
     Module.Module Module.ModuleSet Module.emptyModuleSet Module.mkModuleSet
     Name.Name Name.NamedThing Name.getName__ Name.getOccName__ Name.nameOccName
     Name.nameUnique Name.setNameUnique NameEnv.NameEnv NameEnv.emptyNameEnv
     OccName.HasOccName OccName.OccName OccName.TidyOccEnv OccName.emptyTidyOccEnv
     OccName.occName__ Pair.Pair Panic.assertPanic Panic.panicStr Panic.someSDoc
     Panic.warnPprTrace SrcLoc.RealSrcSpan SrcLoc.SrcSpan UniqFM.UniqFM
     UniqFM.addListToUFM UniqFM.addToUFM UniqFM.addToUFM_Acc UniqFM.addToUFM_C
     UniqFM.addToUFM_Directly UniqFM.alterUFM UniqFM.anyUFM UniqFM.delFromUFM
     UniqFM.delFromUFM_Directly UniqFM.delListFromUFM UniqFM.disjointUFM
     UniqFM.elemUFM UniqFM.elemUFM_Directly UniqFM.eltsUFM UniqFM.emptyUFM
     UniqFM.filterUFM UniqFM.filterUFM_Directly UniqFM.intersectUFM UniqFM.isNullUFM
     UniqFM.listToUFM UniqFM.listToUFM_Directly UniqFM.lookupUFM
     UniqFM.lookupUFM_Directly UniqFM.lookupWithDefaultUFM UniqFM.mapUFM
     UniqFM.minusUFM UniqFM.nonDetFoldUFM UniqFM.nonDetUFMToList UniqFM.partitionUFM
     UniqFM.plusMaybeUFM_C UniqFM.plusUFM UniqFM.plusUFMList UniqFM.plusUFM_C
     UniqFM.plusUFM_CD UniqFM.unitUFM UniqSet.UniqSet UniqSet.addListToUniqSet
     UniqSet.addOneToUniqSet UniqSet.delListFromUniqSet UniqSet.delOneFromUniqSet
     UniqSet.delOneFromUniqSet_Directly UniqSet.elemUniqSet_Directly
     UniqSet.elementOfUniqSet UniqSet.emptyUniqSet UniqSet.filterUniqSet
     UniqSet.getUniqSet UniqSet.intersectUniqSets UniqSet.isEmptyUniqSet
     UniqSet.lookupUniqSet UniqSet.lookupUniqSet_Directly UniqSet.minusUniqSet
     UniqSet.mkUniqSet UniqSet.nonDetEltsUniqSet UniqSet.nonDetFoldUniqSet
     UniqSet.partitionUniqSet UniqSet.sizeUniqSet UniqSet.unionManyUniqSets
     UniqSet.unionUniqSets UniqSet.uniqSetAll UniqSet.uniqSetAny UniqSet.unitUniqSet
     UniqSupply.UniqSupply Unique.Uniquable Unique.Unique Unique.deriveUnique
     Unique.getKey Unique.getUnique Unique.getUnique__ Unique.isLocalUnique
     Unique.mkUniqueGrimily Unique.nonDetCmpUnique Util.HasDebugCallStack Util.count
     Util.debugIsOn Util.foldl2 Util.zipEqual
*)
