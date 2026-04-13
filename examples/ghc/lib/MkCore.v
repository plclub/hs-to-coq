(* Default settings (from HsToRocq.Rocq.Preamble) *)

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
Require FastString.
Require GHC.Base.
Require GHC.Char.
Require GHC.Num.
Require HsSyn.
Require HsToRocq.Err.
Require Name.
Require UniqSupply.
Require Unique.
Require Util.

(* Converted type declarations: *)

Inductive MkStringIds : Type :=
  | Mk_MkStringIds (unpackCStringId : Core.Id) (unpackCStringUtf8Id : Core.Id)
   : MkStringIds.

Inductive FloatBind : Type :=
  | FloatLet : Core.CoreBind -> FloatBind
  | FloatCase
   : Core.CoreExpr -> Core.Id -> Core.AltCon -> list Core.Var -> FloatBind.

Instance Default__MkStringIds : HsToRocq.Err.Default MkStringIds :=
  HsToRocq.Err.Build_Default _ (Mk_MkStringIds HsToRocq.Err.default
                              HsToRocq.Err.default).

#[global] Definition unpackCStringId (arg_0__ : MkStringIds) :=
  let 'Mk_MkStringIds unpackCStringId _ := arg_0__ in
  unpackCStringId.

#[global] Definition unpackCStringUtf8Id (arg_0__ : MkStringIds) :=
  let 'Mk_MkStringIds _ unpackCStringUtf8Id := arg_0__ in
  unpackCStringUtf8Id.

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `MkCore.Outputable__FloatBind' *)

Axiom sortQuantVars : list Core.Var -> list Core.Var.

Axiom mkCoreLet : Core.CoreBind -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkCoreLams : list Core.CoreBndr -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkCoreLets : list Core.CoreBind -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkCoreConApps : Core.DataCon -> list Core.CoreExpr -> Core.CoreExpr.

Axiom mkCoreApps : Core.CoreExpr -> list Core.CoreExpr -> Core.CoreExpr.

Axiom mkCoreApp : GHC.Base.String ->
                  Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkCoreAppTyped : GHC.Base.String ->
                       (Core.CoreExpr * AxiomatizedTypes.Type_)%type ->
                       Core.CoreExpr -> (Core.CoreExpr * AxiomatizedTypes.Type_)%type.

Axiom mkWildValBinder : Core.Mult -> AxiomatizedTypes.Type_ -> Core.Id.

Axiom mkWildCase : Core.CoreExpr ->
                   Core.Scaled AxiomatizedTypes.Type_ ->
                   AxiomatizedTypes.Type_ -> list Core.CoreAlt -> Core.CoreExpr.

Axiom mkIfThenElse : Core.CoreExpr ->
                     Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr.

Axiom castBottomExpr : Core.CoreExpr -> AxiomatizedTypes.Type_ -> Core.CoreExpr.

Axiom mkLitRubbish : AxiomatizedTypes.Type_ -> option Core.CoreExpr.

Axiom mkIntExpr : Platform.Platform -> GHC.Num.Integer -> Core.CoreExpr.

Axiom mkUncheckedIntExpr : GHC.Num.Integer -> Core.CoreExpr.

Axiom mkIntExprInt : Platform.Platform -> nat -> Core.CoreExpr.

Axiom mkWordExpr : Platform.Platform -> GHC.Num.Integer -> Core.CoreExpr.

(* Skipping definition `MkCore.mkIntegerExpr' *)

(* Skipping definition `MkCore.mkNaturalExpr' *)

(* Skipping definition `MkCore.mkFloatExpr' *)

(* Skipping definition `MkCore.mkDoubleExpr' *)

Axiom mkCharExpr : GHC.Char.Char -> Core.CoreExpr.

(* Skipping definition `MkCore.mkStringExpr' *)

(* Skipping definition `MkCore.mkStringExprFS' *)

Axiom mkStringExprFSLookup : forall {m},
                             forall `{GHC.Base.Monad m},
                             (Name.Name -> m Core.Id) -> FastString.FastString -> m Core.CoreExpr.

Axiom getMkStringIds : forall {m : Type -> Type},
                       forall `{GHC.Base.Applicative m}, (Name.Name -> m Core.Id) -> m MkStringIds.

Axiom mkStringExprFSWith : MkStringIds ->
                           FastString.FastString -> Core.CoreExpr.

Axiom mkCoreBoxedTuple : forall `{Util.HasDebugCallStack},
                         list Core.CoreExpr -> Core.CoreExpr.

Axiom mkCoreUnboxedTuple : list Core.CoreExpr -> Core.CoreExpr.

Axiom mkCoreTupBoxity : HsSyn.Boxity -> list Core.CoreExpr -> Core.CoreExpr.

Axiom mkCoreVarTupTy : list Core.Id -> AxiomatizedTypes.Type_.

Axiom mkCoreTup : list Core.CoreExpr -> Core.CoreExpr.

Axiom mkCoreUnboxedSum : nat ->
                         nat -> list AxiomatizedTypes.Type_ -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkBigCoreVarTupSolo : list Core.Id -> Core.CoreExpr.

Axiom mkBigCoreVarTup : list Core.Id -> Core.CoreExpr.

Axiom mkBigCoreTup : list Core.CoreExpr -> Core.CoreExpr.

Axiom mkBigCoreVarTupTy : forall `{Util.HasDebugCallStack},
                          list Core.Id -> AxiomatizedTypes.Type_.

Axiom mkBigCoreTupTy : forall `{Util.HasDebugCallStack},
                       list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom unitExpr : Core.CoreExpr.

Axiom wrapBox : Core.CoreExpr -> Core.CoreExpr.

Axiom boxTy : forall `{Util.HasDebugCallStack},
              AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom unwrapBox : UniqSupply.UniqSupply ->
                  Core.Id ->
                  Core.CoreExpr -> (UniqSupply.UniqSupply * Core.Id * Core.CoreExpr)%type.

Axiom mkChunkified : forall {a : Type}, (list a -> a) -> list a -> a.

Axiom chunkify : forall {a : Type}, list a -> list (list a).

Axiom mkBigTupleSelector : list Core.Id ->
                           Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkBigTupleSelectorSolo : list Core.Id ->
                               Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkSmallTupleSelector : list Core.Id ->
                             Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkSmallTupleSelector1 : list Core.Id ->
                              Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkBigTupleCase : forall {m : Type -> Type},
                       forall `{UniqSupply.MonadUnique m},
                       list Core.Id -> Core.CoreExpr -> Core.CoreExpr -> m Core.CoreExpr.

Axiom mkSmallTupleCase : list Core.Id ->
                         Core.CoreExpr -> Core.Id -> Core.CoreExpr -> Core.CoreExpr.

Axiom wrapFloat : FloatBind -> Core.CoreExpr -> Core.CoreExpr.

Axiom wrapFloats : list FloatBind -> Core.CoreExpr -> Core.CoreExpr.

Axiom bindBindings : Core.CoreBind -> list Core.Var.

Axiom floatBindings : FloatBind -> list Core.Var.

Axiom mkNilExpr : AxiomatizedTypes.Type_ -> Core.CoreExpr.

Axiom mkConsExpr : AxiomatizedTypes.Type_ ->
                   Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkListExpr : AxiomatizedTypes.Type_ ->
                   list Core.CoreExpr -> Core.CoreExpr.

(* Skipping definition `MkCore.mkFoldrExpr' *)

(* Skipping definition `MkCore.mkBuildExpr' *)

Axiom mkNothingExpr : AxiomatizedTypes.Type_ -> Core.CoreExpr.

Axiom mkJustExpr : AxiomatizedTypes.Type_ -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkRuntimeErrorApp : Core.Id ->
                          AxiomatizedTypes.Type_ -> GHC.Base.String -> Core.CoreExpr.

Axiom errorIds : list Core.Id.

Axiom recSelErrorName : Name.Name.

Axiom recConErrorName : Name.Name.

Axiom patErrorName : Name.Name.

Axiom typeErrorName : Name.Name.

Axiom noMethodBindingErrorName : Name.Name.

Axiom nonExhaustiveGuardsErrorName : Name.Name.

Axiom err_nm : GHC.Base.String -> Unique.Unique -> Core.Id -> Name.Name.

Axiom rEC_SEL_ERROR_ID : Core.Id.

Axiom rEC_CON_ERROR_ID : Core.Id.

Axiom pAT_ERROR_ID : Core.Id.

Axiom nO_METHOD_BINDING_ERROR_ID : Core.Id.

Axiom nON_EXHAUSTIVE_GUARDS_ERROR_ID : Core.Id.

Axiom tYPE_ERROR_ID : Core.Id.

Axiom absentSumFieldErrorName : Name.Name.

Axiom aBSENT_SUM_FIELD_ERROR_ID : Core.Id.

Axiom mkExceptionId : Name.Name -> Core.Id.

Axiom divergingIdInfo : list Core.Demand -> Core.IdInfo.

Axiom iMPOSSIBLE_ERROR_ID : Core.Id.

Axiom iMPOSSIBLE_CONSTRAINT_ERROR_ID : Core.Id.

Axiom impossibleErrorName : Name.Name.

Axiom impossibleConstraintErrorName : Name.Name.

Axiom mkImpossibleExpr : AxiomatizedTypes.Type_ ->
                         GHC.Base.String -> Core.CoreExpr.

Axiom mkAbsentErrorApp : AxiomatizedTypes.Type_ ->
                         GHC.Base.String -> Core.CoreExpr.

Axiom absentErrorName : Name.Name.

Axiom absentConstraintErrorName : Name.Name.

Axiom aBSENT_ERROR_ID : Core.Id.

Axiom aBSENT_CONSTRAINT_ERROR_ID : Core.Id.

Axiom mkRuntimeErrorId : BasicTypes.TypeOrConstraint -> Name.Name -> Core.Id.

Axiom mk_runtime_error_id : Name.Name -> AxiomatizedTypes.Type_ -> Core.Id.

Axiom mkRuntimeErrorTy : BasicTypes.TypeOrConstraint -> AxiomatizedTypes.Type_.

(* External variables:
     Type list nat op_zt__ option AxiomatizedTypes.Type_ BasicTypes.TypeOrConstraint
     Core.AltCon Core.CoreAlt Core.CoreBind Core.CoreBndr Core.CoreExpr Core.DataCon
     Core.Demand Core.Id Core.IdInfo Core.Mult Core.Scaled Core.Var
     FastString.FastString GHC.Base.Applicative GHC.Base.Monad GHC.Base.String
     GHC.Char.Char GHC.Num.Integer HsSyn.Boxity HsToRocq.Err.Build_Default
     HsToRocq.Err.Default HsToRocq.Err.default Name.Name Platform.Platform
     UniqSupply.MonadUnique UniqSupply.UniqSupply Unique.Unique
     Util.HasDebugCallStack
*)
