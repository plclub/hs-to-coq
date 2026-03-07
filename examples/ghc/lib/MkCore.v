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
Require Constants.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require CoreUtils.
Require Data.Foldable.
Require Data.Functor.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Builtin.Types.Prim.
Require GHC.Char.
Require GHC.Core.TyCo.Compare.
Require GHC.Core.TyCo.FVs.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Types.Cpr.
Require HsSyn.
Require HsToCoq.Err.
Require Id.
Require Literal.
Require Name.
Require Panic.
Require PrelNames.
Require TysWiredIn.
Require UniqSupply.
Require Unique.
Require Util.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive MkStringIds : Type :=
  | MkStringIds (unpackCStringId : Core.Id) (unpackCStringUtf8Id : Core.Id)
   : MkStringIds.

Inductive FloatBind : Type :=
  | FloatLet : Core.CoreBind -> FloatBind
  | FloatCase
   : Core.CoreExpr -> Core.Id -> Core.AltCon -> list Core.Var -> FloatBind.

Instance Default__MkStringIds : HsToCoq.Err.Default MkStringIds :=
  HsToCoq.Err.Build_Default _ (MkStringIds HsToCoq.Err.default
                             HsToCoq.Err.default).

#[global] Definition unpackCStringId (arg_0__ : MkStringIds) :=
  let 'MkStringIds unpackCStringId _ := arg_0__ in
  unpackCStringId.

#[global] Definition unpackCStringUtf8Id (arg_0__ : MkStringIds) :=
  let 'MkStringIds _ unpackCStringUtf8Id := arg_0__ in
  unpackCStringUtf8Id.

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `MkCore.Outputable__FloatBind' *)

Axiom sortQuantVars : list Core.Var -> list Core.Var.

#[global] Definition mkCoreLet
   : Core.CoreBind -> Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Core.NonRec bndr rhs, body => CoreUtils.bindNonRec bndr rhs body
    | bind, body => Core.Let bind body
    end.

#[global] Definition mkCoreLams
   : list Core.CoreBndr -> Core.CoreExpr -> Core.CoreExpr :=
  Core.mkLams.

#[global] Definition mkCoreLets
   : list Core.CoreBind -> Core.CoreExpr -> Core.CoreExpr :=
  fun binds body => Data.Foldable.foldr mkCoreLet body binds.

#[global] Definition mkCoreAppTyped
   : GHC.Base.String ->
     (Core.CoreExpr * AxiomatizedTypes.Type_)%type ->
     Core.CoreExpr -> (Core.CoreExpr * AxiomatizedTypes.Type_)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, pair fun_ fun_ty, Core.Mk_Type ty =>
        pair (Core.App fun_ (Core.Mk_Type ty)) ((@Core.piResultTy tt) fun_ty ty)
    | _, pair fun_ fun_ty, Core.Mk_Coercion co =>
        pair (Core.App fun_ (Core.Mk_Coercion co)) (Core.funResultTy fun_ty)
    | d, pair fun_ fun_ty, arg =>
        Panic.assertPpr (Core.isFunTy fun_ty) (Panic.someSDoc) (pair (Core.App fun_ arg)
                                                                     (Core.funResultTy fun_ty))
    end.

#[global] Definition mkCoreApps
   : Core.CoreExpr -> list Core.CoreExpr -> Core.CoreExpr :=
  fun fun_ args =>
    let fun_ty := CoreUtils.exprType fun_ in
    let doc_string := Panic.someSDoc in
    Data.Tuple.fst (Data.Foldable.foldl' (mkCoreAppTyped doc_string) (pair fun_
                                                                           fun_ty) args).

#[global] Definition mkCoreConApps
   : Core.DataCon -> list Core.CoreExpr -> Core.CoreExpr :=
  fun con args => mkCoreApps (Core.Mk_Var (Core.dataConWorkId con)) args.

#[global] Definition mkCoreApp
   : GHC.Base.String -> Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr :=
  fun s fun_ arg =>
    Data.Tuple.fst (mkCoreAppTyped s (pair fun_ (CoreUtils.exprType fun_)) arg).

#[global] Definition mkWildValBinder
   : Core.Mult -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun w ty => Id.mkLocalIdOrCoVar PrelNames.wildCardName w ty.

#[global] Definition mkWildCase
   : Core.CoreExpr ->
     Core.Scaled AxiomatizedTypes.Type_ ->
     AxiomatizedTypes.Type_ -> list Core.CoreAlt -> Core.CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | scrut, Core.Scaled w scrut_ty, res_ty, alts =>
        Core.Case scrut (mkWildValBinder w scrut_ty) res_ty alts
    end.

#[global] Definition mkIfThenElse
   : Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr :=
  fun guard then_expr else_expr =>
    mkWildCase guard (Core.linear TysWiredIn.boolTy) (CoreUtils.exprType then_expr)
    (cons (Core.Alt (Core.DataAlt TysWiredIn.falseDataCon) nil else_expr) (cons
           (Core.Alt (Core.DataAlt TysWiredIn.trueDataCon) nil then_expr) nil)).

#[global] Definition castBottomExpr
   : Core.CoreExpr -> AxiomatizedTypes.Type_ -> Core.CoreExpr :=
  fun e res_ty =>
    let e_ty := CoreUtils.exprType e in
    if GHC.Core.TyCo.Compare.eqType e_ty res_ty : bool then e else
    Core.Case e (mkWildValBinder Core.OneTy e_ty) res_ty nil.

#[global] Definition mkLitRubbish
   : AxiomatizedTypes.Type_ -> option Core.CoreExpr :=
  fun ty =>
    match Core.sORTKind_maybe (Core.typeKind ty) with
    | Some (pair torc rep) =>
        if negb (GHC.Core.TyCo.FVs.noFreeVarsOfType rep) : bool then None else
        if Core.isCoVarType ty : bool then None else
        Some (Core.mkTyApps (Core.Lit (Literal.LitRubbish torc rep)) (cons ty nil))
    | _ => GHC.Err.patternFailure
    end.

Axiom mkIntExpr : Platform.Platform -> GHC.Num.Integer.Integer -> Core.CoreExpr.

#[global] Definition mkUncheckedIntExpr
   : GHC.Num.Integer.Integer -> Core.CoreExpr :=
  fun i =>
    mkCoreConApps TysWiredIn.intDataCon (cons (Core.Lit (Literal.mkLitIntUnchecked
                                                         i)) nil).

Axiom mkIntExprInt : Platform.Platform -> nat -> Core.CoreExpr.

Axiom mkWordExpr : Platform.Platform ->
                   GHC.Num.Integer.Integer -> Core.CoreExpr.

(* Skipping definition `MkCore.mkIntegerExpr' *)

(* Skipping definition `MkCore.mkNaturalExpr' *)

(* Skipping definition `MkCore.mkFloatExpr' *)

(* Skipping definition `MkCore.mkDoubleExpr' *)

#[global] Definition mkCharExpr : GHC.Char.Char -> Core.CoreExpr :=
  fun c => mkCoreConApps TysWiredIn.charDataCon (cons (Core.mkCharLit c) nil).

(* Skipping definition `MkCore.mkStringExpr' *)

(* Skipping definition `MkCore.mkStringExprFS' *)

#[global] Definition getMkStringIds {m : Type -> Type} `{GHC.Base.Applicative m}
   : (Name.Name -> m Core.Id) -> m MkStringIds :=
  fun lookupM =>
    Data.Functor.op_zlzdzg__ MkStringIds (lookupM PrelNames.unpackCStringName)
    GHC.Base.<*>
    lookupM PrelNames.unpackCStringUtf8Name.

#[global] Definition mkNilExpr : AxiomatizedTypes.Type_ -> Core.CoreExpr :=
  fun ty => mkCoreConApps TysWiredIn.nilDataCon (cons (Core.Mk_Type ty) nil).

#[global] Definition mkStringExprFSWith
   : MkStringIds -> GHC.Data.FastString.FastString -> Core.CoreExpr :=
  fun ids str =>
    let lit := Core.Lit (Literal.LitString (GHC.Data.FastString.bytesFS str)) in
    let safeChar :=
      fun c =>
        andb (GHC.Base.ord c GHC.Base.>= #1) (GHC.Base.ord c GHC.Base.<= #127) in
    let chars := GHC.Data.FastString.unpackFS str in
    if GHC.Data.FastString.nullFS str : bool then mkNilExpr TysWiredIn.charTy else
    if Data.Foldable.all safeChar chars : bool
    then let unpack_id := unpackCStringId ids in
         Core.App (Core.Mk_Var unpack_id) lit else
    let unpack_utf8_id := unpackCStringUtf8Id ids in
    Core.App (Core.Mk_Var unpack_utf8_id) lit.

#[global] Definition mkStringExprFSLookup {m} `{GHC.Base.Monad m}
   : (Name.Name -> m Core.Id) ->
     GHC.Data.FastString.FastString -> m Core.CoreExpr :=
  fun lookupM str =>
    getMkStringIds lookupM GHC.Base.>>=
    (fun mk => GHC.Base.pure (mkStringExprFSWith mk str)).

#[global] Definition mkCoreBoxedTuple `{Util.HasDebugCallStack}
   : list Core.CoreExpr -> Core.CoreExpr :=
  fun cs =>
    Panic.assertPpr (Data.Foldable.all (Core.tcIsLiftedTypeKind GHC.Base.∘
                                        (Core.typeKind GHC.Base.∘ CoreUtils.exprType)) cs) (Panic.someSDoc)
    mkCoreConApps (TysWiredIn.tupleDataCon HsSyn.Boxed (Coq.Lists.List.length cs))
    (Coq.Init.Datatypes.app (GHC.Base.map (Core.Mk_Type GHC.Base.∘
                                           CoreUtils.exprType) cs) cs).

#[global] Definition mkCoreUnboxedTuple : list Core.CoreExpr -> Core.CoreExpr :=
  fun exps =>
    let tys := GHC.Base.map CoreUtils.exprType exps in
    mkCoreConApps (TysWiredIn.tupleDataCon HsSyn.Unboxed (Coq.Lists.List.length
                                                          tys)) (Coq.Init.Datatypes.app (GHC.Base.map (Core.Mk_Type
                                                                                                       GHC.Base.∘
                                                                                                       (@Core.getRuntimeRep
                                                                                                        tt)) tys)
                                                                                        (Coq.Init.Datatypes.app
                                                                                         (GHC.Base.map Core.Mk_Type tys)
                                                                                         exps)).

#[global] Definition mkCoreTupBoxity
   : HsSyn.Boxity -> list Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | HsSyn.Boxed, exps => mkCoreBoxedTuple exps
    | HsSyn.Unboxed, exps => mkCoreUnboxedTuple exps
    end.

#[global] Definition mkCoreVarTupTy : list Core.Id -> AxiomatizedTypes.Type_ :=
  fun ids => TysWiredIn.mkBoxedTupleTy (GHC.Base.map Id.idType ids).

#[global] Definition mkCoreTup : list Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ =>
    match arg_0__ with
    | cons c nil => c
    | cs => mkCoreBoxedTuple cs
    end.

#[global] Definition mkCoreUnboxedSum
   : nat ->
     nat -> list AxiomatizedTypes.Type_ -> Core.CoreExpr -> Core.CoreExpr :=
  fun arity alt tys exp =>
    mkCoreConApps (TysWiredIn.sumDataCon alt arity) (Coq.Init.Datatypes.app
                   (GHC.Base.map (Core.Mk_Type GHC.Base.∘ (@Core.getRuntimeRep tt)) tys)
                   (Coq.Init.Datatypes.app (GHC.Base.map Core.Mk_Type tys) (cons exp nil))).

#[global] Definition chunkify {a : Type} : list a -> list (list a) :=
  fun xs =>
    let fix split arg_0__
      := match arg_0__ with
         | nil => nil
         | xs =>
             let 'pair as_ bs := GHC.List.splitAt Constants.mAX_TUPLE_SIZE xs in
             cons as_ (split bs)
         end in
    let n_xs := Coq.Lists.List.length xs in
    if n_xs GHC.Base.<= Constants.mAX_TUPLE_SIZE : bool then cons xs nil else
    split xs.

Axiom chunkify : list Core.Id -> list (list Core.Id).

#[global] Definition mkChunkified {a : Type} : (list a -> a) -> list a -> a :=
  fun small_tuple as_ =>
    let fix mk_big_tuple arg_0__
      := match arg_0__ with
         | cons as_ nil => small_tuple as_
         | as_s => mk_big_tuple (chunkify (GHC.Base.map small_tuple as_s))
         end in
    mk_big_tuple (chunkify as_).

#[global] Definition mkBigCoreVarTupSolo : list Core.Id -> Core.CoreExpr :=
  fun arg_0__ =>
    match arg_0__ with
    | cons id nil => mkCoreBoxedTuple (cons (Core.Mk_Var id) nil)
    | ids => mkChunkified mkCoreTup (GHC.Base.map Core.Mk_Var ids)
    end.

Axiom mkBigCoreTup : list Core.CoreExpr -> Core.CoreExpr.

#[global] Definition mkBigCoreVarTup : list Core.Id -> Core.CoreExpr :=
  fun ids => mkBigCoreTup (GHC.Base.map Core.Mk_Var ids).

Axiom mkBigCoreTupTy : forall `{Util.HasDebugCallStack},
                       list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

#[global] Definition mkBigCoreVarTupTy `{Util.HasDebugCallStack}
   : list Core.Id -> AxiomatizedTypes.Type_ :=
  fun ids => mkBigCoreTupTy (GHC.Base.map Id.idType ids).

#[global] Definition unitExpr : Core.CoreExpr :=
  Core.Mk_Var TysWiredIn.unitDataConId.

#[global] Definition wrapBox : Core.CoreExpr -> Core.CoreExpr :=
  fun e =>
    let e_ty := CoreUtils.exprType e in
    match TysWiredIn.boxingDataCon e_ty with
    | TysWiredIn.BI_NoBoxNeeded => e
    | TysWiredIn.BI_Box _ boxing_expr _ => Core.App boxing_expr e
    | TysWiredIn.BI_NoBoxAvailable =>
        Panic.pprPanic (GHC.Base.hs_string__ "wrapBox") (Panic.someSDoc)
    end.

#[global] Definition boxTy `{Util.HasDebugCallStack}
   : AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ :=
  fun ty =>
    match TysWiredIn.boxingDataCon ty with
    | TysWiredIn.BI_NoBoxNeeded => ty
    | TysWiredIn.BI_Box _ _ box_ty => box_ty
    | TysWiredIn.BI_NoBoxAvailable =>
        Panic.pprPanic (GHC.Base.hs_string__ "boxTy") (Panic.someSDoc)
    end.

#[global] Definition unwrapBox
   : UniqSupply.UniqSupply ->
     Core.Id ->
     Core.CoreExpr -> (UniqSupply.UniqSupply * Core.Id * Core.CoreExpr)%type :=
  fun us var body =>
    let 'pair uniq us' := UniqSupply.takeUniqFromSupply us in
    let var_ty := Id.idType var in
    match TysWiredIn.boxingDataCon var_ty with
    | TysWiredIn.BI_NoBoxNeeded => pair (pair us var) body
    | TysWiredIn.BI_NoBoxAvailable =>
        Panic.pprPanic (GHC.Base.hs_string__ "unwrapBox") (Panic.someSDoc)
    | TysWiredIn.BI_Box box_con _ box_ty =>
        let var' :=
          Id.mkSysLocal (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "uc")) uniq
          Core.ManyTy box_ty in
        let body' :=
          Core.Case (Core.Mk_Var var') var' (CoreUtils.exprType body) (cons (Core.Alt
                                                                             (Core.DataAlt box_con) (cons var nil) body)
                                                                            nil) in
        pair (pair us' var') body'
    end.

#[global] Definition mkSmallTupleSelector1
   : list Core.Id -> Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun vars the_var scrut_var scrut =>
    Core.Case scrut scrut_var (Id.idType the_var) (cons (Core.Alt (Core.DataAlt
                                                                   (TysWiredIn.tupleDataCon HsSyn.Boxed
                                                                    (Coq.Lists.List.length vars))) vars (Core.Mk_Var
                                                                                                         the_var)) nil).

#[global] Definition mkSmallTupleSelector
   : list Core.Id -> Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | cons var nil, should_be_the_same_var, _, scrut => scrut
    | vars, the_var, scrut_var, scrut =>
        mkSmallTupleSelector1 vars the_var scrut_var scrut
    end.

#[global] Definition mkBigTupleSelector
   : list Core.Id -> Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun vars the_var scrut_var scrut =>
    let fix mk_tup_sel arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | cons vars nil, the_var => mkSmallTupleSelector vars the_var scrut_var scrut
         | vars_s, the_var =>
             let tpl_tys :=
               Coq.Lists.List.flat_map (fun gp =>
                                          cons (TysWiredIn.mkBoxedTupleTy (GHC.Base.map Id.idType gp)) nil) vars_s in
             let tpl_vs := Id.mkTemplateLocals tpl_tys in
             match (let cont_5__ arg_6__ :=
                        let 'pair tpl gp := arg_6__ in
                        if Data.Foldable.elem the_var gp : bool then cons (pair tpl gp) nil else
                        nil in
                      Coq.Lists.List.flat_map cont_5__ (Util.zipEqual (GHC.Base.hs_string__
                                                                       "mkBigTupleSelector") tpl_vs vars_s)) with
             | cons (pair tpl_v group) nil =>
                 mkSmallTupleSelector group the_var tpl_v (mk_tup_sel (chunkify tpl_vs) tpl_v)
             | _ => GHC.Err.patternFailure
             end
         end in
    mk_tup_sel (chunkify vars) the_var.

#[global] Definition mkBigTupleSelectorSolo
   : list Core.Id -> Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun vars the_var scrut_var scrut =>
    match vars with
    | cons _ nil => mkSmallTupleSelector1 vars the_var scrut_var scrut
    | _ => mkBigTupleSelector vars the_var scrut_var scrut
    end.

#[global] Definition mkSmallTupleCase
   : list Core.Id -> Core.CoreExpr -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | cons var nil, body, _scrut_var, scrut => CoreUtils.bindNonRec var scrut body
    | vars, body, scrut_var, scrut =>
        Core.Case scrut scrut_var (CoreUtils.exprType body) (cons (Core.Alt
                                                                   (Core.DataAlt (TysWiredIn.tupleDataCon HsSyn.Boxed
                                                                                  (Coq.Lists.List.length vars))) vars
                                                                   body) nil)
    end.

#[global] Definition mkBigTupleCase {m : Type -> Type} `{UniqSupply.MonadUnique
  m}
   : list Core.Id -> Core.CoreExpr -> Core.CoreExpr -> m Core.CoreExpr :=
  fun vars body scrut =>
    let new_var
     : UniqSupply.UniqSupply ->
       AxiomatizedTypes.Type_ -> (UniqSupply.UniqSupply * Core.Id)%type :=
      fun us ty =>
        let 'pair uniq us' := UniqSupply.takeUniqFromSupply us in
        let id :=
          Id.mkSysLocal (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "ds")) uniq
          Core.ManyTy ty in
        pair us' id in
    let one_tuple_case :=
      fun arg_3__ arg_4__ =>
        match arg_3__, arg_4__ with
        | chunk_vars, pair (pair us vs) body =>
            let tup_ty := TysWiredIn.mkBoxedTupleTy (GHC.Base.map Id.idType chunk_vars) in
            let 'pair us' scrut_var := new_var us tup_ty in
            let body' :=
              mkSmallTupleCase chunk_vars body scrut_var (Core.Mk_Var scrut_var) in
            pair (pair us' (cons scrut_var vs)) body'
        end in
    let unwrap :=
      fun arg_10__ arg_11__ =>
        match arg_10__, arg_11__ with
        | var, pair (pair us vars) body =>
            let 'pair (pair us' var') body' := unwrapBox us var body in
            pair (pair us' (cons var' vars)) body'
        end in
    let scrut_ty := CoreUtils.exprType scrut in
    let mk_tuple_case
     : UniqSupply.UniqSupply ->
       list (list Core.Id) -> Core.CoreExpr -> Core.CoreExpr :=
      fix mk_tuple_case (arg_16__ : UniqSupply.UniqSupply) (arg_17__
                          : list (list Core.Id)) (arg_18__ : Core.CoreExpr) : Core.CoreExpr
        := match arg_16__, arg_17__, arg_18__ with
           | us, cons vars nil, body =>
               let scrut_var :=
                 match scrut with
                 | Core.Mk_Var v => v
                 | _ => Data.Tuple.snd (new_var us scrut_ty)
                 end in
               mkSmallTupleCase vars body scrut_var scrut
           | us, vars_s, body =>
               let 'pair (pair us' vars') body' := Data.Foldable.foldr one_tuple_case (pair
                                                                                       (pair us nil) body) vars_s in
               mk_tuple_case us' (chunkify vars') body'
           end in
    UniqSupply.getUniqueSupplyM GHC.Base.>>=
    (fun us =>
       let 'pair (pair wrapped_us wrapped_vars) wrapped_body := Data.Foldable.foldr
                                                                  unwrap (pair (pair us nil) body) vars in
       GHC.Base.return_ (mk_tuple_case wrapped_us (chunkify wrapped_vars)
                                       wrapped_body)).

#[global] Definition wrapFloat : FloatBind -> Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FloatLet defns, body => Core.Let defns body
    | FloatCase e b con bs, body => CoreUtils.mkSingleAltCase e b con bs body
    end.

#[global] Definition wrapFloats
   : list FloatBind -> Core.CoreExpr -> Core.CoreExpr :=
  fun floats expr => Data.Foldable.foldr wrapFloat expr floats.

#[global] Definition bindBindings : Core.CoreBind -> list Core.Var :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.NonRec b _ => cons b nil
    | Core.Rec bnds => GHC.Base.map Data.Tuple.fst bnds
    end.

#[global] Definition floatBindings : FloatBind -> list Core.Var :=
  fun arg_0__ =>
    match arg_0__ with
    | FloatLet bnd => bindBindings bnd
    | FloatCase _ b _ bs => cons b bs
    end.

#[global] Definition mkConsExpr
   : AxiomatizedTypes.Type_ -> Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr :=
  fun ty hd tl =>
    mkCoreConApps TysWiredIn.consDataCon (cons (Core.Mk_Type ty) (cons hd (cons tl
                                                                                nil))).

#[global] Definition mkListExpr
   : AxiomatizedTypes.Type_ -> list Core.CoreExpr -> Core.CoreExpr :=
  fun ty xs => Data.Foldable.foldr (mkConsExpr ty) (mkNilExpr ty) xs.

(* Skipping definition `MkCore.mkFoldrExpr' *)

(* Skipping definition `MkCore.mkBuildExpr' *)

#[global] Definition mkNothingExpr : AxiomatizedTypes.Type_ -> Core.CoreExpr :=
  fun ty => Core.mkConApp TysWiredIn.nothingDataCon (cons (Core.Mk_Type ty) nil).

#[global] Definition mkJustExpr
   : AxiomatizedTypes.Type_ -> Core.CoreExpr -> Core.CoreExpr :=
  fun ty val =>
    Core.mkConApp TysWiredIn.justDataCon (cons (Core.Mk_Type ty) (cons val nil)).

#[global] Definition mkRuntimeErrorApp
   : Core.Id -> AxiomatizedTypes.Type_ -> GHC.Base.String -> Core.CoreExpr :=
  fun err_id res_ty err_msg =>
    let err_string := Core.Lit (Literal.mkLitString err_msg) in
    Core.mkApps (Core.Mk_Var err_id) (cons (Core.Mk_Type ((@Core.getRuntimeRep tt)
                                                          res_ty)) (cons (Core.Mk_Type res_ty) (cons err_string nil))).

Axiom aBSENT_CONSTRAINT_ERROR_ID : Core.Id.

Axiom aBSENT_ERROR_ID : Core.Id.

Axiom aBSENT_SUM_FIELD_ERROR_ID : Core.Id.

Axiom iMPOSSIBLE_CONSTRAINT_ERROR_ID : Core.Id.

Axiom iMPOSSIBLE_ERROR_ID : Core.Id.

Axiom nON_EXHAUSTIVE_GUARDS_ERROR_ID : Core.Id.

Axiom nO_METHOD_BINDING_ERROR_ID : Core.Id.

Axiom pAT_ERROR_ID : Core.Id.

Axiom rEC_CON_ERROR_ID : Core.Id.

Axiom rEC_SEL_ERROR_ID : Core.Id.

Axiom tYPE_ERROR_ID : Core.Id.

#[global] Definition errorIds : list Core.Id :=
  cons nON_EXHAUSTIVE_GUARDS_ERROR_ID (cons nO_METHOD_BINDING_ERROR_ID (cons
                                             pAT_ERROR_ID (cons rEC_CON_ERROR_ID (cons rEC_SEL_ERROR_ID (cons
                                                                                        iMPOSSIBLE_ERROR_ID (cons
                                                                                         iMPOSSIBLE_CONSTRAINT_ERROR_ID
                                                                                         (cons aBSENT_ERROR_ID (cons
                                                                                                aBSENT_CONSTRAINT_ERROR_ID
                                                                                                (cons
                                                                                                 aBSENT_SUM_FIELD_ERROR_ID
                                                                                                 (cons tYPE_ERROR_ID
                                                                                                       nil)))))))))).

Axiom err_nm : GHC.Base.String -> Unique.Unique -> Core.Id -> Name.Name.

#[global] Definition recSelErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "recSelError") PrelNames.recSelErrorIdKey
  rEC_SEL_ERROR_ID.

#[global] Definition recConErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "recConError") PrelNames.recConErrorIdKey
  rEC_CON_ERROR_ID.

#[global] Definition patErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "patError") PrelNames.patErrorIdKey pAT_ERROR_ID.

#[global] Definition typeErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "typeError") PrelNames.typeErrorIdKey
  tYPE_ERROR_ID.

#[global] Definition noMethodBindingErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "noMethodBindingError")
  PrelNames.noMethodBindingErrorIdKey nO_METHOD_BINDING_ERROR_ID.

#[global] Definition nonExhaustiveGuardsErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "nonExhaustiveGuardsError")
  PrelNames.nonExhaustiveGuardsErrorIdKey nON_EXHAUSTIVE_GUARDS_ERROR_ID.

#[global] Definition absentSumFieldErrorName : Name.Name :=
  TysWiredIn.mkWiredInIdName PrelNames.gHC_PRIM_PANIC (GHC.Data.FastString.fsLit
                                                       (GHC.Base.hs_string__ "absentSumFieldError"))
  PrelNames.absentSumFieldErrorIdKey aBSENT_SUM_FIELD_ERROR_ID.

#[global] Definition divergingIdInfo : list Core.Demand -> Core.IdInfo :=
  fun arg_dmds =>
    let arity := Coq.Lists.List.length arg_dmds in
    Core.setCprSigInfo (Core.setDmdSigInfo (Core.setArityInfo Core.vanillaIdInfo
                                                              arity) (Core.mkClosedDmdSig arg_dmds Core.botDiv))
                       (GHC.Types.Cpr.mkCprSig arity GHC.Types.Cpr.botCpr).

#[global] Definition mkExceptionId : Name.Name -> Core.Id :=
  fun name =>
    Id.mkVanillaGlobalWithInfo name (Core.mkSpecForAllTys (cons
                                                           GHC.Builtin.Types.Prim.alphaTyVar nil) (Core.mkTyVarTy
                                                                                                   GHC.Builtin.Types.Prim.alphaTyVar))
    (Core.setCafInfo (divergingIdInfo nil) Core.NoCafRefs).

#[global] Definition impossibleErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "impossibleError") PrelNames.impossibleErrorIdKey
  iMPOSSIBLE_ERROR_ID.

#[global] Definition impossibleConstraintErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "impossibleConstraintError")
  PrelNames.impossibleConstraintErrorIdKey iMPOSSIBLE_CONSTRAINT_ERROR_ID.

#[global] Definition mkImpossibleExpr
   : AxiomatizedTypes.Type_ -> GHC.Base.String -> Core.CoreExpr :=
  fun res_ty str =>
    let err_id :=
      match Core.typeTypeOrConstraint res_ty with
      | BasicTypes.TypeLike => iMPOSSIBLE_ERROR_ID
      | BasicTypes.ConstraintLike => iMPOSSIBLE_CONSTRAINT_ERROR_ID
      end in
    mkRuntimeErrorApp err_id res_ty str.

#[global] Definition mkAbsentErrorApp
   : AxiomatizedTypes.Type_ -> GHC.Base.String -> Core.CoreExpr :=
  fun res_ty err_msg =>
    let err_string := Core.Lit (Literal.mkLitString err_msg) in
    let err_id :=
      match Core.typeTypeOrConstraint res_ty with
      | BasicTypes.TypeLike => aBSENT_ERROR_ID
      | BasicTypes.ConstraintLike => aBSENT_CONSTRAINT_ERROR_ID
      end in
    Core.mkApps (Core.Mk_Var err_id) (cons (Core.Mk_Type res_ty) (cons err_string
                                                                       nil)).

#[global] Definition absentErrorName : Name.Name :=
  TysWiredIn.mkWiredInIdName PrelNames.gHC_PRIM_PANIC (GHC.Data.FastString.fsLit
                                                       (GHC.Base.hs_string__ "absentError")) PrelNames.absentErrorIdKey
  aBSENT_ERROR_ID.

#[global] Definition absentConstraintErrorName : Name.Name :=
  TysWiredIn.mkWiredInIdName PrelNames.gHC_PRIM_PANIC (GHC.Data.FastString.fsLit
                                                       (GHC.Base.hs_string__ "absentConstraintError"))
  PrelNames.absentConstraintErrorIdKey aBSENT_CONSTRAINT_ERROR_ID.

Axiom mkRuntimeErrorId : BasicTypes.TypeOrConstraint -> Name.Name -> Core.Id.

#[global] Definition mk_runtime_error_id
   : Name.Name -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun name ty =>
    Id.mkVanillaGlobalWithInfo name ty (divergingIdInfo (cons Core.evalDmd nil)).

#[global] Definition mkRuntimeErrorTy
   : BasicTypes.TypeOrConstraint -> AxiomatizedTypes.Type_ :=
  fun torc =>
    let kind :=
      match torc with
      | BasicTypes.TypeLike => Core.mkTYPEapp GHC.Builtin.Types.Prim.runtimeRep1Ty
      | BasicTypes.ConstraintLike =>
          Core.mkCONSTRAINTapp GHC.Builtin.Types.Prim.runtimeRep1Ty
      end in
    match GHC.Builtin.Types.Prim.mkTemplateTyVars (cons kind nil) with
    | cons tyvar _ =>
        Core.mkSpecForAllTys (cons GHC.Builtin.Types.Prim.runtimeRep1TyVar (cons tyvar
                                                                                 nil)) (Core.mkFunctionType Core.ManyTy
                                                                                                            GHC.Builtin.Types.Prim.addrPrimTy
                                                                                                            (Core.mkTyVarTy
                                                                                                             tyvar))
    | _ => GHC.Err.patternFailure
    end.

(* External variables:
     None Some Type andb bool cons list nat negb nil op_zt__ option pair tt
     AxiomatizedTypes.Type_ BasicTypes.ConstraintLike BasicTypes.TypeLike
     BasicTypes.TypeOrConstraint Constants.mAX_TUPLE_SIZE Coq.Init.Datatypes.app
     Coq.Lists.List.flat_map Coq.Lists.List.length Core.Alt Core.AltCon Core.App
     Core.Case Core.CoreAlt Core.CoreBind Core.CoreBndr Core.CoreExpr Core.DataAlt
     Core.DataCon Core.Demand Core.Id Core.IdInfo Core.Let Core.Lit Core.ManyTy
     Core.Mk_Coercion Core.Mk_Type Core.Mk_Var Core.Mult Core.NoCafRefs Core.NonRec
     Core.OneTy Core.Rec Core.Scaled Core.Var Core.botDiv Core.dataConWorkId
     Core.evalDmd Core.funResultTy Core.getRuntimeRep Core.isCoVarType Core.isFunTy
     Core.linear Core.mkApps Core.mkCONSTRAINTapp Core.mkCharLit Core.mkClosedDmdSig
     Core.mkConApp Core.mkFunctionType Core.mkLams Core.mkSpecForAllTys
     Core.mkTYPEapp Core.mkTyApps Core.mkTyVarTy Core.piResultTy Core.sORTKind_maybe
     Core.setArityInfo Core.setCafInfo Core.setCprSigInfo Core.setDmdSigInfo
     Core.tcIsLiftedTypeKind Core.typeKind Core.typeTypeOrConstraint
     Core.vanillaIdInfo CoreUtils.bindNonRec CoreUtils.exprType
     CoreUtils.mkSingleAltCase Data.Foldable.all Data.Foldable.elem
     Data.Foldable.foldl' Data.Foldable.foldr Data.Functor.op_zlzdzg__ Data.Tuple.fst
     Data.Tuple.snd GHC.Base.Applicative GHC.Base.Monad GHC.Base.String GHC.Base.map
     GHC.Base.op_z2218U__ GHC.Base.op_zgze__ GHC.Base.op_zgzgze__ GHC.Base.op_zlze__
     GHC.Base.op_zlztzg__ GHC.Base.ord GHC.Base.pure GHC.Base.return_
     GHC.Builtin.Types.Prim.addrPrimTy GHC.Builtin.Types.Prim.alphaTyVar
     GHC.Builtin.Types.Prim.mkTemplateTyVars GHC.Builtin.Types.Prim.runtimeRep1Ty
     GHC.Builtin.Types.Prim.runtimeRep1TyVar GHC.Char.Char
     GHC.Core.TyCo.Compare.eqType GHC.Core.TyCo.FVs.noFreeVarsOfType
     GHC.Data.FastString.FastString GHC.Data.FastString.bytesFS
     GHC.Data.FastString.fsLit GHC.Data.FastString.nullFS
     GHC.Data.FastString.unpackFS GHC.Err.patternFailure GHC.List.splitAt
     GHC.Num.fromInteger GHC.Num.Integer.Integer GHC.Types.Cpr.botCpr
     GHC.Types.Cpr.mkCprSig HsSyn.Boxed HsSyn.Boxity HsSyn.Unboxed
     HsToCoq.Err.Build_Default HsToCoq.Err.Default HsToCoq.Err.default Id.idType
     Id.mkLocalIdOrCoVar Id.mkSysLocal Id.mkTemplateLocals Id.mkVanillaGlobalWithInfo
     Literal.LitRubbish Literal.LitString Literal.mkLitIntUnchecked
     Literal.mkLitString Name.Name Panic.assertPpr Panic.pprPanic Panic.someSDoc
     Platform.Platform PrelNames.absentConstraintErrorIdKey
     PrelNames.absentErrorIdKey PrelNames.absentSumFieldErrorIdKey
     PrelNames.gHC_PRIM_PANIC PrelNames.impossibleConstraintErrorIdKey
     PrelNames.impossibleErrorIdKey PrelNames.noMethodBindingErrorIdKey
     PrelNames.nonExhaustiveGuardsErrorIdKey PrelNames.patErrorIdKey
     PrelNames.recConErrorIdKey PrelNames.recSelErrorIdKey PrelNames.typeErrorIdKey
     PrelNames.unpackCStringName PrelNames.unpackCStringUtf8Name
     PrelNames.wildCardName TysWiredIn.BI_Box TysWiredIn.BI_NoBoxAvailable
     TysWiredIn.BI_NoBoxNeeded TysWiredIn.boolTy TysWiredIn.boxingDataCon
     TysWiredIn.charDataCon TysWiredIn.charTy TysWiredIn.consDataCon
     TysWiredIn.falseDataCon TysWiredIn.intDataCon TysWiredIn.justDataCon
     TysWiredIn.mkBoxedTupleTy TysWiredIn.mkWiredInIdName TysWiredIn.nilDataCon
     TysWiredIn.nothingDataCon TysWiredIn.sumDataCon TysWiredIn.trueDataCon
     TysWiredIn.tupleDataCon TysWiredIn.unitDataConId UniqSupply.MonadUnique
     UniqSupply.UniqSupply UniqSupply.getUniqueSupplyM UniqSupply.takeUniqFromSupply
     Unique.Unique Util.HasDebugCallStack Util.zipEqual
*)
