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
Require Data.ByteString.Internal.Type.
Require Data.Foldable.
Require Data.Function.
Require Data.Maybe.
Require Data.OldList.
Require Data.Set.Internal.
Require Data.Tuple.
Require Datatypes.
Require GHC.Base.
Require GHC.Core.FamInstEnv.
Require GHC.Core.Reduction.
Require GHC.Core.TyCo.Compare.
Require GHC.Core.TyCo.FVs.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Types.Tickish.
Require GHC.Utils.Trace.
Require HsSyn.
Require HsToCoq.DeferredFix.
Require Id.
Require Literal.
Require Maybes.
Require Name.
Require OrdList.
Require Panic.
Require PrelNames.
Require PrimOp.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

#[global] Definition CheapAppFun :=
  (Core.Id -> BasicTypes.Arity -> bool)%type.

(* Converted value declarations: *)

Axiom exprType : forall `{Util.HasDebugCallStack},
                 Core.CoreExpr -> AxiomatizedTypes.Type_.

Axiom coreAltType : Core.CoreAlt -> AxiomatizedTypes.Type_.

Axiom coreAltsType : list Core.CoreAlt -> AxiomatizedTypes.Type_.

#[global] Definition mkLamType `{Util.HasDebugCallStack}
   : Core.Var -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ :=
  fun v body_ty =>
    if Core.isTyVar v : bool
    then Core.mkForAllTy (Core.Bndr v Core.coreTyLamForAllTyFlag) body_ty else
    if andb (Core.isCoVar v) (Core.elemVarSet v (GHC.Core.TyCo.FVs.tyCoVarsOfType
                                               body_ty)) : bool
    then Core.mkForAllTy (Core.Bndr v Core.coreTyLamForAllTyFlag) body_ty else
    Core.mkFunctionType (Core.varMult v) (Core.varType v) body_ty.

#[global] Definition mkLamTypes
   : list Core.Var -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ :=
  fun vs ty => Data.Foldable.foldr mkLamType ty vs.

Axiom applyTypeToArgs : forall `{Util.HasDebugCallStack},
                        GHC.Base.String ->
                        AxiomatizedTypes.Type_ -> list Core.CoreExpr -> AxiomatizedTypes.Type_.

#[global] Definition mkCastMCo
   : Core.CoreExpr -> Core.MCoercionR -> Core.CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | e, Core.MRefl => e
    | e, Core.MCo co => Core.Cast e co
    end.

#[global] Definition mkPiMCo : Core.Var -> Core.MCoercionR -> Core.MCoercionR :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Core.MRefl => Core.MRefl
    | v, Core.MCo co => Core.MCo (Core.mkPiCo HsSyn.Representational v co)
    end.

Fixpoint mkCast `{Util.HasDebugCallStack} (arg_0__ : Core.CoreExpr) (arg_1__
                  : Core.CoercionR) : Core.CoreExpr
  := match arg_0__, arg_1__ with
     | e, co =>
         if Panic.assertPpr (Core.coercionRole co GHC.Base.== HsSyn.Representational)
                            (GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend
                                                                                   (GHC.Base.mappend (Datatypes.id
                                                                                                      (GHC.Base.hs_string__
                                                                                                       "coercion"))
                                                                                                     Panic.someSDoc)
                                                                                   (Datatypes.id (GHC.Base.hs_string__
                                                                                                  "passed to mkCast")))
                                                                                  Panic.someSDoc) (Datatypes.id
                                                                 (GHC.Base.hs_string__ "has wrong role")))
                                              Panic.someSDoc) (Core.isReflCo co) : bool
         then e else
         let j_7__ :=
           match arg_0__, arg_1__ with
           | Core.Cast expr co2, co =>
               GHC.Utils.Trace.warnPprTrace (let to_ty2 := Core.coercionRKind co2 in
                                             let from_ty := Core.coercionLKind co in
                                             negb (GHC.Core.TyCo.Compare.eqType from_ty to_ty2)) (GHC.Base.hs_string__
                                             "mkCast") (Panic.someSDoc) (mkCast expr (Core.mkTransCo co2 co))
           | expr, co =>
               let from_ty := Core.coercionLKind co in
               GHC.Utils.Trace.warnPprTrace (negb (GHC.Core.TyCo.Compare.eqType from_ty
                                                                                (exprType expr))) (GHC.Base.hs_string__
                                             "Trying to coerce") (GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend
                                                                                                      (Datatypes.id
                                                                                                       (GHC.Base.hs_string__
                                                                                                        "("))
                                                                                                      Panic.someSDoc)
                                                                                                     Panic.someSDoc)
                                                                                   (Datatypes.id (GHC.Base.hs_string__
                                                                                                  ")"))) (Core.Cast expr
                                                                                                                    co)
           end in
         match arg_0__, arg_1__ with
         | Core.Mk_Coercion e_co, co =>
             if Core.isCoVarType (Core.coercionRKind co) : bool
             then Core.Mk_Coercion (Core.mkCoCast e_co co) else
             j_7__
         | _, _ => j_7__
         end
     end.

(* Skipping definition `CoreUtils.mkTick' *)

(* Skipping definition `CoreUtils.mkTicks' *)

#[global] Definition isSaturatedConApp : Core.CoreExpr -> bool :=
  fun e =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | Core.App f a, as_ => go f (cons a as_)
         | Core.Mk_Var fun_, args =>
             andb (Id.isConLikeId fun_) (Id.idArity fun_ GHC.Base.== Core.valArgCount args)
         | Core.Cast f _, as_ => go f as_
         | _, _ => false
         end in
    go e nil.

(* Skipping definition `CoreUtils.mkTickNoHNF' *)

(* Skipping definition `CoreUtils.tickHNFArgs' *)

(* Skipping definition `CoreUtils.stripTicksTop' *)

#[global] Definition stripTicksTopE {b : Type}
   : (GHC.Types.Tickish.CoreTickish -> bool) -> Core.Expr b -> Core.Expr b :=
  fun p => let go := fun '(other) => other in go.

(* Skipping definition `CoreUtils.stripTicksTopT' *)

#[global] Definition stripTicksE {b : Type}
   : (GHC.Types.Tickish.CoreTickish -> bool) -> Core.Expr b -> Core.Expr b :=
  fun p expr =>
    let go :=
      fix go arg_0__
        := let go_a (arg_14__ : Core.Alt b) : Core.Alt b :=
             let 'Core.Alt c bs e := arg_14__ in
             Core.Alt c bs (go e) in
           match arg_0__ with
           | Core.App e a => Core.App (go e) (go a)
           | Core.Lam b e => Core.Lam b (go e)
           | Core.Let b e => Core.Let (go_bs b) (go e)
           | Core.Case e b t as_ => Core.Case (go e) b t (GHC.Base.map go_a as_)
           | Core.Cast e c => Core.Cast (go e) c
           | other => other
           end
      with go_bs arg_7__
        := let go_b (arg_11__ : b * Core.Expr b) : b * Core.Expr b :=
             let 'pair b e := arg_11__ in
             pair b (go e) in
           match arg_7__ with
           | Core.NonRec b e => Core.NonRec b (go e)
           | Core.Rec bs => Core.Rec (GHC.Base.map go_b bs)
           end for go in
    let go_bs :=
      fix go arg_0__
        := let go_a (arg_14__ : Core.Alt b) : Core.Alt b :=
             let 'Core.Alt c bs e := arg_14__ in
             Core.Alt c bs (go e) in
           match arg_0__ with
           | Core.App e a => Core.App (go e) (go a)
           | Core.Lam b e => Core.Lam b (go e)
           | Core.Let b e => Core.Let (go_bs b) (go e)
           | Core.Case e b t as_ => Core.Case (go e) b t (GHC.Base.map go_a as_)
           | Core.Cast e c => Core.Cast (go e) c
           | other => other
           end
      with go_bs arg_7__
        := let go_b (arg_11__ : b * Core.Expr b) : b * Core.Expr b :=
             let 'pair b e := arg_11__ in
             pair b (go e) in
           match arg_7__ with
           | Core.NonRec b e => Core.NonRec b (go e)
           | Core.Rec bs => Core.Rec (GHC.Base.map go_b bs)
           end for go_bs in
    let go_b : b * Core.Expr b -> b * Core.Expr b :=
      fun '(pair b e) => pair b (go e) in
    let go_a : Core.Alt b -> Core.Alt b :=
      fun '(Core.Alt c bs e) => Core.Alt c bs (go e) in
    go expr.

#[global] Definition stripTicksT {b : Type}
   : (GHC.Types.Tickish.CoreTickish -> bool) ->
     Core.Expr b -> list GHC.Types.Tickish.CoreTickish :=
  fun p expr =>
    let go :=
      fix go arg_0__
        := let go_a (arg_14__ : Core.Alt b) : OrdList.OrdList (Core.Tickish Core.Id) :=
             let 'Core.Alt _ _ e := arg_14__ in
             go e in
           match arg_0__ with
           | Core.App e a => OrdList.appOL (go e) (go a)
           | Core.Lam _ e => go e
           | Core.Let b e => OrdList.appOL (go_bs b) (go e)
           | Core.Case e _ _ as_ =>
               OrdList.appOL (go e) (OrdList.concatOL (GHC.Base.map go_a as_))
           | Core.Cast e _ => go e
           | _ => OrdList.nilOL
           end
      with go_bs arg_7__
        := let go_b (arg_11__ : b * Core.Expr b)
            : OrdList.OrdList (Core.Tickish Core.Id) :=
             let 'pair _ e := arg_11__ in
             go e in
           match arg_7__ with
           | Core.NonRec _ e => go e
           | Core.Rec bs => OrdList.concatOL (GHC.Base.map go_b bs)
           end for go in
    let go_bs :=
      fix go arg_0__
        := let go_a (arg_14__ : Core.Alt b) : OrdList.OrdList (Core.Tickish Core.Id) :=
             let 'Core.Alt _ _ e := arg_14__ in
             go e in
           match arg_0__ with
           | Core.App e a => OrdList.appOL (go e) (go a)
           | Core.Lam _ e => go e
           | Core.Let b e => OrdList.appOL (go_bs b) (go e)
           | Core.Case e _ _ as_ =>
               OrdList.appOL (go e) (OrdList.concatOL (GHC.Base.map go_a as_))
           | Core.Cast e _ => go e
           | _ => OrdList.nilOL
           end
      with go_bs arg_7__
        := let go_b (arg_11__ : b * Core.Expr b)
            : OrdList.OrdList (Core.Tickish Core.Id) :=
             let 'pair _ e := arg_11__ in
             go e in
           match arg_7__ with
           | Core.NonRec _ e => go e
           | Core.Rec bs => OrdList.concatOL (GHC.Base.map go_b bs)
           end for go_bs in
    let go_b : b * Core.Expr b -> OrdList.OrdList (Core.Tickish Core.Id) :=
      fun '(pair _ e) => go e in
    let go_a : Core.Alt b -> OrdList.OrdList (Core.Tickish Core.Id) :=
      fun '(Core.Alt _ _ e) => go e in
    OrdList.fromOL (go expr).

Axiom bindNonRec : forall `{Util.HasDebugCallStack},
                   Core.Id -> Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr.

Axiom exprOkForSpeculation : Core.CoreExpr -> bool.

#[global] Definition needsCaseBindingL
   : BasicTypes.Levity -> Core.CoreExpr -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | BasicTypes.Lifted, _rhs => false
    | BasicTypes.Unlifted, rhs => negb (exprOkForSpeculation rhs)
    end.

#[global] Definition needsCaseBinding `{Util.HasDebugCallStack}
   : AxiomatizedTypes.Type_ -> Core.CoreExpr -> bool :=
  fun ty rhs => needsCaseBindingL (Core.typeLevity ty) rhs.

#[global] Definition mkAltExpr
   : Core.AltCon ->
     list Core.CoreBndr -> list AxiomatizedTypes.Type_ -> Core.CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Core.DataAlt con, args, inst_tys =>
        Core.mkConApp con (Coq.Init.Datatypes.app (GHC.Base.map Core.Mk_Type inst_tys)
                                                  (Core.varsToCoreExprs args))
    | Core.LitAlt lit, nil, nil => Core.Lit lit
    | Core.LitAlt _, _, _ => Panic.panic (GHC.Base.hs_string__ "mkAltExpr LitAlt")
    | Core.DEFAULT, _, _ => Panic.panic (GHC.Base.hs_string__ "mkAltExpr DEFAULT")
    end.

#[global] Definition mkDefaultCase
   : Core.CoreExpr -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun scrut case_bndr body =>
    Core.Case scrut case_bndr (exprType body) (cons (Core.Alt Core.DEFAULT nil body)
                                                    nil).

#[global] Definition mkSingleAltCase
   : Core.CoreExpr ->
     Core.Id -> Core.AltCon -> list Core.Var -> Core.CoreExpr -> Core.CoreExpr :=
  fun scrut case_bndr con bndrs body =>
    let body_ty := exprType body in
    let case_ty :=
      match GHC.Core.TyCo.FVs.occCheckExpand bndrs body_ty with
      | Some body_ty' => body_ty'
      | _ => Panic.pprPanic (GHC.Base.hs_string__ "mkSingleAltCase") (Panic.someSDoc)
      end in
    Core.Case scrut case_bndr case_ty (cons (Core.Alt con bndrs body) nil).

#[global] Definition findDefault {b : Type}
   : list (Core.Alt b) -> (list (Core.Alt b) * option (Core.Expr b))%type :=
  fun arg_0__ =>
    match arg_0__ with
    | cons (Core.Alt Core.DEFAULT args rhs) alts => pair alts (Some rhs)
    | alts => pair alts None
    end.

#[global] Definition addDefault {b : Type}
   : list (Core.Alt b) -> option (Core.Expr b) -> list (Core.Alt b) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | alts, None => alts
    | alts, Some rhs => cons (Core.Alt Core.DEFAULT nil rhs) alts
    end.

#[global] Definition isDefaultAlt {b : Type} : Core.Alt b -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.Alt Core.DEFAULT _ _ => true
    | _ => false
    end.

#[global] Definition findAlt {b : Type}
   : Core.AltCon -> list (Core.Alt b) -> option (Core.Alt b) :=
  fun con alts =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | nil, deflt => deflt
         | cons (Core.Alt con1 _ _ as alt) alts, deflt =>
             match Core.cmpAltCon con con1 with
             | Lt => deflt
             | Eq => Some alt
             | Gt => go alts deflt
             end
         end in
    match alts with
    | cons (Core.Alt Core.DEFAULT _ _ as deflt) alts => go alts (Some deflt)
    | _ => go alts None
    end.

#[global] Definition mergeAlts {a : Type}
   : list (Core.Alt a) -> list (Core.Alt a) -> list (Core.Alt a) :=
  HsToCoq.DeferredFix.deferredFix1 (fun mergeAlts
                                    (arg_0__ arg_1__ : list (Core.Alt a)) =>
                                      match arg_0__, arg_1__ with
                                      | nil, as2 => as2
                                      | as1, nil => as1
                                      | cons a1 as1, cons a2 as2 =>
                                          match Core.cmpAlt a1 a2 with
                                          | Lt => cons a1 (mergeAlts as1 (cons a2 as2))
                                          | Eq => cons a1 (mergeAlts as1 as2)
                                          | Gt => cons a2 (mergeAlts (cons a1 as1) as2)
                                          end
                                      end).

#[global] Definition trimConArgs
   : Core.AltCon -> list Core.CoreArg -> list Core.CoreArg :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Core.DEFAULT, args => nil
    | Core.LitAlt _, args => nil
    | Core.DataAlt dc, args => Util.dropList (Core.dataConUnivTyVars dc) args
    end.

#[global] Definition filterAlts {b : Type}
   : Core.TyCon ->
     list AxiomatizedTypes.Type_ ->
     list Core.AltCon ->
     list (Core.Alt b) -> (list Core.AltCon * list (Core.Alt b))%type :=
  fun _tycon inst_tys imposs_cons alts =>
    let imposs_cons_set := Data.Set.Internal.fromList imposs_cons in
    let impossible_alt {b} : list AxiomatizedTypes.Type_ -> Core.Alt b -> bool :=
      fun arg_1__ arg_2__ =>
        match arg_1__, arg_2__ with
        | _, Core.Alt con _ _ =>
            if Data.Set.Internal.member con imposs_cons_set : bool then true else
            match arg_1__, arg_2__ with
            | inst_tys, Core.Alt (Core.DataAlt con) _ _ =>
                Core.dataConCannotMatch inst_tys con
            | _, _ => false
            end
        end in
    let 'pair alts_wo_default maybe_deflt := findDefault alts in
    let alt_cons :=
      let cont_8__ arg_9__ := let 'Core.Alt con _ _ := arg_9__ in cons con nil in
      Coq.Lists.List.flat_map cont_8__ alts_wo_default in
    let imposs_deflt_cons :=
      Coq.Init.Datatypes.app imposs_cons (Util.filterOut (GHC.Prim.rightSection
                                                          Data.Set.Internal.member imposs_cons_set) alt_cons) in
    let trimmed_alts := Util.filterOut (impossible_alt inst_tys) alts_wo_default in
    Util.seqList imposs_deflt_cons (pair imposs_deflt_cons (addDefault trimmed_alts
                                          maybe_deflt)).

Axiom refineDefaultAlt : list Unique.Unique ->
                         Core.Mult ->
                         Core.TyCon ->
                         list AxiomatizedTypes.Type_ ->
                         list Core.AltCon -> list Core.CoreAlt -> (bool * list Core.CoreAlt)%type.

Axiom combineIdenticalAlts : list Core.AltCon ->
                             list Core.CoreAlt -> (bool * list Core.AltCon * list Core.CoreAlt)%type.

#[global] Definition scaleAltsBy
   : Core.Mult -> list Core.CoreAlt -> list Core.CoreAlt :=
  fun w alts =>
    let scaleBndr : Core.CoreBndr -> Core.CoreBndr := fun b => Id.scaleVarBy w b in
    let scaleAlt : Core.CoreAlt -> Core.CoreAlt :=
      fun '(Core.Alt con bndrs rhs) =>
        Core.Alt con (GHC.Base.map scaleBndr bndrs) rhs in
    GHC.Base.map scaleAlt alts.

#[global] Definition isUnsafeEqualityCase
   : Core.CoreExpr -> Core.Id -> list Core.CoreAlt -> option Core.CoreExpr :=
  fun scrut bndr alts =>
    match alts with
    | cons (Core.Alt ac _ rhs) nil =>
        match ac with
        | Core.DataAlt dc =>
            if andb (Unique.hasKey dc PrelNames.unsafeReflDataConKey) (Id.isDeadBinder
                     bndr) : bool
            then match scrut with
                 | Core.App (Core.App (Core.App (Core.Mk_Var v) _) _) _ =>
                     if Unique.hasKey v PrelNames.unsafeEqualityProofIdKey : bool then Some rhs else
                     None
                 | _ => None
                 end else
            None
        | _ => None
        end
    | _ => None
    end.

#[global] Definition trivial_expr_fold {r : Type}
   : (Core.Id -> r) -> (Literal.Literal -> r) -> r -> r -> Core.CoreExpr -> r :=
  fun k_id k_lit k_triv k_not_triv =>
    let fix go arg_0__
      := match arg_0__ with
         | Core.Mk_Var v => k_id v
         | Core.Lit l => if Literal.litIsTrivial l : bool then k_lit l else k_not_triv
         | Core.Mk_Type _ => k_triv
         | Core.Mk_Coercion _ => k_triv
         | Core.App f t => if negb (Core.isRuntimeArg t) : bool then go f else k_not_triv
         | Core.Lam b e => if negb (Core.isRuntimeVar b) : bool then go e else k_not_triv
         | Core.Cast e _ => go e
         | Core.Case e b _ as_ =>
             if Data.Foldable.null as_ : bool then go e else
             match isUnsafeEqualityCase e b as_ with
             | Some rhs => go rhs
             | _ => k_not_triv
             end
         | _ => k_not_triv
         end in
    go.

#[global] Definition exprIsTrivial : Core.CoreExpr -> bool :=
  fun e =>
    trivial_expr_fold (GHC.Base.const true) (GHC.Base.const true) true false e.

#[global] Definition getIdFromTrivialExpr `{Util.HasDebugCallStack}
   : Core.CoreExpr -> Core.Id :=
  fun e =>
    let panic :=
      Panic.pprPanic (GHC.Base.hs_string__ "getIdFromTrivialExpr") (Panic.someSDoc) in
    trivial_expr_fold GHC.Base.id (GHC.Base.const panic) panic panic e.

#[global] Definition getIdFromTrivialExpr_maybe
   : Core.CoreExpr -> option Core.Id :=
  fun e => trivial_expr_fold Some (GHC.Base.const None) None None e.

#[global] Definition dupAppSize : nat :=
  #8.

#[global] Definition exprIsDupable
   : Platform.Platform -> Core.CoreExpr -> bool :=
  fun platform e =>
    let decrement : nat -> option nat :=
      fun arg_0__ =>
        let 'num_1__ := arg_0__ in
        if num_1__ GHC.Base.== #0 : bool then None else
        let 'n := arg_0__ in
        Some (n GHC.Num.- #1) in
    let go : nat -> Core.CoreExpr -> option nat :=
      fix go (arg_6__ : nat) (arg_7__ : Core.CoreExpr) : option nat
        := match arg_6__, arg_7__ with
           | n, Core.Mk_Type _ => Some n
           | n, Core.Mk_Coercion _ => Some n
           | n, Core.Mk_Var _ => decrement n
           | n, Core.Cast e _ => go n e
           | n, Core.App f a => match go n a with | Some n' => go n' f | _ => None end
           | n, Core.Lit lit =>
               if Literal.litIsDupable platform lit : bool then decrement n else
               None
           | _, _ => None
           end in
    Data.Maybe.isJust (go dupAppSize e).

#[global] Definition exprIsCheapX : CheapAppFun -> Core.CoreExpr -> bool :=
  fun ok_app e =>
    let fix go arg_1__ arg_2__
      := let ok e := go #0 e in
         match arg_1__, arg_2__ with
         | n, Core.Mk_Var v => ok_app v n
         | _, Core.Lit _ => true
         | _, Core.Mk_Type _ => true
         | _, Core.Mk_Coercion _ => true
         | n, Core.Cast e _ => go n e
         | n, Core.Case scrut _ _ alts =>
             andb (ok scrut) (Data.Foldable.and (let cont_5__ arg_6__ :=
                                                   let 'Core.Alt _ _ rhs := arg_6__ in
                                                   cons (go n rhs) nil in
                                                 Coq.Lists.List.flat_map cont_5__ alts))
         | n, Core.Lam x e =>
             if Core.isRuntimeVar x : bool
             then orb (n GHC.Base.== #0) (go (n GHC.Num.- #1) e) else
             go n e
         | n, Core.App f e =>
             if Core.isRuntimeArg e : bool then andb (go (n GHC.Num.+ #1) f) (ok e) else
             go n f
         | n, Core.Let (Core.NonRec _ r) e => andb (go n e) (ok r)
         | n, Core.Let (Core.Rec prs) e =>
             andb (go n e) (Data.Foldable.all (ok GHC.Base.∘ Data.Tuple.snd) prs)
         end in
    let ok := fun e => go #0 e in ok e.

#[global] Definition isWorkFreeApp : CheapAppFun :=
  fun fn n_val_args =>
    if n_val_args GHC.Base.== #0 : bool then true else
    if n_val_args GHC.Base.< Id.idArity fn : bool then true else
    match Core.idDetails fn with
    | Core.DataConWorkId _ => true
    | Core.PrimOpId op _ => PrimOp.primOpIsWorkFree op
    | _ => false
    end.

#[global] Definition exprIsWorkFree : Core.CoreExpr -> bool :=
  fun e => exprIsCheapX isWorkFreeApp e.

Axiom isCheapApp : CheapAppFun.

#[global] Definition exprIsCheap : Core.CoreExpr -> bool :=
  fun e => exprIsCheapX isCheapApp e.

Axiom isExpandableApp : CheapAppFun.

#[global] Definition exprIsExpandable : Core.CoreExpr -> bool :=
  fun e =>
    let ok :=
      fix go arg_1__ arg_2__
        := match arg_1__, arg_2__ with
           | n, Core.Mk_Var v => isExpandableApp v n
           | _, Core.Lit _ => true
           | _, Core.Mk_Type _ => true
           | _, Core.Mk_Coercion _ => true
           | n, Core.Cast e _ => go n e
           | n, Core.Lam x e =>
               if Core.isRuntimeVar x : bool
               then orb (n GHC.Base.== #0) (go (n GHC.Num.- #1) e) else
               go n e
           | n, Core.App f e =>
               if Core.isRuntimeArg e : bool then andb (go (n GHC.Num.+ #1) f) (ok e) else
               go n f
           | _, Core.Case _ _ _ _ => false
           | _, Core.Let _ _ => false
           end
      with ok e
        := go #0 e for ok in
    let go :=
      fix go arg_1__ arg_2__
        := match arg_1__, arg_2__ with
           | n, Core.Mk_Var v => isExpandableApp v n
           | _, Core.Lit _ => true
           | _, Core.Mk_Type _ => true
           | _, Core.Mk_Coercion _ => true
           | n, Core.Cast e _ => go n e
           | n, Core.Lam x e =>
               if Core.isRuntimeVar x : bool
               then orb (n GHC.Base.== #0) (go (n GHC.Num.- #1) e) else
               go n e
           | n, Core.App f e =>
               if Core.isRuntimeArg e : bool then andb (go (n GHC.Num.+ #1) f) (ok e) else
               go n f
           | _, Core.Case _ _ _ _ => false
           | _, Core.Let _ _ => false
           end
      with ok e
        := go #0 e for go in
    ok e.

Axiom expr_ok : (Core.Id -> bool) ->
                (AxiomatizedTypes.PrimOp -> bool) -> Core.CoreExpr -> bool.

#[global] Definition fun_always_ok : Core.Id -> bool :=
  fun arg_0__ => true.

#[global] Definition exprOkToDiscard : Core.CoreExpr -> bool :=
  expr_ok fun_always_ok PrimOp.primOpOkToDiscard.

#[global] Definition exprOkForSpecEval
   : (Core.Id -> bool) -> Core.CoreExpr -> bool :=
  fun fun_ok => expr_ok fun_ok PrimOp.primOpOkForSpeculation.

Axiom app_ok : (Core.Id -> bool) ->
               (AxiomatizedTypes.PrimOp -> bool) -> Core.Id -> list Core.CoreExpr -> bool.

#[global] Definition altsAreExhaustive {b : Type} : list (Core.Alt b) -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => true
    | cons (Core.Alt con1 _ _) alts =>
        match con1 with
        | Core.DEFAULT => true
        | Core.LitAlt _ => false
        | Core.DataAlt c =>
            Util.lengthIs alts (Core.tyConFamilySize (Core.dataConTyCon c) GHC.Num.- #1)
        end
    end.

#[global] Definition etaExpansionTick {pass : GHC.Types.Tickish.TickishPass}
   : Core.Id -> GHC.Types.Tickish.GenTickish pass -> bool :=
  fun id t =>
    andb (Id.hasNoBinding id) (orb (GHC.Types.Tickish.tickishFloatable t)
                                   (GHC.Types.Tickish.isProfTick t)).

#[global] Definition exprIsHNFlike `{Util.HasDebugCallStack}
   : (Core.Var -> bool) -> (Core.Unfolding -> bool) -> Core.CoreExpr -> bool :=
  fun is_con is_con_unf =>
    let id_app_is_value :=
      fun id n_val_args => orb (is_con id) (Id.idArity id GHC.Base.> n_val_args) in
    let app_is_value : Core.CoreExpr -> nat -> bool :=
      fix app_is_value (arg_1__ : Core.CoreExpr) (arg_2__ : nat) : bool
        := match arg_1__, arg_2__ with
           | Core.Mk_Var f, nva => id_app_is_value f nva
           | Core.Cast f _, nva => app_is_value f nva
           | Core.App f a, nva =>
               if Core.isValArg a : bool
               then andb (app_is_value f (nva GHC.Num.+ #1)) (negb (needsCaseBinding (exprType
                                                                                      a) a)) else
               app_is_value f nva
           | _, _ => false
           end in
    let fix is_hnf_like arg_8__
      := match arg_8__ with
         | Core.Mk_Var v =>
             orb (id_app_is_value v #0) (orb (is_con_unf (Id.idUnfolding v))
                                             (Core.definitelyUnliftedType (Id.idType v)))
         | Core.Lit l => negb (Literal.isLitRubbish l)
         | Core.Mk_Type _ => true
         | Core.Mk_Coercion _ => true
         | Core.Lam b e => orb (Core.isRuntimeVar b) (is_hnf_like e)
         | Core.Cast e _ => is_hnf_like e
         | Core.App e a =>
             if Core.isValArg a : bool then app_is_value e #1 else
             is_hnf_like e
         | Core.Let _ e => is_hnf_like e
         | Core.Case e b _ as_ =>
             match isUnsafeEqualityCase e b as_ with
             | Some rhs => is_hnf_like rhs
             | _ => false
             end
         end in
    is_hnf_like.

#[global] Definition exprIsHNF : Core.CoreExpr -> bool :=
  exprIsHNFlike Id.isDataConWorkId Core.isEvaldUnfolding.

#[global] Definition exprIsConLike : Core.CoreExpr -> bool :=
  exprIsHNFlike Id.isConLikeId Core.isConLikeUnfolding.

#[global] Definition exprIsTickedString_maybe
   : Core.CoreExpr -> option Data.ByteString.Internal.Type.ByteString :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.Lit (Literal.LitString bs) => Some bs
    | _ => None
    end.

#[global] Definition exprIsTickedString : Core.CoreExpr -> bool :=
  Data.Maybe.isJust GHC.Base.∘ exprIsTickedString_maybe.

#[global] Definition exprIsTopLevelBindable
   : Core.CoreExpr -> AxiomatizedTypes.Type_ -> bool :=
  fun expr ty =>
    orb (negb (Core.mightBeUnliftedType ty)) (exprIsTickedString expr).

Axiom dataConRepInstPat : list Unique.Unique ->
                          Core.Mult ->
                          Core.DataCon ->
                          list AxiomatizedTypes.Type_ -> (list Core.TyCoVar * list Core.Id)%type.

Axiom dataConRepFSInstPat : list GHC.Data.FastString.FastString ->
                            list Unique.Unique ->
                            Core.Mult ->
                            Core.DataCon ->
                            list AxiomatizedTypes.Type_ -> (list Core.TyCoVar * list Core.Id)%type.

Axiom dataConInstPat : list GHC.Data.FastString.FastString ->
                       list Unique.Unique ->
                       Core.Mult ->
                       Core.DataCon ->
                       list AxiomatizedTypes.Type_ -> (list Core.TyCoVar * list Core.Id)%type.

Axiom cheapEqExpr' : forall {b : Type},
                     (GHC.Types.Tickish.CoreTickish -> bool) -> Core.Expr b -> Core.Expr b -> bool.

#[global] Definition cheapEqExpr {b : Type}
   : Core.Expr b -> Core.Expr b -> bool :=
  cheapEqExpr' (GHC.Base.const false).

#[global] Definition eqTickish
   : Core.RnEnv2 ->
     GHC.Types.Tickish.CoreTickish -> GHC.Types.Tickish.CoreTickish -> bool :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | env
    , GHC.Types.Tickish.Breakpoint lext lid lids lmod
    , GHC.Types.Tickish.Breakpoint rext rid rids rmod =>
        andb (lid GHC.Base.== rid) (andb (GHC.Base.map (Core.rnOccL env) lids
                                          GHC.Base.==
                                          GHC.Base.map (Core.rnOccR env) rids) (andb (lext GHC.Base.== rext) (lmod
                                                                                      GHC.Base.==
                                                                                      rmod)))
    | _, l, r => l GHC.Base.== r
    end.

Axiom diffBinds : bool ->
                  Core.RnEnv2 ->
                  list (Core.Var * Core.CoreExpr)%type ->
                  list (Core.Var * Core.CoreExpr)%type ->
                  (list GHC.Base.String * Core.RnEnv2)%type.

Axiom diffExpr : bool ->
                 Core.RnEnv2 -> Core.CoreExpr -> Core.CoreExpr -> list GHC.Base.String.

Axiom diffIdInfo : Core.RnEnv2 -> Core.Var -> Core.Var -> list GHC.Base.String.

Axiom diffUnfold : Core.RnEnv2 ->
                   Core.Unfolding -> Core.Unfolding -> list GHC.Base.String.

#[global] Definition locBind
   : GHC.Base.String ->
     Core.Var -> Core.Var -> list GHC.Base.String -> list GHC.Base.String :=
  fun loc b1 b2 diffs =>
    let bindLoc :=
      if b1 GHC.Base.== b2 : bool then Panic.someSDoc else
      GHC.Base.mappend (GHC.Base.mappend Panic.someSDoc Panic.someSDoc)
                       Panic.someSDoc in
    let addLoc := fun d => d in GHC.Base.map addLoc diffs.

#[global] Definition isEmptyTy : AxiomatizedTypes.Type_ -> bool :=
  fun ty =>
    match Core.splitTyConApp_maybe ty with
    | Some (pair tc inst_tys) =>
        match Core.tyConDataCons_maybe tc with
        | Some dcs =>
            if Data.Foldable.all (Core.dataConCannotMatch inst_tys) dcs : bool
            then true else
            false
        | _ => false
        end
    | _ => false
    end.

#[global] Definition normSplitTyConApp_maybe
   : GHC.Core.FamInstEnv.FamInstEnvs ->
     AxiomatizedTypes.Type_ ->
     option (Core.TyCon * list AxiomatizedTypes.Type_ *
             AxiomatizedTypes.Coercion)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | fam_envs, ty =>
        let 'GHC.Core.Reduction.Reduction co ty1 := Maybes.orElse
                                                      (GHC.Core.FamInstEnv.topNormaliseType_maybe fam_envs ty)
                                                      (GHC.Core.Reduction.mkReflRedn HsSyn.Representational ty) in
        match Core.splitTyConApp_maybe ty1 with
        | Some (pair tc tc_args) => Some (pair (pair tc tc_args) co)
        | _ => None
        end
    end.

#[global] Definition extendInScopeSetBind
   : Core.InScopeSet -> Core.CoreBind -> Core.InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Core.InScope in_scope, binds =>
        Core.InScope (Core.foldBindersOfBindStrict Core.extendVarSet in_scope binds)
    end.

#[global] Definition extendInScopeSetBndrs
   : Core.InScopeSet -> list Core.CoreBind -> Core.InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Core.InScope in_scope, binds =>
        Core.InScope (Core.foldBindersOfBindsStrict Core.extendVarSet in_scope binds)
    end.

#[global] Definition mkInScopeSetBndrs
   : list Core.CoreBind -> Core.InScopeSet :=
  fun binds =>
    Core.foldBindersOfBindsStrict Core.extendInScopeSet Core.emptyInScopeSet binds.

#[global] Definition collectMakeStaticArgs
   : Core.CoreExpr ->
     option (Core.CoreExpr * AxiomatizedTypes.Type_ * Core.CoreExpr *
             Core.CoreExpr)%type :=
  fun '(e) =>
    match Core.collectArgsTicks (GHC.Base.const true) e with
    | pair (pair (Core.Mk_Var b as fun_) (cons (Core.Mk_Type t) (cons loc (cons arg
        nil)))) _ =>
        if Id.idName b GHC.Base.== PrelNames.makeStaticName : bool
        then Some (pair (pair (pair fun_ t) loc) arg) else
        None
    | _ => None
    end.

#[global] Definition isJoinBind : Core.CoreBind -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.NonRec b _ => Id.isJoinId b
    | Core.Rec (cons (pair b _) _) => Id.isJoinId b
    | _ => false
    end.

#[global] Definition dumpIdInfoOfProgram
   : bool ->
     (Core.IdInfo -> GHC.Base.String) -> Core.CoreProgram -> GHC.Base.String :=
  fun dump_locals ppr_id_info binds =>
    let printId :=
      fun id =>
        if orb (Core.isExportedId id) dump_locals : bool
        then GHC.Base.mappend (GHC.Base.mappend Panic.someSDoc Outputable.colon)
                              (ppr_id_info (Core.idInfo id)) else
        Panic.someSDoc in
    let getIds :=
      fun arg_1__ =>
        match arg_1__ with
        | Core.NonRec i _ => cons i nil
        | Core.Rec bs => GHC.Base.map Data.Tuple.fst bs
        end in
    let ids :=
      Data.OldList.sortBy (Data.Function.on Name.stableNameCmp Name.getName)
      (Data.Foldable.concatMap getIds binds) in
    Panic.someSDoc.

#[global] Definition wantCbvForId : bool -> Core.Var -> bool :=
  fun cbv_for_strict v =>
    let dmd := Id.idDemandInfo v in
    let ty := Id.idType v in
    if andb (Core.isId v) (andb (negb (RepType.isZeroBitTy ty)) (andb
                                 (Core.mightBeLiftedType ty) (andb (negb (Core.isFunTy ty)) (andb (orb (negb
                                                                                                        (Core.isStrictDmd
                                                                                                         dmd))
                                                                                                       cbv_for_strict)
                                                                                                  (negb (Core.isAbsDmd
                                                                                                         dmd)))))) : bool
    then true else
    false.

#[global] Definition shouldStrictifyIdForCbv : Core.Var -> bool :=
  wantCbvForId false.

#[global] Definition mkStrictFieldSeqs
   : list (Core.Id * Core.StrictnessMark)%type ->
     Core.CoreExpr -> Core.CoreExpr :=
  fun args rhs =>
    let case_ty := exprType rhs in
    let addEval
     : (Core.Id * Core.StrictnessMark)%type -> (Core.CoreExpr) -> (Core.CoreExpr) :=
      fun arg_1__ arg_2__ =>
        match arg_1__, arg_2__ with
        | pair arg_id arg_cbv, rhs =>
            if andb (Core.isMarkedStrict arg_cbv) (shouldStrictifyIdForCbv arg_id) : bool
            then Core.Case (Core.Mk_Var (Id.zapIdUnfolding arg_id)) arg_id case_ty (cons
                                                                                    (Core.Alt Core.DEFAULT nil rhs)
                                                                                    nil) else
            rhs
        end in
    Data.Foldable.foldr addEval rhs args.

#[global] Definition shouldUseCbvForId : Core.Var -> bool :=
  wantCbvForId true.

(* External variables:
     Eq Gt Lt None Some Type andb bool cons false list nat negb nil op_zt__ option
     orb pair true AxiomatizedTypes.Coercion AxiomatizedTypes.PrimOp
     AxiomatizedTypes.Type_ BasicTypes.Arity BasicTypes.Levity BasicTypes.Lifted
     BasicTypes.Unlifted Coq.Init.Datatypes.app Coq.Lists.List.flat_map Core.Alt
     Core.AltCon Core.App Core.Bndr Core.Case Core.Cast Core.CoercionR Core.CoreAlt
     Core.CoreArg Core.CoreBind Core.CoreBndr Core.CoreExpr Core.CoreProgram
     Core.DEFAULT Core.DataAlt Core.DataCon Core.DataConWorkId Core.Expr Core.Id
     Core.IdInfo Core.InScope Core.InScopeSet Core.Lam Core.Let Core.Lit Core.LitAlt
     Core.MCo Core.MCoercionR Core.MRefl Core.Mk_Coercion Core.Mk_Type Core.Mk_Var
     Core.Mult Core.NonRec Core.PrimOpId Core.Rec Core.RnEnv2 Core.StrictnessMark
     Core.Tickish Core.TyCoVar Core.TyCon Core.Unfolding Core.Var Core.cmpAlt
     Core.cmpAltCon Core.coercionLKind Core.coercionRKind Core.coercionRole
     Core.collectArgsTicks Core.coreTyLamForAllTyFlag Core.dataConCannotMatch
     Core.dataConTyCon Core.dataConUnivTyVars Core.definitelyUnliftedType
     Core.elemVarSet Core.emptyInScopeSet Core.extendInScopeSet Core.extendVarSet
     Core.foldBindersOfBindStrict Core.foldBindersOfBindsStrict Core.idDetails
     Core.idInfo Core.isAbsDmd Core.isCoVar Core.isCoVarType Core.isConLikeUnfolding
     Core.isEvaldUnfolding Core.isExportedId Core.isFunTy Core.isId
     Core.isMarkedStrict Core.isReflCo Core.isRuntimeArg Core.isRuntimeVar
     Core.isStrictDmd Core.isTyVar Core.isValArg Core.mightBeLiftedType
     Core.mightBeUnliftedType Core.mkCoCast Core.mkConApp Core.mkForAllTy
     Core.mkFunctionType Core.mkPiCo Core.mkTransCo Core.rnOccL Core.rnOccR
     Core.splitTyConApp_maybe Core.tyConDataCons_maybe Core.tyConFamilySize
     Core.typeLevity Core.valArgCount Core.varMult Core.varType Core.varsToCoreExprs
     Data.ByteString.Internal.Type.ByteString Data.Foldable.all Data.Foldable.and
     Data.Foldable.concatMap Data.Foldable.foldr Data.Foldable.null Data.Function.on
     Data.Maybe.isJust Data.OldList.sortBy Data.Set.Internal.fromList
     Data.Set.Internal.member Data.Tuple.fst Data.Tuple.snd Datatypes.id
     GHC.Base.String GHC.Base.const GHC.Base.id GHC.Base.map GHC.Base.mappend
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zl__
     GHC.Core.FamInstEnv.FamInstEnvs GHC.Core.FamInstEnv.topNormaliseType_maybe
     GHC.Core.Reduction.Reduction GHC.Core.Reduction.mkReflRedn
     GHC.Core.TyCo.Compare.eqType GHC.Core.TyCo.FVs.occCheckExpand
     GHC.Core.TyCo.FVs.tyCoVarsOfType GHC.Data.FastString.FastString
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Prim.rightSection
     GHC.Types.Tickish.Breakpoint GHC.Types.Tickish.CoreTickish
     GHC.Types.Tickish.GenTickish GHC.Types.Tickish.TickishPass
     GHC.Types.Tickish.isProfTick GHC.Types.Tickish.tickishFloatable
     GHC.Utils.Trace.warnPprTrace HsSyn.Representational
     HsToCoq.DeferredFix.deferredFix1 Id.hasNoBinding Id.idArity Id.idDemandInfo
     Id.idName Id.idType Id.idUnfolding Id.isConLikeId Id.isDataConWorkId
     Id.isDeadBinder Id.isJoinId Id.scaleVarBy Id.zapIdUnfolding Literal.LitString
     Literal.Literal Literal.isLitRubbish Literal.litIsDupable Literal.litIsTrivial
     Maybes.orElse Name.getName Name.stableNameCmp OrdList.OrdList OrdList.appOL
     OrdList.concatOL OrdList.fromOL OrdList.nilOL Outputable.colon Panic.assertPpr
     Panic.panic Panic.pprPanic Panic.someSDoc Platform.Platform
     PrelNames.makeStaticName PrelNames.unsafeEqualityProofIdKey
     PrelNames.unsafeReflDataConKey PrimOp.primOpIsWorkFree
     PrimOp.primOpOkForSpeculation PrimOp.primOpOkToDiscard RepType.isZeroBitTy
     Unique.Unique Unique.hasKey Util.HasDebugCallStack Util.dropList Util.filterOut
     Util.lengthIs Util.seqList
*)
