(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Lists.List.
Require Import Core.
Require CoreFVs.
Require CoreUtils.
Require Data.Foldable.
Require Data.Maybe.
Require Import Data.Traversable.
Require Data.Tuple.
Require Datatypes.
Require Import GHC.Base.
Require GHC.Core.TyCo.FVs.
Require GHC.Core.TyCo.Subst.
Require GHC.Err.
Require Import GHC.List.
Require GHC.Types.Tickish.
Require Id.
Require Maybes.
Require Name.
Require Panic.
Require UniqSupply.
Require Unique.
Require Util.

(* No type declarations to convert. *)

(* Midamble *)
(* Default_Subst is now defined in Core.v *)

(* Converted value declarations: *)

#[global] Definition extendIdSubst
   : Subst -> Id -> CoreExpr -> Subst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_Subst in_scope ids tvs cvs, v, r =>
        Panic.assertPpr (isNonCoVarId v) (Panic.someSDoc) (Mk_Subst
                                                           in_scope (extendVarEnv ids v r) tvs cvs)
    end.

#[global] Definition extendIdSubstWithClone
   : Subst -> Id -> Id -> Subst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_Subst in_scope ids tvs cvs, v, v' =>
        let new_in_scope :=
          extendVarSet (GHC.Core.TyCo.FVs.tyCoVarsOfType (varType v')) v' in
        Panic.assertPpr (isNonCoVarId v) (Panic.someSDoc) (Mk_Subst
                                                           (extendInScopeSetSet in_scope new_in_scope) (extendVarEnv ids
                                                            v (varToCoreExpr v')) tvs cvs)
    end.

#[global] Definition extendIdSubstList
   : Subst ->
     list (Id * CoreExpr)%type -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, prs =>
        Mk_Subst in_scope (extendVarEnvList ids prs) tvs cvs
    end.

#[global] Definition extendSubst
   : Subst -> Var -> CoreArg -> Subst :=
  fun subst var arg =>
    match arg with
    | Mk_Type ty => extendTvSubst subst var ty
    | Mk_Coercion co => extendCvSubst subst var co
    | _ => extendIdSubst subst var arg
    end.

#[global] Definition extendSubstWithVar
   : Subst -> Var -> Var -> Subst :=
  fun subst v1 v2 => extendIdSubst subst v1 (Mk_Var v2).

Fixpoint extendSubstList (arg_0__ : Subst) (arg_1__
                           : list (Var * CoreArg)%type) : Subst
  := match arg_0__, arg_1__ with
     | subst, nil => subst
     | subst, cons (pair var rhs) prs =>
         extendSubstList (extendSubst subst var rhs) prs
     end.

#[global] Definition lookupIdSubst `{Util.HasDebugCallStack}
   : Subst -> Id -> CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids _ _, v =>
        if Panic.assertPpr (andb (isId v) (negb (isCoVar v))) (Panic.someSDoc) negb
           (isLocalId v) : bool
        then Mk_Var v else
        match lookupVarEnv ids v with
        | Some e => e
        | _ =>
            match lookupInScope in_scope v with
            | Some v' => Mk_Var v'
            | _ => Panic.pprPanic (GHC.Base.hs_string__ "lookupIdSubst") (Panic.someSDoc)
            end
        end
    end.

#[global] Definition lookupIdSubst_maybe `{Util.HasDebugCallStack}
   : Subst -> Id -> option CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst _ ids _ _, v =>
        Panic.assertPpr (andb (isId v) (negb (isCoVar v))) (Panic.someSDoc)
        (lookupVarEnv ids v)
    end.

#[global] Definition delBndr
   : Subst -> Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, v =>
        if isCoVar v : bool
        then Mk_Subst in_scope ids tvs (delVarEnv cvs v) else
        if isTyVar v : bool
        then Mk_Subst in_scope ids (delVarEnv tvs v) cvs else
        Mk_Subst in_scope (delVarEnv ids v) tvs cvs
    end.

#[global] Definition delBndrs
   : Subst -> list Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst in_scope (delVarEnvList ids vs) (delVarEnvList tvs vs)
        (delVarEnvList cvs vs)
    end.

#[global] Definition mkOpenSubst
   : InScopeSet -> list (Var * CoreArg)%type -> Subst :=
  fun in_scope pairs =>
    Mk_Subst in_scope (mkVarEnv (let cont_0__ arg_1__ :=
                                                    let 'pair id e := arg_1__ in
                                                    if isId id : bool then cons (pair id e) nil else
                                                    nil in
                                                  Coq.Lists.List.flat_map cont_0__ pairs)) (mkVarEnv
                                                                                            (let cont_2__ arg_3__ :=
                                                                                               match arg_3__ with
                                                                                               | pair tv (Mk_Type ty) =>
                                                                                                   cons (pair tv ty) nil
                                                                                               | _ => nil
                                                                                               end in
                                                                                             Coq.Lists.List.flat_map
                                                                                             cont_2__ pairs)) (mkVarEnv
                                                                                                               (let cont_4__ arg_5__ :=
                                                                                                                  match arg_5__ with
                                                                                                                  | pair
                                                                                                                  v
                                                                                                                  (Mk_Coercion
                                                                                                                   co) =>
                                                                                                                      cons
                                                                                                                      (pair
                                                                                                                       v
                                                                                                                       co)
                                                                                                                      nil
                                                                                                                  | _ =>
                                                                                                                      nil
                                                                                                                  end in
                                                                                                                Coq.Lists.List.flat_map
                                                                                                                cont_4__
                                                                                                                pairs)).

(* substBndrs: axiomatized since it's part of the mutual fixpoint *)
Axiom substBndrs : Subst -> list Var -> (Subst * list Var)%type.

#[global] Definition substDVarSet `{Util.HasDebugCallStack}
   : Subst -> DVarSet -> DVarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_Subst _ _ tv_env cv_env as subst), fvs =>
        let subst_fv : Var -> (list Var * VarSet)%type -> (list Var * VarSet)%type :=
          fun fv acc =>
            if isTyVar fv : bool
            then let fv_ty := Maybes.orElse (lookupVarEnv tv_env fv) (mkTyVarTy fv) in
                 GHC.Core.TyCo.FVs.tyCoFVsOfType fv_ty (const true) emptyVarSet acc else
            if isCoVar fv : bool
            then let fv_co := Maybes.orElse (lookupVarEnv cv_env fv) (mkCoVarCo fv) in
                 GHC.Core.TyCo.FVs.tyCoFVsOfCo fv_co (const true) emptyVarSet acc else
            let fv_expr := lookupIdSubst subst fv in
            CoreFVs.exprFVs fv_expr (const true) emptyVarSet acc in
        mkDVarSet (Data.Tuple.fst (Data.Foldable.foldr subst_fv (pair nil emptyVarSet)
                                                       (dVarSetElems fvs)))
    end.

#[global] Definition substUnfolding
   : Subst -> Unfolding -> Unfolding :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, unf => unf end.

Axiom substExpr
   : forall `{Util.HasDebugCallStack},
     Subst -> CoreExpr -> CoreExpr.

#[global] Definition substExprSC `{Util.HasDebugCallStack}
   : Subst -> CoreExpr -> CoreExpr :=
  fun subst orig_expr =>
    if isEmptySubst subst : bool then orig_expr else
    substExpr subst orig_expr.

Axiom substBind : forall `{Util.HasDebugCallStack},
     Subst -> CoreBind -> (Subst * CoreBind)%type.

Axiom substBndr : Subst -> Var -> (Subst * Var)%type.

Axiom substRecBndrs : forall {f : Type -> Type} `{Traversable f},
     Subst -> f Id -> (Subst * f Id)%type.

#[global] Definition substBindSC `{Util.HasDebugCallStack}
   : Subst ->
     CoreBind -> (Subst * CoreBind)%type :=
  fun subst bind =>
    if negb (isEmptySubst subst) : bool
    then substBind subst bind else
    match bind with
    | NonRec bndr rhs =>
        let 'pair subst' bndr' := substBndr subst bndr in
        pair subst' (NonRec bndr' rhs)
    | Rec pairs =>
        let 'pair bndrs rhss := unzip pairs in
        let 'pair subst' bndrs' := substRecBndrs subst bndrs in
        let rhss' :=
          if isEmptySubst subst' : bool then rhss else
          map (substExpr subst') rhss in
        pair subst' (Rec (zip bndrs' rhss'))
    end.

#[global] Definition deShadowBinds : CoreProgram -> CoreProgram :=
  fun binds =>
    Data.Tuple.snd (mapAccumL substBind emptySubst binds).

Axiom substIdBndr : String -> Subst -> Subst -> Id -> (Subst * Id)%type.

Axiom substIdInfo : Subst -> Id -> IdInfo -> option IdInfo.

#[global] Definition substIdType : Subst -> Id -> Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_Subst _ _ tv_env cv_env as subst), id =>
        let old_w := varMult id in
        let old_ty := Id.idType id in
        if orb (andb (isEmptyVarEnv tv_env) (isEmptyVarEnv cv_env)) (andb
                (GHC.Core.TyCo.FVs.noFreeVarsOfType old_ty) (GHC.Core.TyCo.FVs.noFreeVarsOfType
                 old_w)) : bool
        then id else
        updateIdTypeAndMult (substTyUnchecked subst) id
    end.

#[global] Definition clone_id
   : Subst ->
     Subst ->
     (Id * Unique.Unique)%type -> (Subst * Id)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | rec_subst
    , (Mk_Subst in_scope idvs tvs cvs as subst)
    , pair old_id uniq =>
        let id1 := setVarUnique old_id uniq in
        let id2 := substIdType subst id1 in
        let new_id :=
          Id.maybeModifyIdInfo (substIdInfo rec_subst id2 (idInfo old_id)) id2 in
        let new_in_scope := extendInScopeSet in_scope new_id in
        let 'pair new_idvs new_cvs := pair (extendVarEnv idvs old_id (Mk_Var new_id))
                                           cvs in
        pair (Mk_Subst new_in_scope new_idvs tvs new_cvs) new_id
    end.

#[global] Definition cloneIdBndr
   : Subst ->
     UniqSupply.UniqSupply -> Id -> (Subst * Id)%type :=
  fun subst us old_id =>
    clone_id subst subst (pair old_id (UniqSupply.uniqFromSupply us)).

#[global] Definition cloneIdBndrs
   : Subst ->
     UniqSupply.UniqSupply ->
     list Id -> (Subst * list Id)%type :=
  fun subst us ids =>
    mapAccumL (clone_id subst) subst (zip ids (UniqSupply.uniqsFromSupply us)).

#[global] Definition cloneBndr
   : Subst ->
     Unique.Unique -> Var -> (Subst * Var)%type :=
  fun subst uniq v =>
    if isTyVar v : bool then cloneTyVarBndr subst v uniq else
    clone_id subst subst (pair v uniq).

#[global] Definition cloneBndrs {m : Type -> Type} `{UniqSupply.MonadUnique m}
   : Subst ->
     list Var -> m (Subst * list Var)%type :=
  fun subst vs =>
    UniqSupply.getUniquesM >>=
    (fun us =>
       pure (mapAccumL (fun arg_0__ arg_1__ =>
                          match arg_0__, arg_1__ with
                          | subst, pair v u => cloneBndr subst u v
                          end) subst (zip vs us))).

#[global] Definition cloneRecIdBndrs {m : Type -> Type} `{UniqSupply.MonadUnique
  m}
   : Subst ->
     list Id -> m (Subst * list Id)%type :=
  fun subst ids =>
    UniqSupply.getUniquesM >>=
    (fun us =>
       let 'pair subst' ids' := mapAccumL (clone_id (GHC.Err.error Panic.someSDoc))
                                  subst (zip ids us) in
       pure (pair subst' ids')).

#[global] Definition substUnfoldingSC
   : Subst -> Unfolding -> Unfolding :=
  fun subst unf =>
    if isEmptySubst subst : bool then unf else
    substUnfolding subst unf.

#[global] Definition substIdOcc : Subst -> Id -> Id :=
  fun subst v =>
    match lookupIdSubst subst v with
    | Mk_Var v' => v'
    | other => Panic.pprPanic (GHC.Base.hs_string__ "substIdOcc") (Panic.someSDoc)
    end.

Axiom substRuleInfo : Subst -> Id -> RuleInfo -> RuleInfo.

Axiom substRule : Subst -> (Name.Name -> Name.Name) -> CoreRule -> CoreRule.

#[global] Definition substRulesForImportedIds
   : Subst -> list CoreRule -> list CoreRule :=
  fun subst rules =>
    let not_needed :=
      fun name =>
        Panic.pprPanic (GHC.Base.hs_string__ "substRulesForImportedIds")
        (Panic.someSDoc) in
    map (substRule subst not_needed) rules.

Axiom substTickish : Subst -> GHC.Types.Tickish.CoreTickish -> GHC.Types.Tickish.CoreTickish.

(* External variables:
     Alt App BuiltinRule Case Cast CoreArg CoreBind CoreExpr CoreProgram CoreRule
     DVarSet Id IdInfo InScopeSet Lam Let Lit Mk_Coercion Mk_Type Mk_Var NonRec None
     Rec Rule RuleInfo Some String Traversable Type Unfolding Var VarSet andb bool
     cons const dVarSetElems delVarEnv delVarEnvList emptyVarSet extendInScopeSet
     extendInScopeSetSet extendVarEnv extendVarEnvList extendVarSet hasCoreUnfolding
     idInfo isCoVar isEmptyRuleInfo isEmptyVarEnv isId isLocalId isNonCoVarId isTyVar
     list lookupInScope lookupVarEnv map mapAccumL mkCoVarCo mkDVarSet mkTyVarTy
     mkVarEnv negb nil op_z2218U__ op_zeze__ op_zgzgze__ op_zt__ option orb pair pure
     realUnfoldingInfo ruleInfo setRuleInfo setUnfoldingInfo setVarUnique substBndrs
     true uniqAway unzip updateIdTypeAndMult varMult varToCoreExpr varType zip
     Coq.Lists.List.flat_map CoreFVs.exprFVs CoreUtils.getIdFromTrivialExpr_maybe
     Data.Foldable.foldr Data.Maybe.mapMaybe Data.Tuple.fst Data.Tuple.snd
     Datatypes.id GHC.Core.TyCo.FVs.noFreeVarsOfType GHC.Core.TyCo.FVs.tyCoFVsOfCo
     GHC.Core.TyCo.FVs.tyCoFVsOfType GHC.Core.TyCo.FVs.tyCoVarsOfType
     Subst cloneTyVarBndr
     emptySubst extendCvSubst
     extendTvSubst isEmptySubst
     substCo substTyUnchecked GHC.Err.error
     GHC.Types.Tickish.Breakpoint GHC.Types.Tickish.CoreTickish Id.idMult Id.idName
     Id.idType Id.maybeModifyIdInfo Maybes.orElse Name.Name Panic.assertPpr
     Panic.pprPanic Panic.someSDoc UniqSupply.MonadUnique UniqSupply.UniqSupply
     UniqSupply.getUniquesM UniqSupply.uniqFromSupply UniqSupply.uniqsFromSupply
     Unique.Unique Util.HasDebugCallStack
*)
