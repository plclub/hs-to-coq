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

Instance Default_Subst : HsToCoq.Err.Default Subst :=
  HsToCoq.Err.Build_Default _ (Mk_Subst HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

(* Converted value declarations: *)

#[global] Definition extendIdSubst
   : GHC.Core.TyCo.Subst.Subst -> Id -> CoreExpr -> GHC.Core.TyCo.Subst.Subst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | GHC.Core.TyCo.Subst.Subst in_scope ids tvs cvs, v, r =>
        Panic.assertPpr (isNonCoVarId v) (Panic.someSDoc) (GHC.Core.TyCo.Subst.Subst
                                                           in_scope (extendVarEnv ids v r) tvs cvs)
    end.

#[global] Definition extendIdSubstWithClone
   : GHC.Core.TyCo.Subst.Subst -> Id -> Id -> GHC.Core.TyCo.Subst.Subst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | GHC.Core.TyCo.Subst.Subst in_scope ids tvs cvs, v, v' =>
        let new_in_scope :=
          extendVarSet (GHC.Core.TyCo.FVs.tyCoVarsOfType (varType v')) v' in
        Panic.assertPpr (isNonCoVarId v) (Panic.someSDoc) (GHC.Core.TyCo.Subst.Subst
                                                           (extendInScopeSetSet in_scope new_in_scope) (extendVarEnv ids
                                                            v (varToCoreExpr v')) tvs cvs)
    end.

#[global] Definition extendIdSubstList
   : GHC.Core.TyCo.Subst.Subst ->
     list (Id * CoreExpr)%type -> GHC.Core.TyCo.Subst.Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | GHC.Core.TyCo.Subst.Subst in_scope ids tvs cvs, prs =>
        GHC.Core.TyCo.Subst.Subst in_scope (extendVarEnvList ids prs) tvs cvs
    end.

#[global] Definition extendSubst
   : GHC.Core.TyCo.Subst.Subst -> Var -> CoreArg -> GHC.Core.TyCo.Subst.Subst :=
  fun subst var arg =>
    match arg with
    | Mk_Type ty => GHC.Core.TyCo.Subst.extendTvSubst subst var ty
    | Mk_Coercion co => GHC.Core.TyCo.Subst.extendCvSubst subst var co
    | _ => extendIdSubst subst var arg
    end.

#[global] Definition extendSubstWithVar
   : GHC.Core.TyCo.Subst.Subst -> Var -> Var -> GHC.Core.TyCo.Subst.Subst :=
  fun subst v1 v2 => extendIdSubst subst v1 (Mk_Var v2).

Fixpoint extendSubstList (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__
                           : list (Var * CoreArg)%type) : GHC.Core.TyCo.Subst.Subst
  := match arg_0__, arg_1__ with
     | subst, nil => subst
     | subst, cons (pair var rhs) prs =>
         extendSubstList (extendSubst subst var rhs) prs
     end.

#[global] Definition lookupIdSubst `{Util.HasDebugCallStack}
   : GHC.Core.TyCo.Subst.Subst -> Id -> CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | GHC.Core.TyCo.Subst.Subst in_scope ids _ _, v =>
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
   : GHC.Core.TyCo.Subst.Subst -> Id -> option CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | GHC.Core.TyCo.Subst.Subst _ ids _ _, v =>
        Panic.assertPpr (andb (isId v) (negb (isCoVar v))) (Panic.someSDoc)
        (lookupVarEnv ids v)
    end.

#[global] Definition delBndr
   : GHC.Core.TyCo.Subst.Subst -> Var -> GHC.Core.TyCo.Subst.Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | GHC.Core.TyCo.Subst.Subst in_scope ids tvs cvs, v =>
        if isCoVar v : bool
        then GHC.Core.TyCo.Subst.Subst in_scope ids tvs (delVarEnv cvs v) else
        if isTyVar v : bool
        then GHC.Core.TyCo.Subst.Subst in_scope ids (delVarEnv tvs v) cvs else
        GHC.Core.TyCo.Subst.Subst in_scope (delVarEnv ids v) tvs cvs
    end.

#[global] Definition delBndrs
   : GHC.Core.TyCo.Subst.Subst -> list Var -> GHC.Core.TyCo.Subst.Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | GHC.Core.TyCo.Subst.Subst in_scope ids tvs cvs, vs =>
        GHC.Core.TyCo.Subst.Subst in_scope (delVarEnvList ids vs) (delVarEnvList tvs vs)
        (delVarEnvList cvs vs)
    end.

#[global] Definition mkOpenSubst
   : InScopeSet -> list (Var * CoreArg)%type -> GHC.Core.TyCo.Subst.Subst :=
  fun in_scope pairs =>
    GHC.Core.TyCo.Subst.Subst in_scope (mkVarEnv (let cont_0__ arg_1__ :=
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

(* Skipping definition `CoreSubst.substBndrs' *)

#[global] Definition substDVarSet `{Util.HasDebugCallStack}
   : GHC.Core.TyCo.Subst.Subst -> DVarSet -> DVarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (GHC.Core.TyCo.Subst.Subst _ _ tv_env cv_env as subst), fvs =>
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
   : GHC.Core.TyCo.Subst.Subst -> Unfolding -> Unfolding :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, unf => unf end.

#[global] Definition substExpr
   : forall `{Util.HasDebugCallStack},
     GHC.Core.TyCo.Subst.Subst -> CoreExpr -> CoreExpr :=
  fix substExpr `{Util.HasDebugCallStack} (subst : GHC.Core.TyCo.Subst.Subst)
                (expr : CoreExpr) : CoreExpr
    := let go_alt :=
         fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | subst, Alt con bndrs rhs =>
               let 'pair subst' bndrs' := substBndrs subst bndrs in
               Alt con bndrs' (substExpr subst' rhs)
           end in
       let fix go arg_5__
         := match arg_5__ with
            | Mk_Var v => lookupIdSubst subst v
            | Mk_Type ty => Mk_Type (GHC.Core.TyCo.Subst.substTyUnchecked subst ty)
            | Mk_Coercion co => Mk_Coercion (GHC.Core.TyCo.Subst.substCo subst co)
            | Lit lit => Lit lit
            | App fun_ arg => App (go fun_) (go arg)
            | Cast e co => Cast (go e) (GHC.Core.TyCo.Subst.substCo subst co)
            | Lam bndr body =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Lam bndr' (substExpr subst' body)
            | Let bind body =>
                let 'pair subst' bind' := substBind subst bind in
                Let bind' (substExpr subst' body)
            | Case scrut bndr ty alts =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Case (go scrut) bndr' (GHC.Core.TyCo.Subst.substTyUnchecked subst ty) (map
                                                                                       (go_alt subst') alts)
            end in
       go expr
  with substBind `{Util.HasDebugCallStack} (arg_0__ : GHC.Core.TyCo.Subst.Subst)
                 (arg_1__ : CoreBind) : (GHC.Core.TyCo.Subst.Subst * CoreBind)%type
    := match arg_0__, arg_1__ with
       | subst, NonRec bndr rhs =>
           let 'pair subst' bndr' := substBndr subst bndr in
           pair subst' (NonRec bndr' (substExpr subst rhs))
       | subst, Rec pairs =>
           let 'pair bndrs rhss := unzip pairs in
           let 'pair subst' bndrs' := substRecBndrs subst bndrs in
           let rhss' := map (substExpr subst') rhss in pair subst' (Rec (zip bndrs' rhss'))
       end
  with substBndr (subst : GHC.Core.TyCo.Subst.Subst) (bndr : Var)
    : (GHC.Core.TyCo.Subst.Subst * Var)%type
    := substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr
  with substIdBndr (arg_0__ : String) (arg_1__ arg_2__
                     : GHC.Core.TyCo.Subst.Subst) (arg_3__ : Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                    Id)%type
    := match arg_0__, arg_1__, arg_2__, arg_3__ with
       | _doc
       , rec_subst
       , (GHC.Core.TyCo.Subst.Subst in_scope env tvs cvs as subst)
       , old_id =>
           let old_w := Id.idMult old_id in
           let old_ty := Id.idType old_id in
           let no_type_change :=
             orb (andb (isEmptyVarEnv tvs) (isEmptyVarEnv cvs)) (andb
                  (GHC.Core.TyCo.FVs.noFreeVarsOfType old_ty) (GHC.Core.TyCo.FVs.noFreeVarsOfType
                   old_w)) in
           let id1 := uniqAway in_scope old_id in
           let id2 :=
             if no_type_change : bool then id1 else
             updateIdTypeAndMult (GHC.Core.TyCo.Subst.substTyUnchecked subst) id1 in
           let mb_new_info := substIdInfo rec_subst id2 (idInfo id2) in
           let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
           let new_in_scope := extendInScopeSet in_scope new_id in
           let no_change := id1 == old_id in
           let new_env :=
             if no_change : bool then delVarEnv env old_id else
             extendVarEnv env old_id (Mk_Var new_id) in
           pair (GHC.Core.TyCo.Subst.Subst new_in_scope new_env tvs cvs) new_id
       end
  with substIdInfo (subst : GHC.Core.TyCo.Subst.Subst) (new_id : Id) (info
                     : IdInfo) : option IdInfo
    := let old_unf := realUnfoldingInfo info in
       let old_rules := ruleInfo info in
       let nothing_to_do :=
         andb (isEmptyRuleInfo old_rules) (negb (hasCoreUnfolding old_unf)) in
       if nothing_to_do : bool then None else
       Some (setUnfoldingInfo (setRuleInfo info (substRuleInfo subst new_id old_rules))
                              (substUnfolding subst old_unf))
  with substRuleInfo (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__ : Id) (arg_2__
                       : RuleInfo) : RuleInfo
    := match arg_0__, arg_1__, arg_2__ with
       | subst, new_id, RuleInfo rules rhs_fvs =>
           let subst_ru_fn := const (Id.idName new_id) in
           RuleInfo (map (substRule subst subst_ru_fn) rules) (substDVarSet subst rhs_fvs)
       end
  with substRule (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__
                   : (Name.Name -> Name.Name)) (arg_2__ : CoreRule) : CoreRule
    := match arg_0__, arg_1__, arg_2__ with
       | _, _, (BuiltinRule _ _ _ _ as rule) => rule
       | subst
       , subst_ru_fn
       , (Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
           let 'pair subst' bndrs' := substBndrs subst bndrs in
           match rule with
           | Rule ru_name_4__ ru_act_5__ ru_fn_6__ ru_rough_7__ ru_bndrs_8__ ru_args_9__
           ru_rhs_10__ ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__ =>
               Rule ru_name_4__ ru_act_5__ (if is_local : bool
                     then subst_ru_fn fn_name
                     else fn_name) ru_rough_7__ bndrs' (map (substExpr subst') args) (substExpr
                     subst' rhs) ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__
           | BuiltinRule _ _ _ _ =>
               GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
           end
       end
  with substRecBndrs {f : Type -> Type} `{Traversable f} (subst
                       : GHC.Core.TyCo.Subst.Subst) (bndrs : f Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                      f Id)%type
    := let 'pair new_subst new_bndrs := mapAccumL (substIdBndr (Datatypes.id
                                                                (GHC.Base.hs_string__ "rec-bndr")) (GHC.Err.error
                                                                Panic.someSDoc)) subst bndrs in
       pair new_subst new_bndrs for substExpr.

#[global] Definition substExprSC `{Util.HasDebugCallStack}
   : GHC.Core.TyCo.Subst.Subst -> CoreExpr -> CoreExpr :=
  fun subst orig_expr =>
    if GHC.Core.TyCo.Subst.isEmptySubst subst : bool then orig_expr else
    substExpr subst orig_expr.

#[global] Definition substBind
   : forall `{Util.HasDebugCallStack},
     GHC.Core.TyCo.Subst.Subst ->
     CoreBind -> (GHC.Core.TyCo.Subst.Subst * CoreBind)%type :=
  fix substExpr `{Util.HasDebugCallStack} (subst : GHC.Core.TyCo.Subst.Subst)
                (expr : CoreExpr) : CoreExpr
    := let go_alt :=
         fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | subst, Alt con bndrs rhs =>
               let 'pair subst' bndrs' := substBndrs subst bndrs in
               Alt con bndrs' (substExpr subst' rhs)
           end in
       let fix go arg_5__
         := match arg_5__ with
            | Mk_Var v => lookupIdSubst subst v
            | Mk_Type ty => Mk_Type (GHC.Core.TyCo.Subst.substTyUnchecked subst ty)
            | Mk_Coercion co => Mk_Coercion (GHC.Core.TyCo.Subst.substCo subst co)
            | Lit lit => Lit lit
            | App fun_ arg => App (go fun_) (go arg)
            | Cast e co => Cast (go e) (GHC.Core.TyCo.Subst.substCo subst co)
            | Lam bndr body =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Lam bndr' (substExpr subst' body)
            | Let bind body =>
                let 'pair subst' bind' := substBind subst bind in
                Let bind' (substExpr subst' body)
            | Case scrut bndr ty alts =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Case (go scrut) bndr' (GHC.Core.TyCo.Subst.substTyUnchecked subst ty) (map
                                                                                       (go_alt subst') alts)
            end in
       go expr
  with substBind `{Util.HasDebugCallStack} (arg_0__ : GHC.Core.TyCo.Subst.Subst)
                 (arg_1__ : CoreBind) : (GHC.Core.TyCo.Subst.Subst * CoreBind)%type
    := match arg_0__, arg_1__ with
       | subst, NonRec bndr rhs =>
           let 'pair subst' bndr' := substBndr subst bndr in
           pair subst' (NonRec bndr' (substExpr subst rhs))
       | subst, Rec pairs =>
           let 'pair bndrs rhss := unzip pairs in
           let 'pair subst' bndrs' := substRecBndrs subst bndrs in
           let rhss' := map (substExpr subst') rhss in pair subst' (Rec (zip bndrs' rhss'))
       end
  with substBndr (subst : GHC.Core.TyCo.Subst.Subst) (bndr : Var)
    : (GHC.Core.TyCo.Subst.Subst * Var)%type
    := substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr
  with substIdBndr (arg_0__ : String) (arg_1__ arg_2__
                     : GHC.Core.TyCo.Subst.Subst) (arg_3__ : Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                    Id)%type
    := match arg_0__, arg_1__, arg_2__, arg_3__ with
       | _doc
       , rec_subst
       , (GHC.Core.TyCo.Subst.Subst in_scope env tvs cvs as subst)
       , old_id =>
           let old_w := Id.idMult old_id in
           let old_ty := Id.idType old_id in
           let no_type_change :=
             orb (andb (isEmptyVarEnv tvs) (isEmptyVarEnv cvs)) (andb
                  (GHC.Core.TyCo.FVs.noFreeVarsOfType old_ty) (GHC.Core.TyCo.FVs.noFreeVarsOfType
                   old_w)) in
           let id1 := uniqAway in_scope old_id in
           let id2 :=
             if no_type_change : bool then id1 else
             updateIdTypeAndMult (GHC.Core.TyCo.Subst.substTyUnchecked subst) id1 in
           let mb_new_info := substIdInfo rec_subst id2 (idInfo id2) in
           let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
           let new_in_scope := extendInScopeSet in_scope new_id in
           let no_change := id1 == old_id in
           let new_env :=
             if no_change : bool then delVarEnv env old_id else
             extendVarEnv env old_id (Mk_Var new_id) in
           pair (GHC.Core.TyCo.Subst.Subst new_in_scope new_env tvs cvs) new_id
       end
  with substIdInfo (subst : GHC.Core.TyCo.Subst.Subst) (new_id : Id) (info
                     : IdInfo) : option IdInfo
    := let old_unf := realUnfoldingInfo info in
       let old_rules := ruleInfo info in
       let nothing_to_do :=
         andb (isEmptyRuleInfo old_rules) (negb (hasCoreUnfolding old_unf)) in
       if nothing_to_do : bool then None else
       Some (setUnfoldingInfo (setRuleInfo info (substRuleInfo subst new_id old_rules))
                              (substUnfolding subst old_unf))
  with substRuleInfo (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__ : Id) (arg_2__
                       : RuleInfo) : RuleInfo
    := match arg_0__, arg_1__, arg_2__ with
       | subst, new_id, RuleInfo rules rhs_fvs =>
           let subst_ru_fn := const (Id.idName new_id) in
           RuleInfo (map (substRule subst subst_ru_fn) rules) (substDVarSet subst rhs_fvs)
       end
  with substRule (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__
                   : (Name.Name -> Name.Name)) (arg_2__ : CoreRule) : CoreRule
    := match arg_0__, arg_1__, arg_2__ with
       | _, _, (BuiltinRule _ _ _ _ as rule) => rule
       | subst
       , subst_ru_fn
       , (Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
           let 'pair subst' bndrs' := substBndrs subst bndrs in
           match rule with
           | Rule ru_name_4__ ru_act_5__ ru_fn_6__ ru_rough_7__ ru_bndrs_8__ ru_args_9__
           ru_rhs_10__ ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__ =>
               Rule ru_name_4__ ru_act_5__ (if is_local : bool
                     then subst_ru_fn fn_name
                     else fn_name) ru_rough_7__ bndrs' (map (substExpr subst') args) (substExpr
                     subst' rhs) ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__
           | BuiltinRule _ _ _ _ =>
               GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
           end
       end
  with substRecBndrs {f : Type -> Type} `{Traversable f} (subst
                       : GHC.Core.TyCo.Subst.Subst) (bndrs : f Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                      f Id)%type
    := let 'pair new_subst new_bndrs := mapAccumL (substIdBndr (Datatypes.id
                                                                (GHC.Base.hs_string__ "rec-bndr")) (GHC.Err.error
                                                                Panic.someSDoc)) subst bndrs in
       pair new_subst new_bndrs for substBind.

#[global] Definition substBndr
   : GHC.Core.TyCo.Subst.Subst -> Var -> (GHC.Core.TyCo.Subst.Subst * Var)%type :=
  fix substExpr `{Util.HasDebugCallStack} (subst : GHC.Core.TyCo.Subst.Subst)
                (expr : CoreExpr) : CoreExpr
    := let go_alt :=
         fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | subst, Alt con bndrs rhs =>
               let 'pair subst' bndrs' := substBndrs subst bndrs in
               Alt con bndrs' (substExpr subst' rhs)
           end in
       let fix go arg_5__
         := match arg_5__ with
            | Mk_Var v => lookupIdSubst subst v
            | Mk_Type ty => Mk_Type (GHC.Core.TyCo.Subst.substTyUnchecked subst ty)
            | Mk_Coercion co => Mk_Coercion (GHC.Core.TyCo.Subst.substCo subst co)
            | Lit lit => Lit lit
            | App fun_ arg => App (go fun_) (go arg)
            | Cast e co => Cast (go e) (GHC.Core.TyCo.Subst.substCo subst co)
            | Lam bndr body =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Lam bndr' (substExpr subst' body)
            | Let bind body =>
                let 'pair subst' bind' := substBind subst bind in
                Let bind' (substExpr subst' body)
            | Case scrut bndr ty alts =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Case (go scrut) bndr' (GHC.Core.TyCo.Subst.substTyUnchecked subst ty) (map
                                                                                       (go_alt subst') alts)
            end in
       go expr
  with substBind `{Util.HasDebugCallStack} (arg_0__ : GHC.Core.TyCo.Subst.Subst)
                 (arg_1__ : CoreBind) : (GHC.Core.TyCo.Subst.Subst * CoreBind)%type
    := match arg_0__, arg_1__ with
       | subst, NonRec bndr rhs =>
           let 'pair subst' bndr' := substBndr subst bndr in
           pair subst' (NonRec bndr' (substExpr subst rhs))
       | subst, Rec pairs =>
           let 'pair bndrs rhss := unzip pairs in
           let 'pair subst' bndrs' := substRecBndrs subst bndrs in
           let rhss' := map (substExpr subst') rhss in pair subst' (Rec (zip bndrs' rhss'))
       end
  with substBndr (subst : GHC.Core.TyCo.Subst.Subst) (bndr : Var)
    : (GHC.Core.TyCo.Subst.Subst * Var)%type
    := substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr
  with substIdBndr (arg_0__ : String) (arg_1__ arg_2__
                     : GHC.Core.TyCo.Subst.Subst) (arg_3__ : Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                    Id)%type
    := match arg_0__, arg_1__, arg_2__, arg_3__ with
       | _doc
       , rec_subst
       , (GHC.Core.TyCo.Subst.Subst in_scope env tvs cvs as subst)
       , old_id =>
           let old_w := Id.idMult old_id in
           let old_ty := Id.idType old_id in
           let no_type_change :=
             orb (andb (isEmptyVarEnv tvs) (isEmptyVarEnv cvs)) (andb
                  (GHC.Core.TyCo.FVs.noFreeVarsOfType old_ty) (GHC.Core.TyCo.FVs.noFreeVarsOfType
                   old_w)) in
           let id1 := uniqAway in_scope old_id in
           let id2 :=
             if no_type_change : bool then id1 else
             updateIdTypeAndMult (GHC.Core.TyCo.Subst.substTyUnchecked subst) id1 in
           let mb_new_info := substIdInfo rec_subst id2 (idInfo id2) in
           let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
           let new_in_scope := extendInScopeSet in_scope new_id in
           let no_change := id1 == old_id in
           let new_env :=
             if no_change : bool then delVarEnv env old_id else
             extendVarEnv env old_id (Mk_Var new_id) in
           pair (GHC.Core.TyCo.Subst.Subst new_in_scope new_env tvs cvs) new_id
       end
  with substIdInfo (subst : GHC.Core.TyCo.Subst.Subst) (new_id : Id) (info
                     : IdInfo) : option IdInfo
    := let old_unf := realUnfoldingInfo info in
       let old_rules := ruleInfo info in
       let nothing_to_do :=
         andb (isEmptyRuleInfo old_rules) (negb (hasCoreUnfolding old_unf)) in
       if nothing_to_do : bool then None else
       Some (setUnfoldingInfo (setRuleInfo info (substRuleInfo subst new_id old_rules))
                              (substUnfolding subst old_unf))
  with substRuleInfo (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__ : Id) (arg_2__
                       : RuleInfo) : RuleInfo
    := match arg_0__, arg_1__, arg_2__ with
       | subst, new_id, RuleInfo rules rhs_fvs =>
           let subst_ru_fn := const (Id.idName new_id) in
           RuleInfo (map (substRule subst subst_ru_fn) rules) (substDVarSet subst rhs_fvs)
       end
  with substRule (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__
                   : (Name.Name -> Name.Name)) (arg_2__ : CoreRule) : CoreRule
    := match arg_0__, arg_1__, arg_2__ with
       | _, _, (BuiltinRule _ _ _ _ as rule) => rule
       | subst
       , subst_ru_fn
       , (Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
           let 'pair subst' bndrs' := substBndrs subst bndrs in
           match rule with
           | Rule ru_name_4__ ru_act_5__ ru_fn_6__ ru_rough_7__ ru_bndrs_8__ ru_args_9__
           ru_rhs_10__ ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__ =>
               Rule ru_name_4__ ru_act_5__ (if is_local : bool
                     then subst_ru_fn fn_name
                     else fn_name) ru_rough_7__ bndrs' (map (substExpr subst') args) (substExpr
                     subst' rhs) ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__
           | BuiltinRule _ _ _ _ =>
               GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
           end
       end
  with substRecBndrs {f : Type -> Type} `{Traversable f} (subst
                       : GHC.Core.TyCo.Subst.Subst) (bndrs : f Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                      f Id)%type
    := let 'pair new_subst new_bndrs := mapAccumL (substIdBndr (Datatypes.id
                                                                (GHC.Base.hs_string__ "rec-bndr")) (GHC.Err.error
                                                                Panic.someSDoc)) subst bndrs in
       pair new_subst new_bndrs for substBndr.

#[global] Definition substRecBndrs
   : forall {f : Type -> Type} `{Traversable f},
     GHC.Core.TyCo.Subst.Subst -> f Id -> (GHC.Core.TyCo.Subst.Subst * f Id)%type :=
  fix substExpr `{Util.HasDebugCallStack} (subst : GHC.Core.TyCo.Subst.Subst)
                (expr : CoreExpr) : CoreExpr
    := let go_alt :=
         fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | subst, Alt con bndrs rhs =>
               let 'pair subst' bndrs' := substBndrs subst bndrs in
               Alt con bndrs' (substExpr subst' rhs)
           end in
       let fix go arg_5__
         := match arg_5__ with
            | Mk_Var v => lookupIdSubst subst v
            | Mk_Type ty => Mk_Type (GHC.Core.TyCo.Subst.substTyUnchecked subst ty)
            | Mk_Coercion co => Mk_Coercion (GHC.Core.TyCo.Subst.substCo subst co)
            | Lit lit => Lit lit
            | App fun_ arg => App (go fun_) (go arg)
            | Cast e co => Cast (go e) (GHC.Core.TyCo.Subst.substCo subst co)
            | Lam bndr body =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Lam bndr' (substExpr subst' body)
            | Let bind body =>
                let 'pair subst' bind' := substBind subst bind in
                Let bind' (substExpr subst' body)
            | Case scrut bndr ty alts =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Case (go scrut) bndr' (GHC.Core.TyCo.Subst.substTyUnchecked subst ty) (map
                                                                                       (go_alt subst') alts)
            end in
       go expr
  with substBind `{Util.HasDebugCallStack} (arg_0__ : GHC.Core.TyCo.Subst.Subst)
                 (arg_1__ : CoreBind) : (GHC.Core.TyCo.Subst.Subst * CoreBind)%type
    := match arg_0__, arg_1__ with
       | subst, NonRec bndr rhs =>
           let 'pair subst' bndr' := substBndr subst bndr in
           pair subst' (NonRec bndr' (substExpr subst rhs))
       | subst, Rec pairs =>
           let 'pair bndrs rhss := unzip pairs in
           let 'pair subst' bndrs' := substRecBndrs subst bndrs in
           let rhss' := map (substExpr subst') rhss in pair subst' (Rec (zip bndrs' rhss'))
       end
  with substBndr (subst : GHC.Core.TyCo.Subst.Subst) (bndr : Var)
    : (GHC.Core.TyCo.Subst.Subst * Var)%type
    := substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr
  with substIdBndr (arg_0__ : String) (arg_1__ arg_2__
                     : GHC.Core.TyCo.Subst.Subst) (arg_3__ : Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                    Id)%type
    := match arg_0__, arg_1__, arg_2__, arg_3__ with
       | _doc
       , rec_subst
       , (GHC.Core.TyCo.Subst.Subst in_scope env tvs cvs as subst)
       , old_id =>
           let old_w := Id.idMult old_id in
           let old_ty := Id.idType old_id in
           let no_type_change :=
             orb (andb (isEmptyVarEnv tvs) (isEmptyVarEnv cvs)) (andb
                  (GHC.Core.TyCo.FVs.noFreeVarsOfType old_ty) (GHC.Core.TyCo.FVs.noFreeVarsOfType
                   old_w)) in
           let id1 := uniqAway in_scope old_id in
           let id2 :=
             if no_type_change : bool then id1 else
             updateIdTypeAndMult (GHC.Core.TyCo.Subst.substTyUnchecked subst) id1 in
           let mb_new_info := substIdInfo rec_subst id2 (idInfo id2) in
           let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
           let new_in_scope := extendInScopeSet in_scope new_id in
           let no_change := id1 == old_id in
           let new_env :=
             if no_change : bool then delVarEnv env old_id else
             extendVarEnv env old_id (Mk_Var new_id) in
           pair (GHC.Core.TyCo.Subst.Subst new_in_scope new_env tvs cvs) new_id
       end
  with substIdInfo (subst : GHC.Core.TyCo.Subst.Subst) (new_id : Id) (info
                     : IdInfo) : option IdInfo
    := let old_unf := realUnfoldingInfo info in
       let old_rules := ruleInfo info in
       let nothing_to_do :=
         andb (isEmptyRuleInfo old_rules) (negb (hasCoreUnfolding old_unf)) in
       if nothing_to_do : bool then None else
       Some (setUnfoldingInfo (setRuleInfo info (substRuleInfo subst new_id old_rules))
                              (substUnfolding subst old_unf))
  with substRuleInfo (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__ : Id) (arg_2__
                       : RuleInfo) : RuleInfo
    := match arg_0__, arg_1__, arg_2__ with
       | subst, new_id, RuleInfo rules rhs_fvs =>
           let subst_ru_fn := const (Id.idName new_id) in
           RuleInfo (map (substRule subst subst_ru_fn) rules) (substDVarSet subst rhs_fvs)
       end
  with substRule (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__
                   : (Name.Name -> Name.Name)) (arg_2__ : CoreRule) : CoreRule
    := match arg_0__, arg_1__, arg_2__ with
       | _, _, (BuiltinRule _ _ _ _ as rule) => rule
       | subst
       , subst_ru_fn
       , (Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
           let 'pair subst' bndrs' := substBndrs subst bndrs in
           match rule with
           | Rule ru_name_4__ ru_act_5__ ru_fn_6__ ru_rough_7__ ru_bndrs_8__ ru_args_9__
           ru_rhs_10__ ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__ =>
               Rule ru_name_4__ ru_act_5__ (if is_local : bool
                     then subst_ru_fn fn_name
                     else fn_name) ru_rough_7__ bndrs' (map (substExpr subst') args) (substExpr
                     subst' rhs) ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__
           | BuiltinRule _ _ _ _ =>
               GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
           end
       end
  with substRecBndrs {f : Type -> Type} `{Traversable f} (subst
                       : GHC.Core.TyCo.Subst.Subst) (bndrs : f Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                      f Id)%type
    := let 'pair new_subst new_bndrs := mapAccumL (substIdBndr (Datatypes.id
                                                                (GHC.Base.hs_string__ "rec-bndr")) (GHC.Err.error
                                                                Panic.someSDoc)) subst bndrs in
       pair new_subst new_bndrs for substRecBndrs.

#[global] Definition substBindSC `{Util.HasDebugCallStack}
   : GHC.Core.TyCo.Subst.Subst ->
     CoreBind -> (GHC.Core.TyCo.Subst.Subst * CoreBind)%type :=
  fun subst bind =>
    if negb (GHC.Core.TyCo.Subst.isEmptySubst subst) : bool
    then substBind subst bind else
    match bind with
    | NonRec bndr rhs =>
        let 'pair subst' bndr' := substBndr subst bndr in
        pair subst' (NonRec bndr' rhs)
    | Rec pairs =>
        let 'pair bndrs rhss := unzip pairs in
        let 'pair subst' bndrs' := substRecBndrs subst bndrs in
        let rhss' :=
          if GHC.Core.TyCo.Subst.isEmptySubst subst' : bool then rhss else
          map (substExpr subst') rhss in
        pair subst' (Rec (zip bndrs' rhss'))
    end.

#[global] Definition deShadowBinds : CoreProgram -> CoreProgram :=
  fun binds =>
    Data.Tuple.snd (mapAccumL substBind GHC.Core.TyCo.Subst.emptySubst binds).

#[global] Definition substIdBndr
   : String ->
     GHC.Core.TyCo.Subst.Subst ->
     GHC.Core.TyCo.Subst.Subst -> Id -> (GHC.Core.TyCo.Subst.Subst * Id)%type :=
  fix substExpr `{Util.HasDebugCallStack} (subst : GHC.Core.TyCo.Subst.Subst)
                (expr : CoreExpr) : CoreExpr
    := let go_alt :=
         fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | subst, Alt con bndrs rhs =>
               let 'pair subst' bndrs' := substBndrs subst bndrs in
               Alt con bndrs' (substExpr subst' rhs)
           end in
       let fix go arg_5__
         := match arg_5__ with
            | Mk_Var v => lookupIdSubst subst v
            | Mk_Type ty => Mk_Type (GHC.Core.TyCo.Subst.substTyUnchecked subst ty)
            | Mk_Coercion co => Mk_Coercion (GHC.Core.TyCo.Subst.substCo subst co)
            | Lit lit => Lit lit
            | App fun_ arg => App (go fun_) (go arg)
            | Cast e co => Cast (go e) (GHC.Core.TyCo.Subst.substCo subst co)
            | Lam bndr body =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Lam bndr' (substExpr subst' body)
            | Let bind body =>
                let 'pair subst' bind' := substBind subst bind in
                Let bind' (substExpr subst' body)
            | Case scrut bndr ty alts =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Case (go scrut) bndr' (GHC.Core.TyCo.Subst.substTyUnchecked subst ty) (map
                                                                                       (go_alt subst') alts)
            end in
       go expr
  with substBind `{Util.HasDebugCallStack} (arg_0__ : GHC.Core.TyCo.Subst.Subst)
                 (arg_1__ : CoreBind) : (GHC.Core.TyCo.Subst.Subst * CoreBind)%type
    := match arg_0__, arg_1__ with
       | subst, NonRec bndr rhs =>
           let 'pair subst' bndr' := substBndr subst bndr in
           pair subst' (NonRec bndr' (substExpr subst rhs))
       | subst, Rec pairs =>
           let 'pair bndrs rhss := unzip pairs in
           let 'pair subst' bndrs' := substRecBndrs subst bndrs in
           let rhss' := map (substExpr subst') rhss in pair subst' (Rec (zip bndrs' rhss'))
       end
  with substBndr (subst : GHC.Core.TyCo.Subst.Subst) (bndr : Var)
    : (GHC.Core.TyCo.Subst.Subst * Var)%type
    := substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr
  with substIdBndr (arg_0__ : String) (arg_1__ arg_2__
                     : GHC.Core.TyCo.Subst.Subst) (arg_3__ : Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                    Id)%type
    := match arg_0__, arg_1__, arg_2__, arg_3__ with
       | _doc
       , rec_subst
       , (GHC.Core.TyCo.Subst.Subst in_scope env tvs cvs as subst)
       , old_id =>
           let old_w := Id.idMult old_id in
           let old_ty := Id.idType old_id in
           let no_type_change :=
             orb (andb (isEmptyVarEnv tvs) (isEmptyVarEnv cvs)) (andb
                  (GHC.Core.TyCo.FVs.noFreeVarsOfType old_ty) (GHC.Core.TyCo.FVs.noFreeVarsOfType
                   old_w)) in
           let id1 := uniqAway in_scope old_id in
           let id2 :=
             if no_type_change : bool then id1 else
             updateIdTypeAndMult (GHC.Core.TyCo.Subst.substTyUnchecked subst) id1 in
           let mb_new_info := substIdInfo rec_subst id2 (idInfo id2) in
           let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
           let new_in_scope := extendInScopeSet in_scope new_id in
           let no_change := id1 == old_id in
           let new_env :=
             if no_change : bool then delVarEnv env old_id else
             extendVarEnv env old_id (Mk_Var new_id) in
           pair (GHC.Core.TyCo.Subst.Subst new_in_scope new_env tvs cvs) new_id
       end
  with substIdInfo (subst : GHC.Core.TyCo.Subst.Subst) (new_id : Id) (info
                     : IdInfo) : option IdInfo
    := let old_unf := realUnfoldingInfo info in
       let old_rules := ruleInfo info in
       let nothing_to_do :=
         andb (isEmptyRuleInfo old_rules) (negb (hasCoreUnfolding old_unf)) in
       if nothing_to_do : bool then None else
       Some (setUnfoldingInfo (setRuleInfo info (substRuleInfo subst new_id old_rules))
                              (substUnfolding subst old_unf))
  with substRuleInfo (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__ : Id) (arg_2__
                       : RuleInfo) : RuleInfo
    := match arg_0__, arg_1__, arg_2__ with
       | subst, new_id, RuleInfo rules rhs_fvs =>
           let subst_ru_fn := const (Id.idName new_id) in
           RuleInfo (map (substRule subst subst_ru_fn) rules) (substDVarSet subst rhs_fvs)
       end
  with substRule (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__
                   : (Name.Name -> Name.Name)) (arg_2__ : CoreRule) : CoreRule
    := match arg_0__, arg_1__, arg_2__ with
       | _, _, (BuiltinRule _ _ _ _ as rule) => rule
       | subst
       , subst_ru_fn
       , (Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
           let 'pair subst' bndrs' := substBndrs subst bndrs in
           match rule with
           | Rule ru_name_4__ ru_act_5__ ru_fn_6__ ru_rough_7__ ru_bndrs_8__ ru_args_9__
           ru_rhs_10__ ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__ =>
               Rule ru_name_4__ ru_act_5__ (if is_local : bool
                     then subst_ru_fn fn_name
                     else fn_name) ru_rough_7__ bndrs' (map (substExpr subst') args) (substExpr
                     subst' rhs) ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__
           | BuiltinRule _ _ _ _ =>
               GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
           end
       end
  with substRecBndrs {f : Type -> Type} `{Traversable f} (subst
                       : GHC.Core.TyCo.Subst.Subst) (bndrs : f Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                      f Id)%type
    := let 'pair new_subst new_bndrs := mapAccumL (substIdBndr (Datatypes.id
                                                                (GHC.Base.hs_string__ "rec-bndr")) (GHC.Err.error
                                                                Panic.someSDoc)) subst bndrs in
       pair new_subst new_bndrs for substIdBndr.

#[global] Definition substIdInfo
   : GHC.Core.TyCo.Subst.Subst -> Id -> IdInfo -> option IdInfo :=
  fix substExpr `{Util.HasDebugCallStack} (subst : GHC.Core.TyCo.Subst.Subst)
                (expr : CoreExpr) : CoreExpr
    := let go_alt :=
         fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | subst, Alt con bndrs rhs =>
               let 'pair subst' bndrs' := substBndrs subst bndrs in
               Alt con bndrs' (substExpr subst' rhs)
           end in
       let fix go arg_5__
         := match arg_5__ with
            | Mk_Var v => lookupIdSubst subst v
            | Mk_Type ty => Mk_Type (GHC.Core.TyCo.Subst.substTyUnchecked subst ty)
            | Mk_Coercion co => Mk_Coercion (GHC.Core.TyCo.Subst.substCo subst co)
            | Lit lit => Lit lit
            | App fun_ arg => App (go fun_) (go arg)
            | Cast e co => Cast (go e) (GHC.Core.TyCo.Subst.substCo subst co)
            | Lam bndr body =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Lam bndr' (substExpr subst' body)
            | Let bind body =>
                let 'pair subst' bind' := substBind subst bind in
                Let bind' (substExpr subst' body)
            | Case scrut bndr ty alts =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Case (go scrut) bndr' (GHC.Core.TyCo.Subst.substTyUnchecked subst ty) (map
                                                                                       (go_alt subst') alts)
            end in
       go expr
  with substBind `{Util.HasDebugCallStack} (arg_0__ : GHC.Core.TyCo.Subst.Subst)
                 (arg_1__ : CoreBind) : (GHC.Core.TyCo.Subst.Subst * CoreBind)%type
    := match arg_0__, arg_1__ with
       | subst, NonRec bndr rhs =>
           let 'pair subst' bndr' := substBndr subst bndr in
           pair subst' (NonRec bndr' (substExpr subst rhs))
       | subst, Rec pairs =>
           let 'pair bndrs rhss := unzip pairs in
           let 'pair subst' bndrs' := substRecBndrs subst bndrs in
           let rhss' := map (substExpr subst') rhss in pair subst' (Rec (zip bndrs' rhss'))
       end
  with substBndr (subst : GHC.Core.TyCo.Subst.Subst) (bndr : Var)
    : (GHC.Core.TyCo.Subst.Subst * Var)%type
    := substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr
  with substIdBndr (arg_0__ : String) (arg_1__ arg_2__
                     : GHC.Core.TyCo.Subst.Subst) (arg_3__ : Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                    Id)%type
    := match arg_0__, arg_1__, arg_2__, arg_3__ with
       | _doc
       , rec_subst
       , (GHC.Core.TyCo.Subst.Subst in_scope env tvs cvs as subst)
       , old_id =>
           let old_w := Id.idMult old_id in
           let old_ty := Id.idType old_id in
           let no_type_change :=
             orb (andb (isEmptyVarEnv tvs) (isEmptyVarEnv cvs)) (andb
                  (GHC.Core.TyCo.FVs.noFreeVarsOfType old_ty) (GHC.Core.TyCo.FVs.noFreeVarsOfType
                   old_w)) in
           let id1 := uniqAway in_scope old_id in
           let id2 :=
             if no_type_change : bool then id1 else
             updateIdTypeAndMult (GHC.Core.TyCo.Subst.substTyUnchecked subst) id1 in
           let mb_new_info := substIdInfo rec_subst id2 (idInfo id2) in
           let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
           let new_in_scope := extendInScopeSet in_scope new_id in
           let no_change := id1 == old_id in
           let new_env :=
             if no_change : bool then delVarEnv env old_id else
             extendVarEnv env old_id (Mk_Var new_id) in
           pair (GHC.Core.TyCo.Subst.Subst new_in_scope new_env tvs cvs) new_id
       end
  with substIdInfo (subst : GHC.Core.TyCo.Subst.Subst) (new_id : Id) (info
                     : IdInfo) : option IdInfo
    := let old_unf := realUnfoldingInfo info in
       let old_rules := ruleInfo info in
       let nothing_to_do :=
         andb (isEmptyRuleInfo old_rules) (negb (hasCoreUnfolding old_unf)) in
       if nothing_to_do : bool then None else
       Some (setUnfoldingInfo (setRuleInfo info (substRuleInfo subst new_id old_rules))
                              (substUnfolding subst old_unf))
  with substRuleInfo (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__ : Id) (arg_2__
                       : RuleInfo) : RuleInfo
    := match arg_0__, arg_1__, arg_2__ with
       | subst, new_id, RuleInfo rules rhs_fvs =>
           let subst_ru_fn := const (Id.idName new_id) in
           RuleInfo (map (substRule subst subst_ru_fn) rules) (substDVarSet subst rhs_fvs)
       end
  with substRule (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__
                   : (Name.Name -> Name.Name)) (arg_2__ : CoreRule) : CoreRule
    := match arg_0__, arg_1__, arg_2__ with
       | _, _, (BuiltinRule _ _ _ _ as rule) => rule
       | subst
       , subst_ru_fn
       , (Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
           let 'pair subst' bndrs' := substBndrs subst bndrs in
           match rule with
           | Rule ru_name_4__ ru_act_5__ ru_fn_6__ ru_rough_7__ ru_bndrs_8__ ru_args_9__
           ru_rhs_10__ ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__ =>
               Rule ru_name_4__ ru_act_5__ (if is_local : bool
                     then subst_ru_fn fn_name
                     else fn_name) ru_rough_7__ bndrs' (map (substExpr subst') args) (substExpr
                     subst' rhs) ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__
           | BuiltinRule _ _ _ _ =>
               GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
           end
       end
  with substRecBndrs {f : Type -> Type} `{Traversable f} (subst
                       : GHC.Core.TyCo.Subst.Subst) (bndrs : f Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                      f Id)%type
    := let 'pair new_subst new_bndrs := mapAccumL (substIdBndr (Datatypes.id
                                                                (GHC.Base.hs_string__ "rec-bndr")) (GHC.Err.error
                                                                Panic.someSDoc)) subst bndrs in
       pair new_subst new_bndrs for substIdInfo.

#[global] Definition substIdType : GHC.Core.TyCo.Subst.Subst -> Id -> Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (GHC.Core.TyCo.Subst.Subst _ _ tv_env cv_env as subst), id =>
        let old_w := varMult id in
        let old_ty := Id.idType id in
        if orb (andb (isEmptyVarEnv tv_env) (isEmptyVarEnv cv_env)) (andb
                (GHC.Core.TyCo.FVs.noFreeVarsOfType old_ty) (GHC.Core.TyCo.FVs.noFreeVarsOfType
                 old_w)) : bool
        then id else
        updateIdTypeAndMult (GHC.Core.TyCo.Subst.substTyUnchecked subst) id
    end.

#[global] Definition clone_id
   : GHC.Core.TyCo.Subst.Subst ->
     GHC.Core.TyCo.Subst.Subst ->
     (Id * Unique.Unique)%type -> (GHC.Core.TyCo.Subst.Subst * Id)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | rec_subst
    , (GHC.Core.TyCo.Subst.Subst in_scope idvs tvs cvs as subst)
    , pair old_id uniq =>
        let id1 := setVarUnique old_id uniq in
        let id2 := substIdType subst id1 in
        let new_id :=
          Id.maybeModifyIdInfo (substIdInfo rec_subst id2 (idInfo old_id)) id2 in
        let new_in_scope := extendInScopeSet in_scope new_id in
        let 'pair new_idvs new_cvs := pair (extendVarEnv idvs old_id (Mk_Var new_id))
                                           cvs in
        pair (GHC.Core.TyCo.Subst.Subst new_in_scope new_idvs tvs new_cvs) new_id
    end.

#[global] Definition cloneIdBndr
   : GHC.Core.TyCo.Subst.Subst ->
     UniqSupply.UniqSupply -> Id -> (GHC.Core.TyCo.Subst.Subst * Id)%type :=
  fun subst us old_id =>
    clone_id subst subst (pair old_id (UniqSupply.uniqFromSupply us)).

#[global] Definition cloneIdBndrs
   : GHC.Core.TyCo.Subst.Subst ->
     UniqSupply.UniqSupply ->
     list Id -> (GHC.Core.TyCo.Subst.Subst * list Id)%type :=
  fun subst us ids =>
    mapAccumL (clone_id subst) subst (zip ids (UniqSupply.uniqsFromSupply us)).

#[global] Definition cloneBndr
   : GHC.Core.TyCo.Subst.Subst ->
     Unique.Unique -> Var -> (GHC.Core.TyCo.Subst.Subst * Var)%type :=
  fun subst uniq v =>
    if isTyVar v : bool then GHC.Core.TyCo.Subst.cloneTyVarBndr subst v uniq else
    clone_id subst subst (pair v uniq).

#[global] Definition cloneBndrs {m : Type -> Type} `{UniqSupply.MonadUnique m}
   : GHC.Core.TyCo.Subst.Subst ->
     list Var -> m (GHC.Core.TyCo.Subst.Subst * list Var)%type :=
  fun subst vs =>
    UniqSupply.getUniquesM >>=
    (fun us =>
       pure (mapAccumL (fun arg_0__ arg_1__ =>
                          match arg_0__, arg_1__ with
                          | subst, pair v u => cloneBndr subst u v
                          end) subst (zip vs us))).

#[global] Definition cloneRecIdBndrs {m : Type -> Type} `{UniqSupply.MonadUnique
  m}
   : GHC.Core.TyCo.Subst.Subst ->
     list Id -> m (GHC.Core.TyCo.Subst.Subst * list Id)%type :=
  fun subst ids =>
    UniqSupply.getUniquesM >>=
    (fun us =>
       let 'pair subst' ids' := mapAccumL (clone_id (GHC.Err.error Panic.someSDoc))
                                  subst (zip ids us) in
       pure (pair subst' ids')).

#[global] Definition substUnfoldingSC
   : GHC.Core.TyCo.Subst.Subst -> Unfolding -> Unfolding :=
  fun subst unf =>
    if GHC.Core.TyCo.Subst.isEmptySubst subst : bool then unf else
    substUnfolding subst unf.

#[global] Definition substIdOcc : GHC.Core.TyCo.Subst.Subst -> Id -> Id :=
  fun subst v =>
    match lookupIdSubst subst v with
    | Mk_Var v' => v'
    | other => Panic.pprPanic (GHC.Base.hs_string__ "substIdOcc") (Panic.someSDoc)
    end.

#[global] Definition substRuleInfo
   : GHC.Core.TyCo.Subst.Subst -> Id -> RuleInfo -> RuleInfo :=
  fix substExpr `{Util.HasDebugCallStack} (subst : GHC.Core.TyCo.Subst.Subst)
                (expr : CoreExpr) : CoreExpr
    := let go_alt :=
         fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | subst, Alt con bndrs rhs =>
               let 'pair subst' bndrs' := substBndrs subst bndrs in
               Alt con bndrs' (substExpr subst' rhs)
           end in
       let fix go arg_5__
         := match arg_5__ with
            | Mk_Var v => lookupIdSubst subst v
            | Mk_Type ty => Mk_Type (GHC.Core.TyCo.Subst.substTyUnchecked subst ty)
            | Mk_Coercion co => Mk_Coercion (GHC.Core.TyCo.Subst.substCo subst co)
            | Lit lit => Lit lit
            | App fun_ arg => App (go fun_) (go arg)
            | Cast e co => Cast (go e) (GHC.Core.TyCo.Subst.substCo subst co)
            | Lam bndr body =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Lam bndr' (substExpr subst' body)
            | Let bind body =>
                let 'pair subst' bind' := substBind subst bind in
                Let bind' (substExpr subst' body)
            | Case scrut bndr ty alts =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Case (go scrut) bndr' (GHC.Core.TyCo.Subst.substTyUnchecked subst ty) (map
                                                                                       (go_alt subst') alts)
            end in
       go expr
  with substBind `{Util.HasDebugCallStack} (arg_0__ : GHC.Core.TyCo.Subst.Subst)
                 (arg_1__ : CoreBind) : (GHC.Core.TyCo.Subst.Subst * CoreBind)%type
    := match arg_0__, arg_1__ with
       | subst, NonRec bndr rhs =>
           let 'pair subst' bndr' := substBndr subst bndr in
           pair subst' (NonRec bndr' (substExpr subst rhs))
       | subst, Rec pairs =>
           let 'pair bndrs rhss := unzip pairs in
           let 'pair subst' bndrs' := substRecBndrs subst bndrs in
           let rhss' := map (substExpr subst') rhss in pair subst' (Rec (zip bndrs' rhss'))
       end
  with substBndr (subst : GHC.Core.TyCo.Subst.Subst) (bndr : Var)
    : (GHC.Core.TyCo.Subst.Subst * Var)%type
    := substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr
  with substIdBndr (arg_0__ : String) (arg_1__ arg_2__
                     : GHC.Core.TyCo.Subst.Subst) (arg_3__ : Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                    Id)%type
    := match arg_0__, arg_1__, arg_2__, arg_3__ with
       | _doc
       , rec_subst
       , (GHC.Core.TyCo.Subst.Subst in_scope env tvs cvs as subst)
       , old_id =>
           let old_w := Id.idMult old_id in
           let old_ty := Id.idType old_id in
           let no_type_change :=
             orb (andb (isEmptyVarEnv tvs) (isEmptyVarEnv cvs)) (andb
                  (GHC.Core.TyCo.FVs.noFreeVarsOfType old_ty) (GHC.Core.TyCo.FVs.noFreeVarsOfType
                   old_w)) in
           let id1 := uniqAway in_scope old_id in
           let id2 :=
             if no_type_change : bool then id1 else
             updateIdTypeAndMult (GHC.Core.TyCo.Subst.substTyUnchecked subst) id1 in
           let mb_new_info := substIdInfo rec_subst id2 (idInfo id2) in
           let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
           let new_in_scope := extendInScopeSet in_scope new_id in
           let no_change := id1 == old_id in
           let new_env :=
             if no_change : bool then delVarEnv env old_id else
             extendVarEnv env old_id (Mk_Var new_id) in
           pair (GHC.Core.TyCo.Subst.Subst new_in_scope new_env tvs cvs) new_id
       end
  with substIdInfo (subst : GHC.Core.TyCo.Subst.Subst) (new_id : Id) (info
                     : IdInfo) : option IdInfo
    := let old_unf := realUnfoldingInfo info in
       let old_rules := ruleInfo info in
       let nothing_to_do :=
         andb (isEmptyRuleInfo old_rules) (negb (hasCoreUnfolding old_unf)) in
       if nothing_to_do : bool then None else
       Some (setUnfoldingInfo (setRuleInfo info (substRuleInfo subst new_id old_rules))
                              (substUnfolding subst old_unf))
  with substRuleInfo (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__ : Id) (arg_2__
                       : RuleInfo) : RuleInfo
    := match arg_0__, arg_1__, arg_2__ with
       | subst, new_id, RuleInfo rules rhs_fvs =>
           let subst_ru_fn := const (Id.idName new_id) in
           RuleInfo (map (substRule subst subst_ru_fn) rules) (substDVarSet subst rhs_fvs)
       end
  with substRule (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__
                   : (Name.Name -> Name.Name)) (arg_2__ : CoreRule) : CoreRule
    := match arg_0__, arg_1__, arg_2__ with
       | _, _, (BuiltinRule _ _ _ _ as rule) => rule
       | subst
       , subst_ru_fn
       , (Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
           let 'pair subst' bndrs' := substBndrs subst bndrs in
           match rule with
           | Rule ru_name_4__ ru_act_5__ ru_fn_6__ ru_rough_7__ ru_bndrs_8__ ru_args_9__
           ru_rhs_10__ ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__ =>
               Rule ru_name_4__ ru_act_5__ (if is_local : bool
                     then subst_ru_fn fn_name
                     else fn_name) ru_rough_7__ bndrs' (map (substExpr subst') args) (substExpr
                     subst' rhs) ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__
           | BuiltinRule _ _ _ _ =>
               GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
           end
       end
  with substRecBndrs {f : Type -> Type} `{Traversable f} (subst
                       : GHC.Core.TyCo.Subst.Subst) (bndrs : f Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                      f Id)%type
    := let 'pair new_subst new_bndrs := mapAccumL (substIdBndr (Datatypes.id
                                                                (GHC.Base.hs_string__ "rec-bndr")) (GHC.Err.error
                                                                Panic.someSDoc)) subst bndrs in
       pair new_subst new_bndrs for substRuleInfo.

#[global] Definition substRule
   : GHC.Core.TyCo.Subst.Subst ->
     (Name.Name -> Name.Name) -> CoreRule -> CoreRule :=
  fix substExpr `{Util.HasDebugCallStack} (subst : GHC.Core.TyCo.Subst.Subst)
                (expr : CoreExpr) : CoreExpr
    := let go_alt :=
         fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | subst, Alt con bndrs rhs =>
               let 'pair subst' bndrs' := substBndrs subst bndrs in
               Alt con bndrs' (substExpr subst' rhs)
           end in
       let fix go arg_5__
         := match arg_5__ with
            | Mk_Var v => lookupIdSubst subst v
            | Mk_Type ty => Mk_Type (GHC.Core.TyCo.Subst.substTyUnchecked subst ty)
            | Mk_Coercion co => Mk_Coercion (GHC.Core.TyCo.Subst.substCo subst co)
            | Lit lit => Lit lit
            | App fun_ arg => App (go fun_) (go arg)
            | Cast e co => Cast (go e) (GHC.Core.TyCo.Subst.substCo subst co)
            | Lam bndr body =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Lam bndr' (substExpr subst' body)
            | Let bind body =>
                let 'pair subst' bind' := substBind subst bind in
                Let bind' (substExpr subst' body)
            | Case scrut bndr ty alts =>
                let 'pair subst' bndr' := substBndr subst bndr in
                Case (go scrut) bndr' (GHC.Core.TyCo.Subst.substTyUnchecked subst ty) (map
                                                                                       (go_alt subst') alts)
            end in
       go expr
  with substBind `{Util.HasDebugCallStack} (arg_0__ : GHC.Core.TyCo.Subst.Subst)
                 (arg_1__ : CoreBind) : (GHC.Core.TyCo.Subst.Subst * CoreBind)%type
    := match arg_0__, arg_1__ with
       | subst, NonRec bndr rhs =>
           let 'pair subst' bndr' := substBndr subst bndr in
           pair subst' (NonRec bndr' (substExpr subst rhs))
       | subst, Rec pairs =>
           let 'pair bndrs rhss := unzip pairs in
           let 'pair subst' bndrs' := substRecBndrs subst bndrs in
           let rhss' := map (substExpr subst') rhss in pair subst' (Rec (zip bndrs' rhss'))
       end
  with substBndr (subst : GHC.Core.TyCo.Subst.Subst) (bndr : Var)
    : (GHC.Core.TyCo.Subst.Subst * Var)%type
    := substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr
  with substIdBndr (arg_0__ : String) (arg_1__ arg_2__
                     : GHC.Core.TyCo.Subst.Subst) (arg_3__ : Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                    Id)%type
    := match arg_0__, arg_1__, arg_2__, arg_3__ with
       | _doc
       , rec_subst
       , (GHC.Core.TyCo.Subst.Subst in_scope env tvs cvs as subst)
       , old_id =>
           let old_w := Id.idMult old_id in
           let old_ty := Id.idType old_id in
           let no_type_change :=
             orb (andb (isEmptyVarEnv tvs) (isEmptyVarEnv cvs)) (andb
                  (GHC.Core.TyCo.FVs.noFreeVarsOfType old_ty) (GHC.Core.TyCo.FVs.noFreeVarsOfType
                   old_w)) in
           let id1 := uniqAway in_scope old_id in
           let id2 :=
             if no_type_change : bool then id1 else
             updateIdTypeAndMult (GHC.Core.TyCo.Subst.substTyUnchecked subst) id1 in
           let mb_new_info := substIdInfo rec_subst id2 (idInfo id2) in
           let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
           let new_in_scope := extendInScopeSet in_scope new_id in
           let no_change := id1 == old_id in
           let new_env :=
             if no_change : bool then delVarEnv env old_id else
             extendVarEnv env old_id (Mk_Var new_id) in
           pair (GHC.Core.TyCo.Subst.Subst new_in_scope new_env tvs cvs) new_id
       end
  with substIdInfo (subst : GHC.Core.TyCo.Subst.Subst) (new_id : Id) (info
                     : IdInfo) : option IdInfo
    := let old_unf := realUnfoldingInfo info in
       let old_rules := ruleInfo info in
       let nothing_to_do :=
         andb (isEmptyRuleInfo old_rules) (negb (hasCoreUnfolding old_unf)) in
       if nothing_to_do : bool then None else
       Some (setUnfoldingInfo (setRuleInfo info (substRuleInfo subst new_id old_rules))
                              (substUnfolding subst old_unf))
  with substRuleInfo (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__ : Id) (arg_2__
                       : RuleInfo) : RuleInfo
    := match arg_0__, arg_1__, arg_2__ with
       | subst, new_id, RuleInfo rules rhs_fvs =>
           let subst_ru_fn := const (Id.idName new_id) in
           RuleInfo (map (substRule subst subst_ru_fn) rules) (substDVarSet subst rhs_fvs)
       end
  with substRule (arg_0__ : GHC.Core.TyCo.Subst.Subst) (arg_1__
                   : (Name.Name -> Name.Name)) (arg_2__ : CoreRule) : CoreRule
    := match arg_0__, arg_1__, arg_2__ with
       | _, _, (BuiltinRule _ _ _ _ as rule) => rule
       | subst
       , subst_ru_fn
       , (Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
           let 'pair subst' bndrs' := substBndrs subst bndrs in
           match rule with
           | Rule ru_name_4__ ru_act_5__ ru_fn_6__ ru_rough_7__ ru_bndrs_8__ ru_args_9__
           ru_rhs_10__ ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__ =>
               Rule ru_name_4__ ru_act_5__ (if is_local : bool
                     then subst_ru_fn fn_name
                     else fn_name) ru_rough_7__ bndrs' (map (substExpr subst') args) (substExpr
                     subst' rhs) ru_auto_11__ ru_origin_12__ ru_orphan_13__ ru_local_14__
           | BuiltinRule _ _ _ _ =>
               GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
           end
       end
  with substRecBndrs {f : Type -> Type} `{Traversable f} (subst
                       : GHC.Core.TyCo.Subst.Subst) (bndrs : f Id) : (GHC.Core.TyCo.Subst.Subst *
                                                                      f Id)%type
    := let 'pair new_subst new_bndrs := mapAccumL (substIdBndr (Datatypes.id
                                                                (GHC.Base.hs_string__ "rec-bndr")) (GHC.Err.error
                                                                Panic.someSDoc)) subst bndrs in
       pair new_subst new_bndrs for substRule.

#[global] Definition substRulesForImportedIds
   : GHC.Core.TyCo.Subst.Subst -> list CoreRule -> list CoreRule :=
  fun subst rules =>
    let not_needed :=
      fun name =>
        Panic.pprPanic (GHC.Base.hs_string__ "substRulesForImportedIds")
        (Panic.someSDoc) in
    map (substRule subst not_needed) rules.

#[global] Definition substTickish
   : GHC.Core.TyCo.Subst.Subst ->
     GHC.Types.Tickish.CoreTickish -> GHC.Types.Tickish.CoreTickish :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | subst, GHC.Types.Tickish.Breakpoint ext n ids modl =>
        let do_one := CoreUtils.getIdFromTrivialExpr_maybe ∘ lookupIdSubst subst in
        GHC.Types.Tickish.Breakpoint ext n (Data.Maybe.mapMaybe do_one ids) modl
    | _subst, other => other
    end.

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
     GHC.Core.TyCo.Subst.Subst GHC.Core.TyCo.Subst.cloneTyVarBndr
     GHC.Core.TyCo.Subst.emptySubst GHC.Core.TyCo.Subst.extendCvSubst
     GHC.Core.TyCo.Subst.extendTvSubst GHC.Core.TyCo.Subst.isEmptySubst
     GHC.Core.TyCo.Subst.substCo GHC.Core.TyCo.Subst.substTyUnchecked GHC.Err.error
     GHC.Types.Tickish.Breakpoint GHC.Types.Tickish.CoreTickish Id.idMult Id.idName
     Id.idType Id.maybeModifyIdInfo Maybes.orElse Name.Name Panic.assertPpr
     Panic.pprPanic Panic.someSDoc UniqSupply.MonadUnique UniqSupply.UniqSupply
     UniqSupply.getUniquesM UniqSupply.uniqFromSupply UniqSupply.uniqsFromSupply
     Unique.Unique Util.HasDebugCallStack
*)
