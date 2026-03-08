(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Core.
Require Data.Foldable.
Require Data.Tuple.
Require FV.
Require GHC.Base.
Require GHC.Core.TyCo.FVs.
Require GHC.List.
Require HsToCoq.Err.
Require Id.
Require Lists.List.
Require Maybes.
Require NameSet.
Require NestedRecursionHelpers.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive RuleFVsFrom : Type :=
  | LhsOnly : RuleFVsFrom
  | RhsOnly : RuleFVsFrom
  | BothSides : RuleFVsFrom.

#[global] Definition FVAnn :=
  Core.DVarSet%type.

#[global] Definition CoreExprWithFVs' :=
  (Core.AnnExpr' Core.Id FVAnn)%type.

#[global] Definition CoreExprWithFVs :=
  (Core.AnnExpr Core.Id FVAnn)%type.

#[global] Definition CoreBindWithFVs :=
  (Core.AnnBind Core.Id FVAnn)%type.

#[global] Definition CoreAltWithFVs :=
  (Core.AnnAlt Core.Id FVAnn)%type.

Instance Default__RuleFVsFrom : HsToCoq.Err.Default RuleFVsFrom :=
  HsToCoq.Err.Build_Default _ LhsOnly.

(* Converted value declarations: *)

#[global] Definition varTypeTyCoFVs : Core.Var -> FV.FV :=
  fun var =>
    let mult_fvs :=
      match Core.varMultMaybe var with
      | Some mult => GHC.Core.TyCo.FVs.tyCoFVsOfType mult
      | None => FV.emptyFV
      end in
    FV.unionFV (GHC.Core.TyCo.FVs.tyCoFVsOfType (Core.varType var)) mult_fvs.

#[global] Definition addBndr : Core.CoreBndr -> FV.FV -> FV.FV :=
  fun bndr fv fv_cand in_scope acc =>
    (FV.unionFV (varTypeTyCoFVs bndr) (FV.delFV bndr fv)) fv_cand in_scope acc.

#[global] Definition addBndrs : list Core.CoreBndr -> FV.FV -> FV.FV :=
  fun bndrs fv => Data.Foldable.foldr addBndr fv bndrs.

#[global] Definition idRuleFVs : Core.Id -> FV.FV :=
  fun id => FV.emptyFV.

#[global] Definition stableUnfoldingFVs : Core.Unfolding -> option FV.FV :=
  fun '(_other) => None.

#[global] Definition idUnfoldingFVs : Core.Id -> FV.FV :=
  fun id => Maybes.orElse (stableUnfoldingFVs (Id.realIdUnfolding id)) FV.emptyFV.

#[global] Definition bndrRuleAndUnfoldingFVs : Core.Id -> FV.FV :=
  fun id =>
    if Core.isId id : bool then FV.unionFV (idRuleFVs id) (idUnfoldingFVs id) else
    FV.emptyFV.

Fixpoint expr_fvs `(arg_0__ : Core.CoreExpr) arg_1__ arg_2__ arg_3__
  := match arg_0__, arg_1__, arg_2__, arg_3__ with
     | Core.Mk_Type ty, fv_cand, in_scope, acc =>
         GHC.Core.TyCo.FVs.tyCoFVsOfType ty fv_cand in_scope acc
     | Core.Mk_Coercion co, fv_cand, in_scope, acc =>
         GHC.Core.TyCo.FVs.tyCoFVsOfCo co fv_cand in_scope acc
     | Core.Mk_Var var, fv_cand, in_scope, acc => FV.unitFV var fv_cand in_scope acc
     | Core.Lit _, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
     | Core.App fun_ arg, fv_cand, in_scope, acc =>
         (FV.unionFV (expr_fvs fun_) (expr_fvs arg)) fv_cand in_scope acc
     | Core.Lam bndr body, fv_cand, in_scope, acc =>
         addBndr bndr (expr_fvs body) fv_cand in_scope acc
     | Core.Cast expr co, fv_cand, in_scope, acc =>
         (FV.unionFV (expr_fvs expr) (GHC.Core.TyCo.FVs.tyCoFVsOfCo co)) fv_cand in_scope
         acc
     | Core.Case scrut bndr ty alts, fv_cand, in_scope, acc =>
         let alt_fvs :=
           fun '(Core.Mk_Alt _ bndrs rhs) => addBndrs bndrs (expr_fvs rhs) in
         (FV.unionFV (FV.unionFV (expr_fvs scrut) (GHC.Core.TyCo.FVs.tyCoFVsOfType ty))
                     (addBndr bndr (FV.unionsFV (Lists.List.map alt_fvs alts)))) fv_cand in_scope acc
     | Core.Let (Core.NonRec bndr rhs) body, fv_cand, in_scope, acc =>
         (FV.unionFV (let 'pair bndr rhs := pair bndr rhs in
                      FV.unionFV (expr_fvs rhs) (bndrRuleAndUnfoldingFVs bndr)) (addBndr bndr
                      (expr_fvs body))) fv_cand in_scope acc
     | Core.Let (Core.Rec pairs) body, fv_cand, in_scope, acc =>
         addBndrs (GHC.Base.map Data.Tuple.fst pairs) (FV.unionFV (FV.unionsFV
                                                                   (Lists.List.map (fun '(pair bndr rhs) =>
                                                                                      FV.unionFV (expr_fvs rhs)
                                                                                                 (bndrRuleAndUnfoldingFVs
                                                                                                  bndr)) pairs))
                                                                  (expr_fvs body)) fv_cand in_scope acc
     end.

#[global] Definition exprFVs : Core.CoreExpr -> FV.FV :=
  FV.filterFV Core.isLocalVar GHC.Base.∘ expr_fvs.

#[global] Definition exprFreeVars : Core.CoreExpr -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprFVs.

#[global] Definition exprFreeVarsDSet : Core.CoreExpr -> Core.DVarSet :=
  FV.fvDVarSet GHC.Base.∘ exprFVs.

#[global] Definition exprFreeVarsList : Core.CoreExpr -> list Core.Var :=
  FV.fvVarList GHC.Base.∘ exprFVs.

#[global] Definition exprSomeFreeVars
   : FV.InterestingVarFun -> Core.CoreExpr -> Core.VarSet :=
  fun fv_cand e => FV.fvVarSet (FV.filterFV fv_cand (expr_fvs e)).

#[global] Definition exprFreeIds : Core.CoreExpr -> Core.IdSet :=
  exprSomeFreeVars Core.isLocalId.

#[global] Definition exprsSomeFreeVars
   : FV.InterestingVarFun -> list Core.CoreExpr -> Core.VarSet :=
  fun fv_cand es => FV.fvVarSet (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs es)).

#[global] Definition exprsFreeIds : list Core.CoreExpr -> Core.IdSet :=
  exprsSomeFreeVars Core.isLocalId.

#[global] Definition exprSomeFreeVarsDSet
   : FV.InterestingVarFun -> Core.CoreExpr -> Core.DVarSet :=
  fun fv_cand e => FV.fvDVarSet (FV.filterFV fv_cand (expr_fvs e)).

#[global] Definition exprFreeIdsDSet : Core.CoreExpr -> Core.DIdSet :=
  exprSomeFreeVarsDSet Core.isLocalId.

#[global] Definition exprSomeFreeVarsList
   : FV.InterestingVarFun -> Core.CoreExpr -> list Core.Var :=
  fun fv_cand e => FV.fvVarList (FV.filterFV fv_cand (expr_fvs e)).

#[global] Definition exprFreeIdsList : Core.CoreExpr -> list Core.Id :=
  exprSomeFreeVarsList Core.isLocalId.

#[global] Definition exprsSomeFreeVarsDSet
   : FV.InterestingVarFun -> list Core.CoreExpr -> Core.DVarSet :=
  fun fv_cand e => FV.fvDVarSet (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs e)).

#[global] Definition exprsFreeIdsDSet : list Core.CoreExpr -> Core.DIdSet :=
  exprsSomeFreeVarsDSet Core.isLocalId.

#[global] Definition exprsSomeFreeVarsList
   : FV.InterestingVarFun -> list Core.CoreExpr -> list Core.Var :=
  fun fv_cand es =>
    FV.fvVarList (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs es)).

#[global] Definition exprsFreeIdsList : list Core.CoreExpr -> list Core.Id :=
  exprsSomeFreeVarsList Core.isLocalId.

#[global] Definition exprsFVs : list Core.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV exprFVs exprs.

#[global] Definition exprsFreeVars : list Core.CoreExpr -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprsFVs.

#[global] Definition exprsFreeVarsList : list Core.CoreExpr -> list Core.Var :=
  FV.fvVarList GHC.Base.∘ exprsFVs.

#[global] Definition rhs_fvs : (Core.Id * Core.CoreExpr)%type -> FV.FV :=
  fun '(pair bndr rhs) =>
    FV.unionFV (expr_fvs rhs) (bndrRuleAndUnfoldingFVs bndr).

#[global] Definition bindFreeVars : Core.CoreBind -> Core.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.NonRec b r =>
        FV.fvVarSet (FV.filterFV Core.isLocalVar (rhs_fvs (pair b r)))
    | Core.Rec prs =>
        FV.fvVarSet (FV.filterFV Core.isLocalVar (addBndrs (GHC.Base.map Data.Tuple.fst
                                                            prs) (FV.mapUnionFV rhs_fvs prs)))
    end.

#[global] Definition exprs_fvs : list Core.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV expr_fvs exprs.

(* Skipping definition `CoreFVs.tickish_fvs' *)

(* Skipping definition `CoreFVs.exprOrphNames' *)

(* Skipping definition `CoreFVs.exprsOrphNames' *)

(* Skipping definition `CoreFVs.orphNamesOfTyCon' *)

(* Skipping definition `CoreFVs.orphNamesOfType' *)

#[global] Definition orphNamesOfThings {a}
   : (a -> NameSet.NameSet) -> list a -> NameSet.NameSet :=
  fun f =>
    Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ f) NameSet.emptyNameSet.

(* Skipping definition `CoreFVs.orphNamesOfTypes' *)

(* Skipping definition `CoreFVs.orphNamesOfMCo' *)

(* Skipping definition `CoreFVs.orphNamesOfCo' *)

(* Skipping definition `CoreFVs.orphNamesOfProv' *)

(* Skipping definition `CoreFVs.orphNamesOfCos' *)

(* Skipping definition `CoreFVs.orphNamesOfCoCon' *)

(* Skipping definition `CoreFVs.orphNamesOfCoAxBranches' *)

(* Skipping definition `CoreFVs.orphNamesOfCoAxBranch' *)

(* Skipping definition `CoreFVs.orphNamesOfAxiomLHS' *)

(* Skipping definition `CoreFVs.orph_names_of_fun_ty_con' *)

#[global] Definition ruleFVs : RuleFVsFrom -> Core.CoreRule -> FV.FV :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Core.BuiltinRule _ _ _ _ => FV.emptyFV
    | from, Core.Rule _ _ _do_not_include _ bndrs args rhs _ _ _ _ =>
        let exprs :=
          match from with
          | LhsOnly => args
          | RhsOnly => cons rhs nil
          | BothSides => cons rhs args
          end in
        FV.filterFV Core.isLocalVar (addBndrs bndrs (exprs_fvs exprs))
    end.

#[global] Definition rulesFVs : RuleFVsFrom -> list Core.CoreRule -> FV.FV :=
  fun from => FV.mapUnionFV (ruleFVs from).

#[global] Definition ruleRhsFreeVars : Core.CoreRule -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ ruleFVs RhsOnly.

#[global] Definition rulesRhsFreeIds : list Core.CoreRule -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ (FV.filterFV Core.isLocalId GHC.Base.∘ rulesFVs RhsOnly).

#[global] Definition ruleLhsFreeIds : Core.CoreRule -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ (FV.filterFV Core.isLocalId GHC.Base.∘ ruleFVs LhsOnly).

#[global] Definition ruleLhsFreeIdsList : Core.CoreRule -> list Core.Var :=
  FV.fvVarList GHC.Base.∘ (FV.filterFV Core.isLocalId GHC.Base.∘ ruleFVs LhsOnly).

#[global] Definition ruleFreeVars : Core.CoreRule -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ ruleFVs BothSides.

#[global] Definition rulesFreeVarsDSet : list Core.CoreRule -> Core.DVarSet :=
  fun rules => FV.fvDVarSet (rulesFVs BothSides rules).

#[global] Definition rulesFreeVars : list Core.CoreRule -> Core.VarSet :=
  fun rules => FV.fvVarSet (rulesFVs BothSides rules).

(* Skipping definition `CoreFVs.mkRuleInfo' *)

#[global] Definition freeVarsOf : CoreExprWithFVs -> Core.DIdSet :=
  fun '(pair fvs _) => fvs.

#[global] Definition freeVarsOfAnn : FVAnn -> Core.DIdSet :=
  fun fvs => fvs.

#[global] Definition aFreeVar : Core.Var -> Core.DVarSet :=
  Core.unitDVarSet.

#[global] Definition unionFVs : Core.DVarSet -> Core.DVarSet -> Core.DVarSet :=
  Core.unionDVarSet.

#[global] Definition unionFVss : list Core.DVarSet -> Core.DVarSet :=
  Core.unionDVarSets.

#[global] Definition dVarTypeTyCoVars : Core.Var -> Core.DTyCoVarSet :=
  fun var => FV.fvDVarSet (varTypeTyCoFVs var).

#[global] Definition delBinderFV : Core.Var -> Core.DVarSet -> Core.DVarSet :=
  fun b s => unionFVs (Core.delDVarSet s b) (dVarTypeTyCoVars b).

#[global] Definition delBindersFV
   : list Core.Var -> Core.DVarSet -> Core.DVarSet :=
  fun bs fvs => Data.Foldable.foldr delBinderFV fvs bs.

#[global] Definition varTypeTyCoVars : Core.Var -> Core.TyCoVarSet :=
  fun var => FV.fvVarSet (varTypeTyCoFVs var).

#[global] Definition idFVs : Core.Id -> FV.FV :=
  fun id => FV.unionFV (varTypeTyCoFVs id) (bndrRuleAndUnfoldingFVs id).

#[global] Definition idFreeVars : Core.Id -> Core.VarSet :=
  fun id => FV.fvVarSet (idFVs id).

#[global] Definition dIdFreeVars : Core.Id -> Core.DVarSet :=
  fun id => FV.fvDVarSet (idFVs id).

#[global] Definition bndrRuleAndUnfoldingVarsDSet : Core.Id -> Core.DVarSet :=
  fun id => FV.fvDVarSet (bndrRuleAndUnfoldingFVs id).

#[global] Definition bndrRuleAndUnfoldingIds : Core.Id -> Core.IdSet :=
  fun id => FV.fvVarSet (FV.filterFV Core.isId (bndrRuleAndUnfoldingFVs id)).

#[global] Definition idRuleVars : Core.Id -> Core.VarSet :=
  fun id => FV.fvVarSet (idRuleFVs id).

#[global] Definition idUnfoldingVars : Core.Id -> Core.VarSet :=
  fun id => FV.fvVarSet (idUnfoldingFVs id).

(* Skipping definition `CoreFVs.stableUnfoldingVars' *)

#[global] Definition freeVarsBind
   : Core.CoreBind -> Core.DVarSet -> (CoreBindWithFVs * Core.DVarSet)%type :=
  fix freeVars (arg_0__ : Core.CoreExpr) : CoreExprWithFVs
    := match arg_0__ with
       | Core.Mk_Var v =>
           let ty_fvs := dVarTypeTyCoVars v in
           let mult_vars := GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet (Core.varMult v) in
           if Core.isLocalVar v : bool
           then pair (unionFVs (unionFVs (aFreeVar v) ty_fvs) mult_vars) (Core.AnnVar
                      v) else
           pair Core.emptyDVarSet (Core.AnnVar v)
       | Core.Lit lit => pair Core.emptyDVarSet (Core.AnnLit lit)
       | Core.Lam b body =>
           let b_ty := Id.idType b in
           let b_fvs := GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet b_ty in
           let '(pair body_fvs _ as body') := freeVars body in
           pair (unionFVs b_fvs (delBinderFV b body_fvs)) (Core.AnnLam b body')
       | Core.App fun_ arg =>
           let arg' := freeVars arg in
           let fun' := freeVars fun_ in
           pair (unionFVs (freeVarsOf fun') (freeVarsOf arg')) (Core.AnnApp fun' arg')
       | Core.Case scrut bndr ty alts =>
           let fv_alt :=
             fun '(Core.Mk_Alt con args rhs) =>
               let rhs2 := freeVars rhs in
               pair (delBindersFV args (freeVarsOf rhs2)) (Core.Mk_AnnAlt con args rhs2) in
           let 'pair alts_fvs_s alts2 := NestedRecursionHelpers.mapAndUnzipFix fv_alt
                                           alts in
           let alts_fvs := unionFVss alts_fvs_s in
           let scrut2 := freeVars scrut in
           pair (unionFVs (unionFVs (delBinderFV bndr alts_fvs) (freeVarsOf scrut2))
                          (GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet ty)) (Core.AnnCase scrut2 bndr ty alts2)
       | Core.Let bind body =>
           let body2 := freeVars body in
           let 'pair bind2 bind_fvs := freeVarsBind bind (freeVarsOf body2) in
           pair bind_fvs (Core.AnnLet bind2 body2)
       | Core.Cast expr co =>
           let cfvs := GHC.Core.TyCo.FVs.tyCoVarsOfCoDSet co in
           let expr2 := freeVars expr in
           pair (unionFVs (freeVarsOf expr2) cfvs) (Core.AnnCast expr2 (pair cfvs co))
       | Core.Mk_Type ty =>
           pair (GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet ty) (Core.AnnType ty)
       | Core.Mk_Coercion co =>
           pair (GHC.Core.TyCo.FVs.tyCoVarsOfCoDSet co) (Core.AnnCoercion co)
       end
  with freeVarsBind (arg_0__ : Core.CoreBind) (arg_1__ : Core.DVarSet)
    : (CoreBindWithFVs * Core.DVarSet)%type
    := match arg_0__, arg_1__ with
       | Core.NonRec binder rhs, body_fvs =>
           let body_fvs2 := delBinderFV binder body_fvs in
           let rhs2 := freeVars rhs in
           pair (Core.AnnNonRec binder rhs2) (unionFVs (unionFVs (freeVarsOf rhs2)
                                                                 body_fvs2) (bndrRuleAndUnfoldingVarsDSet binder))
       | Core.Rec binds, body_fvs =>
           let 'pair binders rhss := GHC.List.unzip binds in
           let rhss2 := GHC.Base.map (freeVars GHC.Base.∘ snd) binds in
           let rhs_body_fvs :=
             Data.Foldable.foldr (unionFVs GHC.Base.∘ freeVarsOf) body_fvs rhss2 in
           let binders_fvs :=
             FV.fvDVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs binders) in
           let all_fvs := unionFVs rhs_body_fvs binders_fvs in
           pair (Core.AnnRec (GHC.List.zip binders rhss2)) (delBindersFV binders all_fvs)
       end for freeVarsBind.

#[global] Definition freeVars : Core.CoreExpr -> CoreExprWithFVs :=
  fix freeVars (arg_0__ : Core.CoreExpr) : CoreExprWithFVs
    := match arg_0__ with
       | Core.Mk_Var v =>
           let ty_fvs := dVarTypeTyCoVars v in
           let mult_vars := GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet (Core.varMult v) in
           if Core.isLocalVar v : bool
           then pair (unionFVs (unionFVs (aFreeVar v) ty_fvs) mult_vars) (Core.AnnVar
                      v) else
           pair Core.emptyDVarSet (Core.AnnVar v)
       | Core.Lit lit => pair Core.emptyDVarSet (Core.AnnLit lit)
       | Core.Lam b body =>
           let b_ty := Id.idType b in
           let b_fvs := GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet b_ty in
           let '(pair body_fvs _ as body') := freeVars body in
           pair (unionFVs b_fvs (delBinderFV b body_fvs)) (Core.AnnLam b body')
       | Core.App fun_ arg =>
           let arg' := freeVars arg in
           let fun' := freeVars fun_ in
           pair (unionFVs (freeVarsOf fun') (freeVarsOf arg')) (Core.AnnApp fun' arg')
       | Core.Case scrut bndr ty alts =>
           let fv_alt :=
             fun '(Core.Mk_Alt con args rhs) =>
               let rhs2 := freeVars rhs in
               pair (delBindersFV args (freeVarsOf rhs2)) (Core.Mk_AnnAlt con args rhs2) in
           let 'pair alts_fvs_s alts2 := NestedRecursionHelpers.mapAndUnzipFix fv_alt
                                           alts in
           let alts_fvs := unionFVss alts_fvs_s in
           let scrut2 := freeVars scrut in
           pair (unionFVs (unionFVs (delBinderFV bndr alts_fvs) (freeVarsOf scrut2))
                          (GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet ty)) (Core.AnnCase scrut2 bndr ty alts2)
       | Core.Let bind body =>
           let body2 := freeVars body in
           let 'pair bind2 bind_fvs := freeVarsBind bind (freeVarsOf body2) in
           pair bind_fvs (Core.AnnLet bind2 body2)
       | Core.Cast expr co =>
           let cfvs := GHC.Core.TyCo.FVs.tyCoVarsOfCoDSet co in
           let expr2 := freeVars expr in
           pair (unionFVs (freeVarsOf expr2) cfvs) (Core.AnnCast expr2 (pair cfvs co))
       | Core.Mk_Type ty =>
           pair (GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet ty) (Core.AnnType ty)
       | Core.Mk_Coercion co =>
           pair (GHC.Core.TyCo.FVs.tyCoVarsOfCoDSet co) (Core.AnnCoercion co)
       end
  with freeVarsBind (arg_0__ : Core.CoreBind) (arg_1__ : Core.DVarSet)
    : (CoreBindWithFVs * Core.DVarSet)%type
    := match arg_0__, arg_1__ with
       | Core.NonRec binder rhs, body_fvs =>
           let body_fvs2 := delBinderFV binder body_fvs in
           let rhs2 := freeVars rhs in
           pair (Core.AnnNonRec binder rhs2) (unionFVs (unionFVs (freeVarsOf rhs2)
                                                                 body_fvs2) (bndrRuleAndUnfoldingVarsDSet binder))
       | Core.Rec binds, body_fvs =>
           let 'pair binders rhss := GHC.List.unzip binds in
           let rhss2 := GHC.Base.map (freeVars GHC.Base.∘ snd) binds in
           let rhs_body_fvs :=
             Data.Foldable.foldr (unionFVs GHC.Base.∘ freeVarsOf) body_fvs rhss2 in
           let binders_fvs :=
             FV.fvDVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs binders) in
           let all_fvs := unionFVs rhs_body_fvs binders_fvs in
           pair (Core.AnnRec (GHC.List.zip binders rhss2)) (delBindersFV binders all_fvs)
       end for freeVars.

(* External variables:
     None Some bool cons list nil op_zt__ option pair snd Core.AnnAlt Core.AnnApp
     Core.AnnBind Core.AnnCase Core.AnnCast Core.AnnCoercion Core.AnnExpr
     Core.AnnExpr' Core.AnnLam Core.AnnLet Core.AnnLit Core.AnnNonRec Core.AnnRec
     Core.AnnType Core.AnnVar Core.App Core.BuiltinRule Core.Case Core.Cast
     Core.CoreBind Core.CoreBndr Core.CoreExpr Core.CoreRule Core.DIdSet
     Core.DTyCoVarSet Core.DVarSet Core.Id Core.IdSet Core.Lam Core.Let Core.Lit
     Core.Mk_Alt Core.Mk_AnnAlt Core.Mk_Coercion Core.Mk_Type Core.Mk_Var Core.NonRec
     Core.Rec Core.Rule Core.TyCoVarSet Core.Unfolding Core.Var Core.VarSet
     Core.delDVarSet Core.emptyDVarSet Core.isId Core.isLocalId Core.isLocalVar
     Core.unionDVarSet Core.unionDVarSets Core.unitDVarSet Core.varMult
     Core.varMultMaybe Core.varType Data.Foldable.foldr Data.Tuple.fst FV.FV
     FV.InterestingVarFun FV.delFV FV.emptyFV FV.filterFV FV.fvDVarSet FV.fvVarList
     FV.fvVarSet FV.mapUnionFV FV.unionFV FV.unionsFV FV.unitFV GHC.Base.map
     GHC.Base.op_z2218U__ GHC.Core.TyCo.FVs.tyCoFVsOfCo
     GHC.Core.TyCo.FVs.tyCoFVsOfType GHC.Core.TyCo.FVs.tyCoVarsOfCoDSet
     GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet GHC.List.unzip GHC.List.zip
     HsToCoq.Err.Build_Default HsToCoq.Err.Default Id.idType Id.realIdUnfolding
     Lists.List.map Maybes.orElse NameSet.NameSet NameSet.emptyNameSet
     NameSet.unionNameSet NestedRecursionHelpers.mapAndUnzipFix
*)
