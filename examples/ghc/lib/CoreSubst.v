(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Import Core.
Require Import GHC.Base.
Require Panic.
Require Util.

(* No type declarations to convert. *)

(* Midamble *)

(* GHC 9.10: Subst is now a concrete inductive type in Core.v
   (merged from GHC.Core.TyCo.Subst). This midamble provides:
   1. Projection functions for Subst
   2. Structural lemmas (eta, injectivity)
   3. Type/coercion substitution (identity, since types are axiomatized)
   4. Mutually recursive substExpr_/substBind_ (need Fixpoint...with...)
   All other functions are either auto-generated or redefined in edits. *)

Require Import Core.
Require Import AxiomatizedTypes.
Require Import Util.
Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import GHC.List.
Require Import Data.Traversable.
Require Import Data.Tuple.
Require Import Id.
Require Import Panic.
Require Import Coq.Lists.List.
Require Import Datatypes.

(* === Projections for the concrete Subst type === *)

Definition substInScope (s : Subst) : InScopeSet :=
  match s with Mk_Subst is _ _ _ => is end.
Definition substIdEnv (s : Subst) : IdSubstEnv :=
  match s with Mk_Subst _ ie _ _ => ie end.

(* Constructor/projection round trips — now provable *)
Lemma substInScope_Mk_Subst : forall is ie te ce,
  substInScope (Mk_Subst is ie te ce) = is.
Proof. reflexivity. Qed.
Lemma substIdEnv_Mk_Subst : forall is ie te ce,
  substIdEnv (Mk_Subst is ie te ce) = ie.
Proof. reflexivity. Qed.

(* Eta: every Subst is constructed from its projections *)
Lemma Subst_eta : forall s,
  s = Mk_Subst (substInScope s) (substIdEnv s) tt tt.
Proof. intros [is ie [] []]. reflexivity. Qed.

(* Injectivity of Mk_Subst *)
Lemma Mk_Subst_injective : forall is1 ie1 is2 ie2 te1 ce1 te2 ce2,
  Mk_Subst is1 ie1 te1 ce1 = Mk_Subst is2 ie2 te2 ce2 ->
  is1 = is2 /\ ie1 = ie2.
Proof. intros. inversion H. auto. Qed.

(* Type/coercion substitution: identity since types are axiomatized *)
Definition substTyUnchecked (_ : Subst)
  (ty : AxiomatizedTypes.Type_) : AxiomatizedTypes.Type_ := ty.
Definition substCo (_ : Subst)
  (co : AxiomatizedTypes.Coercion) : AxiomatizedTypes.Coercion := co.

(* isEmptySubst: GHC version in TyCoSubst calls isEmptyVarEnv on tvs/cvs
   (unit types); simplified since only IdSubstEnv matters *)
Definition isEmptySubst (s : Subst) : bool :=
  isEmptyVarEnv (substIdEnv s).

(* mkOpenSubst: uses list comprehensions + type/coercion filtering;
   kept in midamble since edits parser doesn't support tick patterns *)
Definition mkOpenSubst (in_scope : InScopeSet)
  (pairs : list (Var * CoreArg)%type) : Subst :=
  Mk_Subst in_scope
    (mkVarEnv (Coq.Lists.List.flat_map
      (fun '(pair id e) =>
        if isId id then cons (pair id e) nil else nil) pairs))
    tt tt.

(* substIdInfo: simplified since types/coercions are axiomatized.
   Returns None (no info change needed). *)
Definition substIdInfo (_ : Subst) (_ : Id)
  (_ : IdInfo) : option IdInfo := None.

(* substIdBndr: capture-avoiding variable freshening.
   Simplified: no type change (TvSubstEnv = CvSubstEnv = unit). *)
Definition substIdBndr (doc : String)
  (rec_subst subst : Subst) (old_id : Id)
  : (Subst * Id)%type :=
  let in_scope := substInScope subst in
  let env := substIdEnv subst in
  let id1 := uniqAway in_scope old_id in
  let id2 := id1 in
  let mb_new_info := substIdInfo rec_subst id2 (idInfo id2) in
  let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
  let no_change := GHC.Base.op_zeze__ id1 old_id in
  let new_env :=
    if no_change : bool
    then delVarEnv env old_id
    else extendVarEnv env old_id (Mk_Var new_id) in
  pair (Mk_Subst (extendInScopeSet in_scope new_id) new_env tt tt) new_id.

(* substBndr: simplified — all Vars are Ids, no TyVar/CoVar branching *)
Definition substBndr (subst : Subst) (bndr : Var)
  : (Subst * Var)%type :=
  substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr.

Definition substBndrs {f : Type -> Type} `{Data.Traversable.Traversable f}
  (subst : Subst) (bndrs : f Var)
  : (Subst * f Var)%type :=
  Data.Traversable.mapAccumL substBndr subst bndrs.

Definition substRecBndrs {f : Type -> Type} `{Data.Traversable.Traversable f}
  (subst : Subst) (bndrs : f Id)
  : (Subst * f Id)%type :=
  let '(new_subst, new_bndrs) :=
    Data.Traversable.mapAccumL
      (substIdBndr (Datatypes.id (GHC.Base.hs_string__ "rec-bndr"))
                   (GHC.Err.error Panic.someSDoc))
      subst bndrs in
  pair new_subst new_bndrs.

(* lookupIdSubst: GHC version uses pprPanic for missing vars;
   we use Mk_Var v fallback. Defined here (before substExpr_) because
   substExpr_ calls it. *)
Definition lookupIdSubst `{Util.HasDebugCallStack}
  (s : Subst) (v : Id) : CoreExpr :=
  if negb (isLocalId v) then Mk_Var v
  else match lookupVarEnv (substIdEnv s) v with
       | Some e => e
       | None =>
         match lookupInScope (substInScope s) v with
         | Some v' => Mk_Var v'
         | None => Mk_Var v
         end
       end.

(* substExpr and substBind: mutually recursive substitution.
   Uses Fixpoint ... with ... on the mutually inductive Expr/Bind types.
   Must be in midamble because hs-to-coq can't generate the mutual Fixpoint. *)
Fixpoint substExpr_ (subst : Subst)
  (expr : CoreExpr) {struct expr} : CoreExpr :=
  match expr with
  | Mk_Var v => lookupIdSubst subst v
  | Lit lit => Lit lit
  | App f a => App (substExpr_ subst f) (substExpr_ subst a)
  | Lam bndr body =>
      let '(subst', bndr') := substBndr subst bndr in
      Lam bndr' (substExpr_ subst' body)
  | Let bind body =>
      let '(subst', bind') := substBind_ subst bind in
      Let bind' (substExpr_ subst' body)
  | Case scrut bndr ty alts =>
      let '(subst', bndr') := substBndr subst bndr in
      let fix go_alts (l : list (Alt Var)) :=
        match l with
        | nil => nil
        | cons (Mk_Alt con bndrs rhs) rest =>
            let '(subst'', bndrs') := substBndrs subst' bndrs in
            cons (Mk_Alt con bndrs' (substExpr_ subst'' rhs)) (go_alts rest)
        end in
      Case (substExpr_ subst scrut) bndr'
           (substTyUnchecked subst ty) (go_alts alts)
  | Cast e co => Cast (substExpr_ subst e) (substCo subst co)
  | Mk_Type ty => Mk_Type (substTyUnchecked subst ty)
  | Mk_Coercion co => Mk_Coercion (substCo subst co)
  end
with substBind_ (subst : Subst)
  (bind : CoreBind) {struct bind}
  : (Subst * CoreBind)%type :=
  match bind with
  | NonRec bndr rhs =>
      let '(subst', bndr') := substBndr subst bndr in
      (subst', NonRec bndr' (substExpr_ subst rhs))
  | Rec pairs =>
      let bndrs := GHC.Base.map Data.Tuple.fst pairs in
      let '(subst', bndrs') := substRecBndrs subst bndrs in
      let fix go_rhss (ps : list (Var * CoreExpr)) :=
        match ps with
        | nil => nil
        | cons (pair _ rhs) rest =>
            cons (substExpr_ subst' rhs) (go_rhss rest)
        end in
      (subst', Rec (GHC.List.zip bndrs' (go_rhss pairs)))
  end.

Definition substExpr `{Util.HasDebugCallStack}
  (subst : Subst) (expr : CoreExpr) : CoreExpr :=
  substExpr_ subst expr.

Definition substBind `{Util.HasDebugCallStack}
  (subst : Subst) (bind : CoreBind)
  : (Subst * CoreBind)%type :=
  substBind_ subst bind.

(* Convenience wrappers *)
Definition substExprSC `{Util.HasDebugCallStack}
  (subst : Subst) (expr : CoreExpr) : CoreExpr :=
  if isEmptySubst subst then expr
  else substExpr subst expr.

Definition substBindSC `{Util.HasDebugCallStack}
  (subst : Subst) (bind : CoreBind)
  : (Subst * CoreBind)%type :=
  if isEmptySubst subst then (subst, bind)
  else substBind subst bind.

(* Converted value declarations: *)

#[global] Definition extendIdSubst : Subst -> Id -> CoreExpr -> Subst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_Subst in_scope ids tvs cvs, v, r =>
        Panic.assertPpr (isNonCoVarId v) (Panic.someSDoc) (Mk_Subst in_scope
                                                                    (extendVarEnv ids v r) tvs cvs)
    end.

#[global] Definition extendIdSubstWithClone (s : Subst) (v1 v2 : Id) : Subst :=
  let 'Mk_Subst in_scope ids _ _ := s in
  Mk_Subst in_scope (extendVarEnv ids v1 (Mk_Var v2)) tt tt.

#[global] Definition extendIdSubstList
   : Subst -> list (Id * CoreExpr)%type -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, prs =>
        Mk_Subst in_scope (extendVarEnvList ids prs) tvs cvs
    end.

#[global] Definition extendSubst (s : Subst) (v : Var) (arg : CoreArg)
   : Subst :=
  match arg with
  | Mk_Type _ => s
  | Mk_Coercion _ => s
  | _ => extendIdSubst s v arg
  end.

#[global] Definition extendSubstWithVar (s : Subst) (v1 v2 : Var) : Subst :=
  extendIdSubst s v1 (Mk_Var v2).

Fixpoint extendSubstList (arg_0__ : Subst) (arg_1__ : list (Var * CoreArg)%type)
  : Subst
  := match arg_0__, arg_1__ with
     | subst, nil => subst
     | subst, cons (pair var rhs) prs =>
         extendSubstList (extendSubst subst var rhs) prs
     end.

(* Skipping definition `CoreSubst.lookupIdSubst' *)

#[global] Definition lookupIdSubst_maybe `{Util.HasDebugCallStack}
   : Subst -> Id -> option CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst _ ids _ _, v =>
        Panic.assertPpr (andb (isId v) (negb (isCoVar v))) (Panic.someSDoc)
        (lookupVarEnv ids v)
    end.

#[global] Definition delBndr (s : Subst) (v : Var) : Subst :=
  Mk_Subst (substInScope s) (delVarEnv (substIdEnv s) v) tt tt.

#[global] Definition delBndrs (s : Subst) (vs : list Var) : Subst :=
  Mk_Subst (substInScope s) (delVarEnvList (substIdEnv s) vs) tt tt.

(* Skipping definition `CoreSubst.mkOpenSubst' *)

(* Skipping definition `CoreSubst.substExprSC' *)

(* Skipping definition `CoreSubst.substExpr' *)

(* Skipping definition `CoreSubst.substBindSC' *)

(* Skipping definition `CoreSubst.substBind' *)

(* Skipping definition `CoreSubst.deShadowBinds' *)

(* Skipping definition `CoreSubst.substBndr' *)

(* Skipping definition `CoreSubst.substBndrs' *)

(* Skipping definition `CoreSubst.substRecBndrs' *)

(* Skipping definition `CoreSubst.substIdBndr' *)

(* Skipping definition `CoreSubst.cloneIdBndr' *)

(* Skipping definition `CoreSubst.cloneIdBndrs' *)

(* Skipping definition `CoreSubst.cloneBndrs' *)

(* Skipping definition `CoreSubst.cloneBndr' *)

(* Skipping definition `CoreSubst.cloneRecIdBndrs' *)

(* Skipping definition `CoreSubst.clone_id' *)

#[global] Definition substIdType (_ : Subst) (id : Id) : Id :=
  id.

(* Skipping definition `CoreSubst.substIdInfo' *)

#[global] Definition substUnfoldingSC (_ : Subst) (unf : Unfolding)
   : Unfolding :=
  unf.

#[global] Definition substUnfolding (_ : Subst) (unf : Unfolding) : Unfolding :=
  unf.

#[global] Definition substIdOcc (subst : Subst) (v : Id) : Id :=
  match lookupIdSubst subst v with
  | Mk_Var v' => v'
  | _ => Panic.panicStr (hs_string__ "substIdOcc") Panic.someSDoc
  end.

(* Skipping definition `CoreSubst.substRuleInfo' *)

(* Skipping definition `CoreSubst.substRulesForImportedIds' *)

(* Skipping definition `CoreSubst.substRule' *)

(* Skipping definition `CoreSubst.substDVarSet' *)

(* Skipping definition `CoreSubst.substTickish' *)

(* External variables:
     CoreArg CoreExpr Id Mk_Coercion Mk_Subst Mk_Type Mk_Var Subst Unfolding Var andb
     cons delVarEnv delVarEnvList extendVarEnv extendVarEnvList hs_string__ isCoVar
     isId isNonCoVarId list lookupIdSubst lookupVarEnv negb nil op_zt__ option pair
     substIdEnv substInScope tt Panic.assertPpr Panic.panicStr Panic.someSDoc
     Util.HasDebugCallStack
*)
