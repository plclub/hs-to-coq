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
Require GHC.Types.Tickish.
Require Name.
Require UniqSupply.
Require Unique.
Require Util.

(* No type declarations to convert. *)

(* Midamble *)

(* GHC 9.10: Subst is axiomatized in GHC.Core.TyCo.Subst.
   This midamble provides structural axioms and concrete function definitions
   so that theories/CoreSubst.v proofs can reason about substitution. *)

Require Import GHC.Core.TyCo.Subst.
Require Import AxiomatizedTypes.
Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import GHC.List.
Require Import Data.Traversable.
Require Import Data.Tuple.
Require Import Id.
Require Import Panic.
Require Import Coq.Lists.List.
Require Import Datatypes.

(* === IdSubstEnv type alias === *)
Definition IdSubstEnv := VarEnv CoreExpr.

(* === Structural axioms for the abstract Subst type ===

   In GHC: data Subst = Subst InScopeSet IdSubstEnv TvSubstEnv CvSubstEnv
   where TvSubstEnv = CvSubstEnv = unit (types/coercions are axiomatized).

   Subst is defined as an Axiom in GHC.Core.TyCo.Subst (loaded before Core.v)
   because InScopeSet and VarEnv are defined in Core.v. These axioms give
   it the expected record structure. *)

Axiom Mk_Subst : InScopeSet -> IdSubstEnv -> unit -> unit ->
  GHC.Core.TyCo.Subst.Subst.

Axiom substInScope : GHC.Core.TyCo.Subst.Subst -> InScopeSet.
Axiom substIdEnv : GHC.Core.TyCo.Subst.Subst -> IdSubstEnv.

(* Constructor/projection round trips *)
Axiom substInScope_Mk_Subst : forall is ie te ce,
  substInScope (Mk_Subst is ie te ce) = is.
Axiom substIdEnv_Mk_Subst : forall is ie te ce,
  substIdEnv (Mk_Subst is ie te ce) = ie.

(* Eta: every Subst is constructed from its projections *)
Axiom Subst_eta : forall s,
  s = Mk_Subst (substInScope s) (substIdEnv s) tt tt.

(* Injectivity of Mk_Subst *)
Axiom Mk_Subst_injective : forall is1 ie1 is2 ie2 te1 ce1 te2 ce2,
  Mk_Subst is1 ie1 te1 ce1 = Mk_Subst is2 ie2 te2 ce2 ->
  is1 = is2 /\ ie1 = ie2.

(* Equivalences with GHC.Core.TyCo.Subst functions *)
Axiom emptySubst_eq :
  GHC.Core.TyCo.Subst.emptySubst = Mk_Subst emptyInScopeSet emptyVarEnv tt tt.
Axiom mkEmptySubst_eq : forall is,
  @GHC.Core.TyCo.Subst.mkEmptySubst InScopeSet is = Mk_Subst is emptyVarEnv tt tt.

(* Type/coercion substitution is identity (types are axiomatized) *)
Axiom substTyUnchecked_id : forall s ty,
  GHC.Core.TyCo.Subst.substTyUnchecked s ty = ty.
Axiom substCo_id : forall s (co : AxiomatizedTypes.Coercion),
  @GHC.Core.TyCo.Subst.substCo AxiomatizedTypes.Coercion s co = co.

(* === Concrete function definitions === *)

Definition emptySubst : GHC.Core.TyCo.Subst.Subst :=
  Mk_Subst emptyInScopeSet emptyVarEnv tt tt.

Definition mkEmptySubst (in_scope : InScopeSet) : GHC.Core.TyCo.Subst.Subst :=
  Mk_Subst in_scope emptyVarEnv tt tt.

(* Type/coercion substitution: identity *)
Definition substTyUnchecked (_ : GHC.Core.TyCo.Subst.Subst)
  (ty : AxiomatizedTypes.Type_) : AxiomatizedTypes.Type_ := ty.
Definition substCo (_ : GHC.Core.TyCo.Subst.Subst)
  (co : AxiomatizedTypes.Coercion) : AxiomatizedTypes.Coercion := co.

Definition isEmptySubst (s : GHC.Core.TyCo.Subst.Subst) : bool :=
  isEmptyVarEnv (substIdEnv s).

Definition extendIdSubst (s : GHC.Core.TyCo.Subst.Subst)
  (v : Id) (r : CoreExpr) : GHC.Core.TyCo.Subst.Subst :=
  Mk_Subst (substInScope s) (extendVarEnv (substIdEnv s) v r) tt tt.

Definition extendIdSubstWithClone (s : GHC.Core.TyCo.Subst.Subst)
  (v1 v2 : Id) : GHC.Core.TyCo.Subst.Subst :=
  Mk_Subst (substInScope s) (extendVarEnv (substIdEnv s) v1 (Mk_Var v2)) tt tt.

Definition extendIdSubstList (s : GHC.Core.TyCo.Subst.Subst)
  (prs : list (Id * CoreExpr)%type) : GHC.Core.TyCo.Subst.Subst :=
  Mk_Subst (substInScope s) (extendVarEnvList (substIdEnv s) prs) tt tt.

Definition extendSubst (s : GHC.Core.TyCo.Subst.Subst)
  (v : Var) (arg : CoreArg) : GHC.Core.TyCo.Subst.Subst :=
  match arg with
  | Mk_Type _ => s
  | Mk_Coercion _ => s
  | _ => extendIdSubst s v arg
  end.

Definition extendSubstWithVar (s : GHC.Core.TyCo.Subst.Subst)
  (v1 v2 : Var) : GHC.Core.TyCo.Subst.Subst :=
  extendIdSubst s v1 (Mk_Var v2).

Fixpoint extendSubstList (s : GHC.Core.TyCo.Subst.Subst)
  (l : list (Var * CoreArg)%type) : GHC.Core.TyCo.Subst.Subst :=
  match l with
  | nil => s
  | cons (pair var rhs) prs => extendSubstList (extendSubst s var rhs) prs
  end.

Definition lookupIdSubst `{Util.HasDebugCallStack}
  (s : GHC.Core.TyCo.Subst.Subst) (v : Id) : CoreExpr :=
  if negb (isLocalId v) then Mk_Var v
  else match lookupVarEnv (substIdEnv s) v with
       | Some e => e
       | None =>
         match lookupInScope (substInScope s) v with
         | Some v' => Mk_Var v'
         | None => Mk_Var v
         end
       end.

Definition lookupIdSubst_maybe `{Util.HasDebugCallStack}
  (s : GHC.Core.TyCo.Subst.Subst) (v : Id) : option CoreExpr :=
  if negb (isLocalId v) then None
  else lookupVarEnv (substIdEnv s) v.

Definition delBndr (s : GHC.Core.TyCo.Subst.Subst) (v : Var)
  : GHC.Core.TyCo.Subst.Subst :=
  Mk_Subst (substInScope s) (delVarEnv (substIdEnv s) v) tt tt.

Definition delBndrs (s : GHC.Core.TyCo.Subst.Subst) (vs : list Var)
  : GHC.Core.TyCo.Subst.Subst :=
  Mk_Subst (substInScope s) (delVarEnvList (substIdEnv s) vs) tt tt.

Definition mkOpenSubst (in_scope : InScopeSet)
  (pairs : list (Var * CoreArg)%type) : GHC.Core.TyCo.Subst.Subst :=
  Mk_Subst in_scope
    (mkVarEnv (Coq.Lists.List.flat_map
      (fun '(pair id e) =>
        if isId id then cons (pair id e) nil else nil) pairs))
    tt tt.

(* substIdInfo: simplified since types/coercions are axiomatized.
   Returns None (no info change needed) since unfolding substitution
   is identity and rule substitution doesn't affect well-scopedness. *)
Definition substUnfolding (_ : GHC.Core.TyCo.Subst.Subst) (unf : Unfolding)
  : Unfolding := unf.

Definition substIdInfo (_ : GHC.Core.TyCo.Subst.Subst) (_ : Id)
  (_ : IdInfo) : option IdInfo := None.

(* substIdBndr: capture-avoiding variable freshening *)
Definition substIdBndr (doc : String)
  (rec_subst subst : GHC.Core.TyCo.Subst.Subst) (old_id : Id)
  : (GHC.Core.TyCo.Subst.Subst * Id)%type :=
  let in_scope := substInScope subst in
  let env := substIdEnv subst in
  let id1 := uniqAway in_scope old_id in
  (* no type change: TvSubstEnv = CvSubstEnv = unit *)
  let id2 := id1 in
  let mb_new_info := substIdInfo rec_subst id2 (idInfo id2) in
  let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
  let no_change := GHC.Base.op_zeze__ id1 old_id in
  let new_env :=
    if no_change : bool
    then delVarEnv env old_id
    else extendVarEnv env old_id (Mk_Var new_id) in
  pair (Mk_Subst (extendInScopeSet in_scope new_id) new_env tt tt) new_id.

Definition substBndr (subst : GHC.Core.TyCo.Subst.Subst) (bndr : Var)
  : (GHC.Core.TyCo.Subst.Subst * Var)%type :=
  substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr.

Definition substBndrs {f : Type -> Type} `{Data.Traversable.Traversable f}
  (subst : GHC.Core.TyCo.Subst.Subst) (bndrs : f Var)
  : (GHC.Core.TyCo.Subst.Subst * f Var)%type :=
  Data.Traversable.mapAccumL substBndr subst bndrs.

Definition substRecBndrs {f : Type -> Type} `{Data.Traversable.Traversable f}
  (subst : GHC.Core.TyCo.Subst.Subst) (bndrs : f Id)
  : (GHC.Core.TyCo.Subst.Subst * f Id)%type :=
  let '(new_subst, new_bndrs) :=
    Data.Traversable.mapAccumL
      (substIdBndr (Datatypes.id (GHC.Base.hs_string__ "rec-bndr"))
                   (GHC.Err.error Panic.someSDoc))
      subst bndrs in
  pair new_subst new_bndrs.

(* substExpr and substBind: mutually recursive substitution.
   Uses Fixpoint ... with ... on the mutually inductive Expr/Bind types.
   Nested fix is used for list traversal so Coq's guard checker
   can see structural decrease through list/pair/Alt nesting. *)
Fixpoint substExpr_ (subst : GHC.Core.TyCo.Subst.Subst)
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
with substBind_ (subst : GHC.Core.TyCo.Subst.Subst)
  (bind : CoreBind) {struct bind}
  : (GHC.Core.TyCo.Subst.Subst * CoreBind)%type :=
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
  (subst : GHC.Core.TyCo.Subst.Subst) (expr : CoreExpr) : CoreExpr :=
  substExpr_ subst expr.

Definition substBind `{Util.HasDebugCallStack}
  (subst : GHC.Core.TyCo.Subst.Subst) (bind : CoreBind)
  : (GHC.Core.TyCo.Subst.Subst * CoreBind)%type :=
  substBind_ subst bind.

(* Convenience wrappers *)
Definition substExprSC `{Util.HasDebugCallStack}
  (subst : GHC.Core.TyCo.Subst.Subst) (expr : CoreExpr) : CoreExpr :=
  if isEmptySubst subst then expr
  else substExpr subst expr.

Definition substBindSC `{Util.HasDebugCallStack}
  (subst : GHC.Core.TyCo.Subst.Subst) (bind : CoreBind)
  : (GHC.Core.TyCo.Subst.Subst * CoreBind)%type :=
  if isEmptySubst subst then (subst, bind)
  else substBind subst bind.

Definition substUnfoldingSC (_ : GHC.Core.TyCo.Subst.Subst)
  (unf : Unfolding) : Unfolding := unf.

Definition substIdOcc (subst : GHC.Core.TyCo.Subst.Subst) (v : Id) : Id :=
  match lookupIdSubst subst v with
  | Mk_Var v' => v'
  | _ => Panic.panicStr (GHC.Base.hs_string__ "substIdOcc") Panic.someSDoc
  end.

(* substIdType: identity since types are axiomatized *)
Definition substIdType (_ : GHC.Core.TyCo.Subst.Subst) (id : Id) : Id := id.

(* Converted value declarations: *)

(* Skipping definition `CoreSubst.extendIdSubst' *)

(* Skipping definition `CoreSubst.extendIdSubstWithClone' *)

(* Skipping definition `CoreSubst.extendIdSubstList' *)

(* Skipping definition `CoreSubst.extendSubst' *)

(* Skipping definition `CoreSubst.extendSubstWithVar' *)

(* Skipping definition `CoreSubst.extendSubstList' *)

(* Skipping definition `CoreSubst.lookupIdSubst' *)

(* Skipping definition `CoreSubst.lookupIdSubst_maybe' *)

(* Skipping definition `CoreSubst.delBndr' *)

(* Skipping definition `CoreSubst.delBndrs' *)

(* Skipping definition `CoreSubst.mkOpenSubst' *)

(* Skipping definition `CoreSubst.substExprSC' *)

(* Skipping definition `CoreSubst.substExpr' *)

(* Skipping definition `CoreSubst.substBindSC' *)

(* Skipping definition `CoreSubst.substBind' *)

Axiom deShadowBinds : CoreProgram -> CoreProgram.

(* Skipping definition `CoreSubst.substBndr' *)

(* Skipping definition `CoreSubst.substBndrs' *)

(* Skipping definition `CoreSubst.substRecBndrs' *)

(* Skipping definition `CoreSubst.substIdBndr' *)

Axiom cloneIdBndr : GHC.Core.TyCo.Subst.Subst ->
                    UniqSupply.UniqSupply -> Id -> (GHC.Core.TyCo.Subst.Subst * Id)%type.

Axiom cloneIdBndrs : GHC.Core.TyCo.Subst.Subst ->
                     UniqSupply.UniqSupply -> list Id -> (GHC.Core.TyCo.Subst.Subst * list Id)%type.

Axiom cloneBndrs : forall {m : Type -> Type},
                   forall `{UniqSupply.MonadUnique m},
                   GHC.Core.TyCo.Subst.Subst ->
                   list Var -> m (GHC.Core.TyCo.Subst.Subst * list Var)%type.

Axiom cloneBndr : GHC.Core.TyCo.Subst.Subst ->
                  Unique.Unique -> Var -> (GHC.Core.TyCo.Subst.Subst * Var)%type.

Axiom cloneRecIdBndrs : forall {m : Type -> Type},
                        forall `{UniqSupply.MonadUnique m},
                        GHC.Core.TyCo.Subst.Subst ->
                        list Id -> m (GHC.Core.TyCo.Subst.Subst * list Id)%type.

Axiom clone_id : GHC.Core.TyCo.Subst.Subst ->
                 GHC.Core.TyCo.Subst.Subst ->
                 (Id * Unique.Unique)%type -> (GHC.Core.TyCo.Subst.Subst * Id)%type.

(* Skipping definition `CoreSubst.substIdType' *)

(* Skipping definition `CoreSubst.substIdInfo' *)

(* Skipping definition `CoreSubst.substUnfoldingSC' *)

(* Skipping definition `CoreSubst.substUnfolding' *)

(* Skipping definition `CoreSubst.substIdOcc' *)

Axiom substRuleInfo : GHC.Core.TyCo.Subst.Subst -> Id -> RuleInfo -> RuleInfo.

Axiom substRulesForImportedIds : GHC.Core.TyCo.Subst.Subst ->
                                 list CoreRule -> list CoreRule.

Axiom substRule : GHC.Core.TyCo.Subst.Subst ->
                  (Name.Name -> Name.Name) -> CoreRule -> CoreRule.

Axiom substDVarSet : forall `{Util.HasDebugCallStack},
                     GHC.Core.TyCo.Subst.Subst -> DVarSet -> DVarSet.

Axiom substTickish : GHC.Core.TyCo.Subst.Subst ->
                     GHC.Types.Tickish.CoreTickish -> GHC.Types.Tickish.CoreTickish.

(* External variables:
     CoreProgram CoreRule DVarSet Id RuleInfo Type Var list op_zt__
     GHC.Core.TyCo.Subst.Subst GHC.Types.Tickish.CoreTickish Name.Name
     UniqSupply.MonadUnique UniqSupply.UniqSupply Unique.Unique
     Util.HasDebugCallStack
*)
