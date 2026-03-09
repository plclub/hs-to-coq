From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat.
Set Bullet Behavior "Strict Subproofs".

Require Import Coq.Lists.List.

Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Data.Foldable.
Require Import Data.Traversable.

Require Import Proofs.GHC.Base.
Require Import Proofs.Data.Foldable.
Require Import Proofs.Data.Traversable.

Require Import BasicTypes.
Require Import Id.
Require Import Core.
Require Import CoreUtils.
Require Import CoreSubst.

Require Import Proofs.Core.
Require Import Proofs.CoreInduct.
Require Import Proofs.CoreSubst.
Require Import Proofs.ScopeInvariant.
Require Import Proofs.Forall.
Require Import Proofs.OrdList.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetStrong.
Require Import Proofs.VarEnv.

Require Import CSE.
Require Import TrieMap.
Require Import Proofs.TrieMap.

Opaque GHC.Base.hs_string__.

(** * Evaluating CSE *)
(* We really ought to be able to automate these things *)

(* GHC 9.10: cseExpr, cseBind, try_for_cse are all axiomatized in the lib.
   Computational unfolding lemmas cannot be proved; Admitted. *)

Lemma cseExpr_App env f a :
  cseExpr env (App f a) = App (cseExpr env f) (tryForCSE env a).
Proof. Admitted.
#[export] Hint Rewrite cseExpr_App : hs_simpl.

Lemma cseExpr_Let env bind e :
  cseExpr env (Let bind e) = let: (env', bind') := cseBind NotTopLevel env bind
                             in Let bind' (cseExpr env' e).
Proof. Admitted.
#[export] Hint Rewrite cseExpr_Let : hs_simpl.

(* GHC 9.10: cse_bind signature changed (added env_rhs parameter).
   cseBind is axiomatized so this lemma is not provable. *)
Lemma cseBind_NonRec toplevel env b e :
  cseBind toplevel env (NonRec b e) =
    let: (env1, b1)       := addBinder env b in
    let: (env2, (b2, e2)) := cse_bind toplevel env env1 (b,e) b1 in
    (env2, NonRec b2 e2).
Proof. Admitted.
#[export] Hint Rewrite cseBind_NonRec : hs_simpl.

(** * Stripping ticks *)

Lemma stripTicksE_id {b} p (e : Expr b) :
  stripTicksE p e = e.
Proof.
  (* GHC 9.10: Alt changed from tuple to Mk_Alt; proof needs reworking *)
Admitted.

#[export] Hint Rewrite @stripTicksE_id : hs_simpl.
#[export] Hint Rewrite (@stripTicksE_id CoreBndr) : hs_simpl.

Lemma stripTicksT_nil {b} p (e : Expr b) :
  stripTicksT p e = nil.
Proof.
  (* GHC 9.10: Alt changed from tuple to Mk_Alt; proof needs reworking *)
Admitted.

#[export] Hint Rewrite @stripTicksT_nil : hs_simpl.
#[export] Hint Rewrite (@stripTicksT_nil CoreBndr) : hs_simpl.

(** * Well-scopedness for CSE *)

(* vars = set of variables in scope AFTER `cs_subst` is applied *)
Record WellScopedCSEnv (env : CSEnv) (vars : VarSet) : Prop :=
 IsWellScopedCSEnv
   { ws_subst   : WellScoped_Subst (cs_subst env) vars
   ; ws_map     : const True (cs_map env)
   ; ws_rec_map : const True (cs_rec_map env) }.

(* GHC 9.10: tryForCSE wraps try_for_cse which is axiomatized.
   Cannot unfold; Admitted. *)
Lemma tryForCSE_simpl env expr :
  tryForCSE env expr = match lookupCSEnv env (cseExpr env expr) with
                       | Some e => e
                       | None   => cseExpr env expr
                       end.
Proof. Admitted.

(* GHC 9.10: cseExpr, cseBind, try_for_cse are axiomatized.
   The well-scopedness proof cannot proceed by computation. Admitted. *)
Definition WS_cseExpr vars env e :
  WellScopedCSEnv env             vars ->
  WellScoped      e               vars ->
  WellScoped      (cseExpr env e) (getSubstInScopeVars (cs_subst env)).
Proof. Admitted.
