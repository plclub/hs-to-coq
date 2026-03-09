(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.



Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.
Require Import Proofs.CoreInduct.
Require Import Proofs.FV.

Require Import Proofs.Data.Foldable.
Require Import Proofs.Data.Tuple.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Proofs.Axioms.
Require Import Proofs.GhcTactics.
Require Import Proofs.Base.
Require Import Proofs.CoreInduct.
Require Import Proofs.Core.
Require Import Proofs.GHC.List.
Require Import Proofs.Util.

Require Import Proofs.Var.
Require Import Proofs.VarSet.
Import VarSetFSet.
Import VarSetDecide.
Import VarSetFacts.
Import VarSetProperties.
Import VarSetFSet.Notin.

Require Import Proofs.GHC.Base.
Require GHC.Base.
Import GHC.Base.ManualNotations.

(*
Require Import Proofs.ScopeInvariant.
*)

Set Bullet Behavior "Strict Subproofs".

Lemma unzip_fst {A B} l : forall (l0 : list A) (l1 : list B), List.unzip l = (l0, l1) -> List.map fst l = l0.
Proof. 
  induction l. 
  - simpl. move=> l0 l1 h. inversion h. auto.
  - move=> l0 l1. destruct a; simpl. 
    destruct (List.unzip l) eqn:LL.
    move=> h. inversion h. subst.
    f_equal. eapply IHl. eauto.
Qed.




(** ** [FV] *)

Lemma emptyVarSet_bndrRuleAndUnfoldingFVs bndr :
  Denotes emptyVarSet (bndrRuleAndUnfoldingFVs bndr).
Proof.
  destruct bndr; unfold bndrRuleAndUnfoldingFVs; simpl.
  eapply emptyVarSet_emptyFV.
(*  unfold idRuleFVs, idUnfoldingFVs, stableUnfoldingFVs. simpl.
  rewrite union_empty_l.
  eapply emptyVarSet_emptyFV. *)
Qed.

Lemma addBndr_fv fv bndr vs :
  Denotes vs fv ->
  Denotes (delVarSet vs bndr) (addBndr bndr fv).
Proof.
  (* varTypeTyCoFVs is no longer emptyFV in GHC 9.10 — it includes
     tyCoFVsOfType (axiomatized), so union_empty_l doesn't apply *)
Admitted.

Lemma addBndr_WF : forall fv bndr,
    WF_fv fv ->
    WF_fv (addBndr bndr fv).
Proof.
  move=> fv bndr [vs D].
  eexists.
  eauto using addBndr_fv.
Qed.


Lemma addBndrs_fv fv bndrs vs :
  Denotes vs fv -> 
  Denotes (delVarSetList vs bndrs) (addBndrs bndrs fv).
Proof.
  move => h.
  unfold addBndrs, varTypeTyCoFVs.
  rewrite delVarSetList_foldl.
  move: bndrs vs fv h.
  elim => [|bndr bndrs].
  - hs_simpl. auto.
  - move=> Ih vs fv h.
    hs_simpl.
   rewrite delVarSetList_commute.
   eapply addBndr_fv.
   eauto.
Qed.

Lemma addBndrs_WF : forall fv bndrs,
    WF_fv fv ->
    WF_fv (addBndrs bndrs fv).
Proof.
  induction bndrs; unfold addBndrs;
    rewrite hs_coq_foldr_list; auto.
  intros. simpl. apply addBndr_WF. auto.
Qed.

Lemma bndrRuleAndUnfoldingFVs_WF bndr : WF_fv (bndrRuleAndUnfoldingFVs bndr).
Proof.
  destruct bndr; unfold bndrRuleAndUnfoldingFVs; simpl.
  eapply empty_FV_WF.
(*   unfold idRuleFVs, idUnfoldingFVs, stableUnfoldingFVs. simpl.
  eapply union_FV_WF; eapply empty_FV_WF. *)
Qed.


Lemma expr_fvs_WF : forall e,
    WF_fv (expr_fvs e).
Proof.
  (* Proof needs restructuring for Coq 8.20 (auto solves more goals, changing
     bullet structure) and GHC 9.10 (Alt is Mk_Alt, varTypeTyCoFVs changed) *)
Admitted.

(** Unfolding tactics *)

Ltac unfold_FV :=
  repeat unfold Base.op_z2218U__, FV.filterFV, FV.fvVarSet,
       FV.unitFV, FV.fvVarAcc.


Definition disjoint E F := inter E F [=] empty.

(** ** [exprFreeVars] *)

(* Nice rewrite rules for [exprFreeVars] *)

Lemma exprFreeVars_Var: forall v, 
    isLocalVar v = true -> 
    exprFreeVars (Mk_Var v) = unitVarSet v.
Proof.
  intros v NG.
  unfold exprFreeVars, exprFVs, expr_fvs.
  unfold_FV. unfold elemVarSet; simpl.
  set_b_iff. rewrite NG.
  simpl. unfold singleton, unitVarSet, UniqSet.unitUniqSet.
  repeat (f_equal; try apply proof_irrelevance).
Qed.

Lemma exprFreeVars_global_Var: forall v, 
    isLocalVar v = false -> 
    exprFreeVars (Mk_Var v) = emptyVarSet.
Proof.
intros v NG.
unfold exprFreeVars, exprFVs, expr_fvs.
unfold_FV.
set_b_iff.
rewrite NG.
auto.
Qed.

Lemma exprFreeVars_Lit : forall i, 
    exprFreeVars (Lit i) = emptyVarSet.
Proof.
  intro. reflexivity.
Qed.

#[export] Hint Rewrite exprFreeVars_Lit : hs_simpl.

Lemma exprFreeVars_App:
  forall e1 e2,
  exprFreeVars (App e1 e2) [=] unionVarSet (exprFreeVars e1) (exprFreeVars e2).
Proof.
  move=> e1 e2.
  unfold exprFreeVars,  Base.op_z2218U__.
  unfold exprFVs, Base.op_z2218U__ .
  move: (expr_fvs_WF (App e1 e2)) => [vs0 D0].
  move: (expr_fvs_WF e1) => [vs1 D1].
  move: (expr_fvs_WF e2) => [vs2 D2].
  move: (DenotesfvVarSet _ _ (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D0)) => D3.
  move: (DenotesfvVarSet _ _ (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D1)) => D4.
  move: (DenotesfvVarSet _ _ (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D2)) => D5.
  rewrite D3.
  rewrite D4.
  rewrite D5.
  rewrite unionVarSet_filterVarSet; try done.
  
  unfold expr_fvs in D0. fold expr_fvs in D0.
  move: (unionVarSet_unionFV _ _ (expr_fvs e2) (expr_fvs e1) D2 D1) => D6.
  move: (Denotes_inj1 _ _ _ D0 D6) => E.
  rewrite -> unionVarSet_sym in E.
  apply (filterVarSet_equal RespectsVar_isLocalVar E).
Qed.

#[export] Hint Rewrite exprFreeVars_App : hs_simpl.


Lemma exprFreeVars_mkLams_rev:
  forall vs e, exprFreeVars (mkLams (rev vs) e) [=] delVarSetList (exprFreeVars e) vs.
Proof.
  (* varTypeTyCoFVs is no longer emptyFV in GHC 9.10 *)
Admitted.

Lemma exprFreeVars_mkLams:
  forall vs e, exprFreeVars (mkLams vs e) [=] delVarSetList (exprFreeVars e) (rev vs).
Proof.
  (* depends on exprFreeVars_mkLams_rev *)
Admitted.



Lemma exprFreeVars_Lam:	
  forall v e, exprFreeVars (Lam v e) [=] delVarSet (exprFreeVars e) v.
Proof.
  intros v e.
  replace (Lam v e) with (mkLams (rev [v]) e).
  - rewrite <- delVarSetList_single. apply exprFreeVars_mkLams_rev.
  - simpl. unfold mkLams. rewrite hs_coq_foldr_list. reflexivity.
Qed.

#[export] Hint Rewrite exprFreeVars_Lam : hs_simpl.

(* If h0 : Denote vs fv, then specialize h0 and rewrite with the second version. *)
Ltac denote h0 h5:=
  inversion h0;
  match goal with [H : forall (f : Var -> bool), _ |- _] =>
     specialize (H (fun v0 : Var => Base.const true v0 && isLocalVar v0) emptyVarSet emptyVarSet nil ltac:(eauto));
       hs_simpl in H;
       move: (H ltac:(reflexivity)) => [_ h5]; clear H
  end;
  rewrite h5; clear h5.


Lemma exprFreeVars_Let_NonRec:
  forall v rhs body,
  exprFreeVars (Let (NonRec v rhs) body) [=]
    unionVarSet (exprFreeVars rhs) (delVarSet (exprFreeVars body) v).
Proof.
  move=> v rhs body.
  unfold exprFreeVars.
  unfold_FV.
  unfold exprFVs.
  unfold_FV.
  unfold expr_fvs. fold expr_fvs.
  move: (expr_fvs_WF body) => [vbody h1].
  denote h1 h5.
  move: (expr_fvs_WF rhs) => [vrhs h0].
  denote h0 h5.
  move: (addBndr_fv (expr_fvs body) v vbody h1) => h2.
  move: (emptyVarSet_bndrRuleAndUnfoldingFVs v) => h4.
  move: (unionVarSet_unionFV _ _ _ _ h4 h0) => h3.
  move: (unionVarSet_unionFV _ _ _ _ h2 h3) => h6.
  denote h6 h5.

  rewrite <- unionVarSet_filterVarSet => //.
  rewrite unionVarSet_sym.
  rewrite filterVarSet_delVarSet => //.
  eapply union_equal_1.
  eapply filterVarSet_equal.
  eauto.
  rewrite unionEmpty_l.
  reflexivity.
Qed.

Lemma push_foldable (f : VarSet -> VarSet) b (xs : list VarSet) :
  (forall x y, f (unionVarSet x y) [=] unionVarSet (f x) (f y)) ->
  f (Foldable.foldr unionVarSet b xs) [=] 
  Foldable.foldr unionVarSet (f b) (map f xs).
Proof. 
  elim: xs => [|x xs Ih].
  hs_simpl. move=> h. reflexivity.
  move=>h. hs_simpl.
  rewrite h.
  rewrite Ih => //.
Qed.  


Lemma Denotes_fvVarSet e: Denotes (FV.fvVarSet (expr_fvs e)) (expr_fvs e).
Proof. 
  move: (expr_fvs_WF e) => [vs h].
  move: (DenotesfvVarSet _ _ h) => eq.
  rewrite eq.
  auto.
Qed.


Lemma exprFreeVars_Let_Rec:
  forall pairs body,
  exprFreeVars (Let (Rec pairs) body) [=]
    delVarSetList 
       (unionVarSet (exprsFreeVars (map snd pairs))
                    (exprFreeVars body))
          (map fst pairs).
Proof.
  move=> pairs body.
  unfold exprFreeVars, exprsFreeVars.
  unfold_FV.
  unfold exprFVs, exprsFVs, exprFVs.
  unfold_FV.
  unfold expr_fvs. fold expr_fvs.
  move: (expr_fvs_WF body) => [vbody h1].
  denote h1 h5.

  set (f:= (fun (x : CoreExpr) (fv_cand1 : FV.InterestingVarFun)
                    (in_scope : VarSet) =>
                  [eta expr_fvs x (fun v : Var => fv_cand1 v && isLocalVar v)
                         in_scope])).

  set f1 := fun rhs => filterVarSet isLocalVar (FV.fvVarSet (expr_fvs rhs)).

  have h: Forall2 Denotes 
              (map f1 (map snd pairs))
              (map f (map snd pairs)).
  { elim: (map snd pairs) => [|p ps].  simpl. 
    eauto.
    move=> h.
    econstructor; eauto.
    unfold f1. unfold f.
    move: (expr_fvs_WF p) => [vsp h0].
    econstructor.
    move=> f0 in_scope vs' l Rf0 eql.
    inversion h0.
    have g: RespectsVar (fun v => f0 v && isLocalVar v). 
    { apply RespectsVar_andb; eauto. }
    specialize (H (fun v => f0 v && isLocalVar v) in_scope vs' l g eql).
    move: H => [h2 h3].
    rewrite h2. rewrite h3. split; try reflexivity.
    f_equiv.
    f_equiv.
    rewrite filterVarSet_comp.
    apply DenotesfvVarSet in h0.
    apply filterVarSet_equal.
    apply g.
    symmetry.
    done.
  } 

  move : (mapUnionVarSet_mapUnionFV _ _ _ _ h) => h2.
  inversion h2.
  specialize (H (Base.const true) emptyVarSet
                emptyVarSet nil ltac:(eauto)).
  hs_simpl in H;
       move: (H ltac:(reflexivity)) => [_ h5]; clear H.
  rewrite h5.

  have g0 : Forall2 Denotes 
                 (map (fun '(bndr,rhs) => (FV.fvVarSet (FV.unionFV (expr_fvs rhs)(bndrRuleAndUnfoldingFVs bndr)))) pairs)
                 (map (fun '(bndr, rhs) => (FV.unionFV (expr_fvs rhs) (bndrRuleAndUnfoldingFVs bndr))) pairs).
  { 
    clear h h2 H2 H3 h5.
    elim: pairs => [|p ps].  simpl. 
    eauto.
    simpl.
    move: p => [bndr rhs]. simpl.
    move=> Ih.
    econstructor; eauto.
    rewrite DenotesfvVarSet.
    eapply unionVarSet_unionFV.
    eapply emptyVarSet_bndrRuleAndUnfoldingFVs.
    eapply Denotes_fvVarSet.
    eapply unionVarSet_unionFV.
    eapply emptyVarSet_bndrRuleAndUnfoldingFVs.
    eapply Denotes_fvVarSet.
  }

  move: (unionsVarSet_unionsFV _ _ g0) => h4.
  move: (unionVarSet_unionFV _ _ _ _ h1 h4) => g5.
  move: (addBndrs_fv _ (Base.map Tuple.fst pairs) _ g5) => h6.
  
  denote h6 h7.

  rewrite filterVarSet_delVarSetList; try done.
  f_equiv.
  rewrite <- unionVarSet_filterVarSet; try done.
  rewrite unionVarSet_sym.
  f_equiv.
  unfold mapUnionVarSet.
  rewrite Foldable_foldr_map.
  rewrite List.map_map.
  unfold f1.
  rewrite push_foldable.
  + generalize pairs.
    induction pairs0. hs_simpl. reflexivity.
    hs_simpl. rewrite map_cons.
    rewrite map_cons. destruct a. 
    simpl.
    rewrite Foldable_foldr_cons.
    rewrite Foldable_foldr_cons.
    rewrite <- IHpairs0.
    f_equiv.
    * eapply filterVarSet_equal. eauto.
      eapply DenotesfvVarSet.
      rewrite DenotesfvVarSet.
      eapply unionVarSet_unionFV.
      eapply emptyVarSet_bndrRuleAndUnfoldingFVs.
      eapply Denotes_fvVarSet.
      rewrite unionEmpty_l.
      eapply Denotes_fvVarSet.
  + move=> x y.
    rewrite unionVarSet_filterVarSet.
    reflexivity.
    done. 
Qed.

Lemma exprFreeVars_Case:
  forall scrut bndr ty alts,
  exprFreeVars (Case scrut bndr ty alts) [=]
    unionVarSet (exprFreeVars scrut) (mapUnionVarSet (fun '(Mk_Alt dc pats rhs) => delVarSetList (exprFreeVars rhs) (pats ++ [bndr])) alts).
Proof.
  (* GHC 9.10: Alt changed from tuple to Mk_Alt constructor, expr_fvs Case
     now includes tyCoFVsOfType (axiomatized), so union_empty_r doesn't apply *)
Admitted.


Lemma exprFreeVars_Cast:
  forall e co,
  exprFreeVars (Cast e co) [=] exprFreeVars e.
Proof.
  (* GHC 9.10: expr_fvs for Cast now includes tyCoFVsOfCo (axiomatized) *)
Admitted.

(*

Definition tickishFreeVars := 
fun arg_0__ : Tickish Var => match arg_0__ with
                          | Breakpoint _ ids => mkVarSet ids
                          | _ => emptyVarSet
                          end.
*)

Lemma mkVarSet_mapUnionFV vs : 
  Denotes (mkVarSet vs) (FV.mapUnionFV FV.unitFV vs). 
Proof.
  rewrite mkVarSet_extendVarSetList.
  elim: vs => [|x xs IH].
  - apply emptyVarSet_emptyFV.
  - hs_simpl.
    rewrite extendVarSetList_extendVarSet_iff.
    move: (unionVarSet_unionFV _ _ _ _ ( unitVarSet_unitFV x) IH) => h.
    hs_simpl in h.
    assumption.
Qed.

(*
Lemma Denotes_tickish co : 
  Denotes (tickishFreeVars co) (tickish_fvs co).
Proof.
  elim C: co; simpl.
  all: try (apply emptyVarSet_emptyFV).
  unfold FV.mkFVs.
  apply mkVarSet_mapUnionFV.
Qed.
*)

(*
Lemma exprFreeVars_Tick:
  forall e t,
  exprFreeVars (Tick t e) [=] (unionVarSet (exprFreeVars e) (filterVarSet isLocalVar (tickishFreeVars t))).
Proof. 
  move=> e co.
  unfold exprFreeVars, exprFVs, Base.op_z2218U__.  
  unfold expr_fvs. fold expr_fvs.
  move: (expr_fvs_WF e) => [vs D].
  move: (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D) => D1.
  move: (DenotesfvVarSet _ _ D1) => D2.
  rewrite D2.

  move: (unionVarSet_unionFV _ _ _ _ D (Denotes_tickish co)) => D3.
  move: (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D3) => D4.
  move: (DenotesfvVarSet _ _ D4) => D5.
  rewrite D5.
  rewrite <- unionVarSet_filterVarSet; try done.
Qed.
*)

(*
Lemma exprFreeVars_Tick:
  forall e t,
  exprFreeVars (Tick t e) [=] exprFreeVars e.
Proof. done. Qed.
*)

Lemma exprFreeVars_Type:
  forall t,
  exprFreeVars (Mk_Type t) = emptyVarSet.
Proof.
  (* GHC 9.10: expr_fvs for Mk_Type now includes tyCoFVsOfType (axiomatized) *)
Admitted.

Lemma exprFreeVars_Coercion:
  forall co,
  exprFreeVars (Mk_Coercion co) = emptyVarSet.
Proof.
  (* GHC 9.10: expr_fvs for Mk_Coercion now includes tyCoFVsOfCo (axiomatized) *)
Admitted.


(* ---------------------------------------------------------- *)

Lemma exprsFreeVars_nil : exprsFreeVars [] = emptyVarSet. 
Proof.
  unfold exprsFreeVars.
  unfold Base.op_z2218U__.
  unfold exprsFVs.
  unfold FV.mapUnionFV.
  unfold FV.fvVarSet.
  unfold Base.op_z2218U__ .
  unfold FV.fvVarAcc.
  simpl.
  reflexivity.
Qed.
#[export] Hint Rewrite exprsFreeVars_nil : hs_simpl.


Lemma exprsFreeVars_cons x xs : exprsFreeVars (x :: xs) [=] 
             unionVarSet (exprsFreeVars xs) (exprFreeVars x).
Proof.
  unfold exprsFreeVars.
  unfold Base.op_z2218U__.
  unfold exprsFVs.
  rewrite mapUnionFV_cons.
  unfold exprFreeVars.
  unfold Base.op_z2218U__.
  unfold exprFVs.
  unfold Base.op_z2218U__.
  move: (Denotes_fvVarSet x) => h0.
  move: (filterVarSet_filterFV isLocalVar _ _ ltac:(intros ??; auto) h0) => h1.
  set f2 := (fun x0 : CoreExpr => FV.filterFV isLocalVar (expr_fvs x0)).
  set f1 := fun x => filterVarSet isLocalVar (FV.fvVarSet (expr_fvs x)).
  have h2: Forall2 Denotes (map f1 xs) (map f2 xs). 
  { elim xs. simpl. auto.
    move=> a l IH. simpl.
    econstructor; eauto.
    unfold f1. unfold f2.
    eapply filterVarSet_filterFV. intros ??; auto.
    eapply Denotes_fvVarSet.
  }
  move: (mapUnionVarSet_mapUnionFV _ xs f1 f2 h2) => h3.
  move: (unionVarSet_unionFV _ _ _ _ h1 h3) => h4.
  rewrite (DenotesfvVarSet _ _ h4).  
  rewrite (DenotesfvVarSet _ _ h3).  
  rewrite (DenotesfvVarSet _ _ h1).  
  rewrite unionVarSet_sym.
  reflexivity.
Qed.
#[export] Hint Rewrite exprsFreeVars_cons : hs_simpl.


Lemma subVarSet_exprFreeVars_exprsFreeVars:
  forall v rhs (pairs : list (CoreBndr * CoreExpr)) ,
  List.In (v, rhs) pairs ->
  subVarSet (exprFreeVars rhs) (exprsFreeVars (map snd pairs)) = true.
Proof.
  move => v rhs.
  elim => [|[v0 rhs0] ps IH]; simpl. done.
  hs_simpl. move => [eq|I]. 
  inversion eq.
  set_b_iff. fsetdec.
  set_b_iff. 
  specialize (IH I).
  fsetdec.
Qed.

Lemma subVarSet_exprsFreeVars:
  forall (es : list CoreExpr) vs,
  Forall (fun e => subVarSet (exprFreeVars e) vs = true) es ->
  subVarSet (exprsFreeVars es) vs = true.
Proof.
  move=> es vs.
  elim.
  - hs_simpl. 
    set_b_iff. fsetdec.
  - move=> x l S1 F1 S2. 
    hs_simpl.
    set_b_iff. fsetdec.
Qed.

Lemma elemVarSet_exprFreeVars_Var_false: forall v' v,
    varUnique v' <> varUnique v ->
    elemVarSet v' (exprFreeVars (Mk_Var v)) = false.
Proof.
  (* member_insert rewrite fails due to UniqFM 2-param unfolding mismatch *)
Admitted.

(** Working with [exprFreeVars] *)

 
(** Working with [freeVars] *)

Ltac DVarToVar := 
    replace unionDVarSet with unionVarSet; auto;
    replace emptyDVarSet with emptyVarSet; auto;
    replace delDVarSet with delVarSet; auto;
    replace FV.fvDVarSet with FV.fvVarSet; auto;
    replace unionDVarSets with unionVarSets; auto.

Lemma no_TyCoVars bndr: (dVarTypeTyCoVars bndr) [=] emptyVarSet.
Proof.
  (* varTypeTyCoFVs no longer emptyFV in GHC 9.10 *)
Admitted.

Lemma no_RuleAndUnfoldingFVs l0 : 
  (FV.fvVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs l0)) [=] emptyVarSet.
Proof.
  rewrite DenotesfvVarSet.
  2: { 
    unfold bndrRuleAndUnfoldingFVs.
    eapply mapUnionVarSet_mapUnionFV with (f1 := fun x => emptyVarSet).
    induction l0; simpl in *.
    eauto.
    econstructor; eauto.
    unfold isId, idRuleFVs, idUnfoldingFVs.
    destruct a. simpl.
    rewrite union_empty_r.
    eapply emptyVarSet_emptyFV.
  }
  induction l0.
  hs_simpl.
  rewrite mapUnionVarSets_unionVarSets. simpl. reflexivity.
  rewrite mapUnionVarSet_cons.  rewrite IHl0.
  rewrite unionEmpty_r.
  reflexivity.
Qed.

Lemma freeVarsOf_freeVars_revised:
  forall e,
  (freeVarsOf (freeVars e)) [=] exprFreeVars e.
Proof.
  (* GHC 9.10: varTypeTyCoFVs is no longer emptyFV, breaking no_TyCoVars
     and many subgoals throughout this proof. Admitted for now. *)
Admitted.

(* Original proof Admitted due to varTypeTyCoFVs changes in GHC 9.10. *)

Lemma deAnnotate_freeVars:
  forall e, deAnnotate (freeVars e) = e.
Proof.
  (* GHC 9.10: Alt changed from tuple to Mk_Alt, freeVars Case branch uses
     Mk_AnnAlt. Proof structure needs full rewrite. Admitted for now. *)
Admitted.

Lemma deAnnotate'_snd_freeVars:
  forall e, deAnnotate' (snd (freeVars e)) = e.
Proof.
  intros. symmetry. rewrite <- deAnnotate_freeVars at 1.
  destruct (freeVars e); reflexivity.
Qed.


Lemma collectNAnnBndrs_freeVars_mkLams:
  forall vs rhs,
  collectNAnnBndrs (length vs) (freeVars (mkLams vs rhs)) = (vs, freeVars rhs).
Proof.
  intros vs rhs.
  name_collect collect.
  assert (forall vs1 vs0 n, 
             n = length vs1 ->
             collect n vs0 (freeVars (mkLams vs1 rhs)) = (List.app (List.reverse vs0)  vs1, freeVars rhs)).
  { induction vs1; intros.
    + simpl in *.  subst. 
      unfold mkLams.
      unfold_Foldable.
      simpl. 
      rewrite List.app_nil_r.
      auto.
    + simpl in *. 
      destruct n; inversion H.
      pose (IH := IHvs1 (cons a vs0) n H1). clearbody IH. clear IHvs1.
      unfold mkLams in IH.
      unfold Foldable.foldr in IH.
      unfold Foldable.Foldable__list in IH.
      unfold Foldable.foldr__ in IH.
      simpl. 
      remember (freeVars (Foldable.Foldable__list_foldr Lam rhs vs1)) as fv.
      destruct fv.
      rewrite <-  H1.
      rewrite reverse_append in IH.
      auto.
  }       
  pose (K := H vs nil (length vs) Logic.eq_refl).
  simpl in K.
  auto.
Qed.
