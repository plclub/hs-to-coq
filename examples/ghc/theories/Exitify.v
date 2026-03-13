Require Import GHC.Base.
Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.

Require Import Proofs.Prelude.

Require Import Psatz.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.NArith.BinNat.
Require Import Coq.Program.Equality. (* for dependent destruction *)
 
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Proofs.Axioms.
Require Import Proofs.Base.
Require Import Proofs.JoinPointInvariants.
Require Import Proofs.ScopeInvariant.
Require Import Proofs.StateLogic.
Require Import Proofs.CoreInduct.
Require Import Proofs.Forall.
Require Import Proofs.Core.
Require Import Proofs.CoreFVs.
Require Import Proofs.GhcTactics.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetStrong.
Require Import Proofs.VarEnv.
Require Import Proofs.Unique.
Require Import Proofs.GhcUtils.
Require Import Proofs.Util.

Set Bullet Behavior "Strict Subproofs".
Opaque Base.hs_string__.
Close Scope Z_scope.

(** * Proofs about the Exitification pass *)

Lemma etaUnique: forall u, Unique.MkUnique (Unique.getKey u) = u.
Proof. intro u. destruct u. simpl. auto. Qed.

(* GHC 9.10: initExitJoinUnique moved to GHC.Builtin.Uniques (not translated) *)
Lemma isLocalId_mkLocalId : forall u s w ty,
  Unique.isLocalUnique u = true ->
  is_true
    (isLocalId
       (mkLocalId (Name.mkSystemVarName u s) w ty)).
Proof.
  intros u s w ty Hlocal.
  unfold mkLocalId, Id.mkLocalIdWithInfo, mkLocalVar, mk_id.
  unfold isLocalId.
  unfold Name.mkSystemVarName, Name.mkSystemName, Name.mkSystemNameAt.
  simpl. exact Hlocal.
Qed.        



(**
In this module, we prove that the exitification pass preserves the various
invariants of Core. But first we need to do some yak-shaving to deal
with the kind of definitions that we get out of hs-to-coq here.
*)



(** ** A domain predicate for [go] *)

(**
The local function [go] of [exitifyRec] is defined via [deferredFix]. Unfortunately, it
is not defined everywhere, but only on certain well-formed terms. Because it calls
[error] (i.e. [default]) in the other cases, it is not possibly to prove termination 
using [deferredFix_eq_on] on all input, but we need to restrict accordingly.

The following predicate describes expressions on which [go] does not call [error]:
*)

Definition alt_rhs {b} (alt : Alt b) : Expr b :=
  let '(Mk_Alt _ _ rhs) := alt in rhs.

Definition alt_pats {b} (alt : Alt b) : list b :=
  let '(Mk_Alt _ pats _) := alt in pats.

Definition alt_con {b} (alt : Alt b) : AltCon :=
  let '(Mk_Alt con _ _) := alt in con.

Inductive GoDom : CoreExpr -> Prop :=
  | GoDom_Var  v: GoDom (Mk_Var v)
  | GoDom_Lit  l: GoDom (Lit l)
  | GoDom_App e1 e2:
    GoDom e1 -> GoDom (App e1 e2)
  | GoDom_Lam v e:
    GoDom e -> GoDom (Lam v e)
  | GoDom_LetNonRec_Join v rhs e:
    GoDom_JoinPair v rhs ->
    GoDom e ->
    GoDom (Let (NonRec v rhs) e)
  | GoDom_LetNonRec v rhs e:
    GoDom_Pair v rhs ->
    GoDom e ->
    GoDom (Let (NonRec v rhs) e)
  | GoDom_LetRec_Join pairs e:
    Forall (fun p => GoDom_JoinPair (fst p) (snd p)) pairs ->
    pairs <> []  -> (* because [go] uses [head] *)
    GoDom e ->
    GoDom (Let (Rec pairs) e)
  | GoDom_LetRec pairs e:
    Forall (fun p => GoDom_Pair (fst p) (snd p)) pairs ->
    pairs <> [] -> (* because [go] uses [head] *)
    GoDom e ->
    GoDom (Let (Rec pairs) e)
  | GoDom_Case scrut bndr ty alts:
    Forall (fun alt => GoDom (alt_rhs alt)) alts ->
    GoDom (Case scrut bndr ty alts)
  | GoDom_Cast e c:
    GoDom e ->
    GoDom (Cast e c)
(*  | GoDom_Tick  e t:
    GoDom e ->
    GoDom (Tick t e) *)
  | GoDom_Type t:
    GoDom (Mk_Type t)
  | GoDom_Coercion t:
    GoDom (Mk_Coercion t) 
 with GoDom_JoinPair : CoreBndr -> CoreExpr -> Prop :=
  | GoDom_Join v params rhs :
    isJoinId_maybe v = Some (length params) ->
    GoDom rhs ->
    GoDom_JoinPair v (mkLams params rhs)
    (* This is crucial: Every join point has enough lambdas *)
 with GoDom_Pair : CoreBndr -> CoreExpr -> Prop :=
  | GoDom_NotJoin v rhs :
    isJoinId_maybe v = None ->
    GoDom_Pair v rhs
  .

Record JoinRHS := MkJoinRHS
  { jrhs_v : CoreBndr;
    jrhs_params : list CoreBndr;
    jrhs_rhs : CoreExpr;
    jrhs_isJoinRHS : isJoinId_maybe jrhs_v = Some (length jrhs_params)
  }.
  
Lemma GoDom_JoinPair_JoinRHS:
  forall v rhs,
  GoDom_JoinPair v rhs ->
  exists r, (v, rhs) = (fun '(MkJoinRHS j params body _) => (j, mkLams params body)) r.
Proof.
  intros v rhs H.
  inversion H; subst.
  eexists (MkJoinRHS v params rhs0 _).
  simpl. reflexivity.
  Unshelve. assumption.
Qed.

Lemma GoDom_JoinPair_JoinRHS_pairs:
  forall pairs,
  Forall (fun p => GoDom_JoinPair (fst p) (snd p)) pairs ->
  exists pairs', pairs = map (fun '(MkJoinRHS j params body _) => (j, mkLams params body)) pairs'.
Proof.
  intros pairs H. induction H.
  - exists nil. reflexivity.
  - destruct x as [v rhs]. simpl in H.
    apply GoDom_JoinPair_JoinRHS in H. destruct H as [r Hr].
    destruct IHForall as [pairs' Hpairs'].
    exists (r :: pairs'). simpl. rewrite <- Hpairs'.
    inversion Hr. reflexivity.
Qed.

(** The predicate is actually a corollary of being join-point valid.

So we could just use [isJoinPointsValid e n jps = true] instead of [GoDom], but that
would add the complexity of the following proof to other proofs in this module.
*)


Program Fixpoint isJoinPointsValid_GoDom
  e n jps { measure e (CoreLT) } :
  isJoinPointsValid e n jps = true ->
  GoDom e := _.
Next Obligation.
  rename isJoinPointsValid_GoDom into IH.
  destruct e.
  * constructor.
  * constructor.
  * simpl in H. simpl_bool. destruct H as [He1 He2].
    apply IH in He1; only 2: Core_termination.
    constructor. assumption.
  * simpl in H. simpl_bool. destruct H as [_ He].
    apply IH in He; only 2: Core_termination.
    constructor. assumption.
  * simpl in H.
    destruct b as [v rhs | pairs].
    + simpl_bool. destruct H as [Hpair He].
      fold isJoinPointsValidPair in Hpair.
      destruct (isJoinId_maybe v) eqn:HiJI.
      - apply GoDom_LetNonRec_Join.
        ** eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS in Hpair; only 2: apply HiJI.
           destruct  (isJoinRHS_mkLams3 _ _ _ Hpair) as [rhs' [vs [Heq1 Heq2]]].
           subst.
           apply isJoinRHS_mkLams2 in Hpair.
           destruct Hpair as [_ Hpair].
           apply IH in Hpair; only 2: Core_termination.
           constructor; assumption.
        ** eapply IH in He; only 2: Core_termination.
           assumption.
      - eapply isJoinPointsValidPair_isJoinPointsValid in Hpair; only 2: apply HiJI.
        apply GoDom_LetNonRec.
        ** constructor. assumption.
        ** eapply IH in He; only 2: Core_termination.
           assumption.
    + simpl_bool. destruct H as [[HnotNull Hall_or_none] [Hpair He]].
      fold isJoinPointsValidPair in Hpair.
      simpl_bool. destruct Hall_or_none as [Hnone|Hall].
      - apply GoDom_LetRec.
        ** rewrite forallb_forall in Hnone.
           rewrite Forall_forall.
           intros [v rhs] HIn. specialize (Hnone _ HIn).
           constructor. simpl in *.
           rewrite negb_true_iff in Hnone.
           rewrite isJoinId_eq in Hnone.
           destruct_match; congruence.
        ** destruct pairs; simpl in HnotNull; congruence.
        ** eapply IH in He; only 2: Core_termination.
           assumption.
      - apply GoDom_LetRec_Join.
        ** rewrite forallb_forall in Hpair.
           rewrite forallb_forall in Hall.
           rewrite Forall_forall.
           intros [v rhs] HIn.
           specialize (Hall _ HIn).
           specialize (Hpair _ HIn).
           simpl in *.
           rewrite isJoinId_eq in Hall; destruct_match; try congruence; clear Hall.
           eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS in Hpair; only 2: apply Heq.
           destruct  (isJoinRHS_mkLams3 _ _ _ Hpair) as [rhs' [vs [Heq1 Heq2]]].
           subst.
           apply isJoinRHS_mkLams2 in Hpair.
           destruct Hpair as [_ Hpair].
           apply IH in Hpair; only 2: Core_termination.
           constructor; assumption.
        ** destruct pairs; simpl in HnotNull; congruence.
        ** eapply IH in He; only 2: Core_termination.
           assumption.
   * simpl in H.  simpl_bool. destruct H as [[HnotJoin He] Halts].
     constructor.
     rewrite Forall_forall.
     intros [dc pats rhs] HIn.
     rewrite forallb_forall in Halts. specialize (Halts _ HIn).
     simpl in *.
     simpl_bool. destruct Halts as [HnotJoins Hrhs].
     apply IH in Hrhs; only 2: Core_termination.
     assumption.
   * simpl in H.
     apply IH in H; only 2: Core_termination.
     constructor. assumption.
(*   * simpl in H.
     apply IH in H; only 2: Core_termination.
     constructor. assumption. *)
   * constructor.
   * constructor. 
Qed.

Lemma isValidJoinPointsPair_GoDom_JoinPair:
  forall v e jps,
  isValidJoinPointsPair v e jps = true ->
  GoDom_JoinPair v e.
Proof.
  intros v e jps H.
  unfold isValidJoinPointsPair in H.
  destruct (isJoinId_maybe v) eqn:HiJI; try discriminate.
  destruct (isJoinRHS_mkLams3 _ _ _ H) as [body [vs [Heq1 Heq2]]].
  subst.
  apply isJoinRHS_mkLams2 in H.
  destruct H as [_ Hvalid].
  apply isJoinPointsValid_GoDom in Hvalid.
  constructor; assumption.
Qed.

(** * Working within [exitifyRec] *)

(**
A large part of this module deals with what happens “inside” [exitifyRec]. So instead
of passing the arguments to [exitifyRec] around everywhere, we use a section to “enter
this context”:
*)

Section in_exitifyRec.

  (* For better proof paralellism, see 
     https://coq.inria.fr/refman/proof-engine/proof-handling.html#coq:opt.default-proof-using-expression
   *)
  Set Default Proof Using "Type".

  (** These are (almost) the parameters of [exitifyRec] *)
  Variable in_scope : InScopeSet.
  Variable pairs : list (CoreBndr * CoreExpr).
  (** almost, because [exitifyRec] is actually called with the following
      in-scope-set, but we need access to the underlying [in_scope] in our proofs.
  *)
  Definition in_scope2 := extendInScopeSetList in_scope (map fst pairs).

  (** Not a parameter of [exitifyRec], but when doing the
      proofs about join-point-validity, we need to know which join points are
      in scope outside the [Rec] *)
  Variable jps : VarSet.

  (** Now we give  names to the local functions of [exitifyRec].
     See http://www.joachim-breitner.de/blog/738-Verifying_local_definitions_in_Coq
     for more on that idiom.
   *)

  (* GHC 9.10: exitifyRec is axiomatized, so we cannot unfold it to extract
     local definitions. All definitions and proofs in this section are Admitted. *)

  Definition isvs := getInScopeVars in_scope.
  Definition fs := map fst pairs.

  Hypothesis pairs_WS :
    Forall (fun p => GoodLocalVar (fst p) /\ WellScoped (snd p) (extendVarSetList (isvs) fs)) pairs.

  Hypothesis pairs_VJPP :
    Forall (fun p => isValidJoinPointsPair (fst p) (snd p) (updJPSs jps fs) = true) pairs.

  Hypothesis pairs_NoDup :
    NoDup (map varUnique fs).

  Hypothesis jps_subset_isvs :
    subVarSet jps (isvs) = true.

  Theorem exitifyRec_WellScoped:
    forall body,
    WellScoped body (extendVarSetList (isvs) fs) ->
    WellScoped (mkLets (exitifyRec (extendInScopeSetList in_scope fs) pairs) body) (isvs).
  Admitted.

  Theorem exitifyRec_JPI:
    forall body n,
    pairs <> [] ->
    let jps' := updJPSs jps fs in
    isJoinPointsValid body 0 jps' = true ->
    isJoinPointsValid (mkLets (exitifyRec (extendInScopeSetList in_scope fs) pairs) body) n jps = true.
  Admitted.

End in_exitifyRec.

(** This concludes the proofs about [exitifyRec]. We can sum up all the above 
    in a single lemma.
    I also introduces an equality for fst_pairs for easier application.
    I also groups all assumptions about [pairs] in one big Forall.
*)
Lemma exitifyRec_WellScoped_JPI:
  forall (in_scope : InScopeSet) (pairs : list (CoreBndr * CoreExpr)) fst_pairs n jps,
  fst_pairs = map fst pairs ->
  subVarSet jps (isvs in_scope) = true ->
  NoDup (map varUnique fst_pairs) ->
  pairs <> [] ->
  Forall (fun '(v,rhs) =>
     GoodLocalVar v /\
     WellScoped rhs (extendVarSetList (isvs in_scope) fst_pairs) /\
     isValidJoinPointsPair v rhs (updJPSs jps fst_pairs) = true
  ) pairs ->
  forall body : CoreExpr,
  WellScoped body (extendVarSetList (isvs in_scope) fst_pairs) ->
  isJoinPointsValid body 0 (updJPSs jps fst_pairs) = true ->
  WellScoped
    (mkLets (exitifyRec (extendInScopeSetList in_scope fst_pairs) pairs) body)
    (isvs in_scope) /\
  isJoinPointsValid
    (mkLets (exitifyRec (extendInScopeSetList in_scope fst_pairs) pairs) body) n jps = true.
Proof.
  intros in_scope0 pairs0 fst_pairs0 n0 jps0 Hfst Hjps_sub Hnodup Hne Hpairs body Hbody_WS Hbody_JPI.
  subst fst_pairs0.
  split.
  - eapply (exitifyRec_WellScoped in_scope0 pairs0 jps0); auto.
    + rewrite Forall_forall in *. intros [v rhs] HIn.
      specialize (Hpairs _ HIn). simpl in *. tauto.
    + rewrite Forall_forall in *. intros [v rhs] HIn.
      specialize (Hpairs _ HIn). simpl in *. tauto.
  - eapply (exitifyRec_JPI in_scope0 pairs0 jps0); auto.
    + rewrite Forall_forall in *. intros [v rhs] HIn.
      specialize (Hpairs _ HIn). simpl in *. tauto.
    + rewrite Forall_forall in *. intros [v rhs] HIn.
      specialize (Hpairs _ HIn). simpl in *. tauto.
Qed.

(** ** Verification of [go] in [exitifyProgram] *)

(** For the rest of the module, we deal with well-scopedness and join-point-validity
    simultaneously. We need always both anyways, because the join-point-validity
    implies that the expression in is in the domain of 

    We extract the local [go] from [exitifyProgram], and use induction
    to show that it preserves both invariants.
*)

Definition top_go := ltac:(
  let rhs := eval cbv beta delta [exitifyProgram] in (exitifyProgram []) in
  lazymatch rhs with | (let x := ?rhs in ?body) => 
    exact rhs
  end).

Lemma mapSnd_map:
  forall {a b c} (f : b -> c) (xs : list (a * b)),
  Util.mapSnd f xs = map (fun x => (fst x, f (snd x))) xs.
Proof. intros. induction xs. reflexivity. simpl. destruct a0. rewrite <- IHxs.  reflexivity. Qed.

Lemma top_go_mkLams:
  forall in_scope body vs,
  top_go in_scope (mkLams vs body) =
  mkLams vs (top_go (extendInScopeSetList in_scope vs) body).
Proof.
  intros in_scope0 body vs.
  revert in_scope0 body.
  induction vs as [|v vs' IH]; intros.
  - simpl. rewrite extendInScopeSetList_nil. reflexivity.
  - change (mkLams (v :: vs') body) with (Lam v (mkLams vs' body)).
    change (mkLams (v :: vs') (top_go (extendInScopeSetList in_scope0 (v :: vs')) body))
      with (Lam v (mkLams vs' (top_go (extendInScopeSetList in_scope0 (v :: vs')) body))).
    simpl top_go at 1.
    rewrite extendInScopeSetList_cons.
    f_equal.
    apply IH.
Qed.

Ltac solve_subVarSet :=
  unfold isvs;
  rewrite ?getInScopeVars_extendInScopeSet;
  rewrite ?getInScopeVars_extendInScopeSetList;
  rewrite ?extendVarSetList_append;
  rewrite ?extendVarSetList_cons;
  rewrite ?extendVarSetList_nil;
  rewrite ?updJPSs_append;
  rewrite ?updJPSs_cons;
  rewrite ?updJPSs_nil;
  repeat first [ apply subVarSet_updJPSs_extendVarSetList
               | apply subVarSet_updJPS_extendVarSet
               | apply subVarSet_delVarSetList_extendVarSetList
               | apply subVarSet_delVarSet_extendVarSet
               ];
  first [ assumption
        | apply subVarSet_emptyVarSet
        ].

(**
Nothing really interesting is happening here, just lots oftaking the
conjunction between the invariants apart and combining them again, and 
lots of shifting around [VarSet]s and [InScopeSets], and eventually a call to
[exififyRec]. This really should be simpler.
*)

Lemma top_go_WellScoped_JPI :
  forall e in_scope n jps,
  WellScoped e (getInScopeVars in_scope)->
  isJoinPointsValid e n jps = true ->
  subVarSet jps (isvs in_scope) = true ->
  WellScoped (top_go in_scope e) (getInScopeVars in_scope) /\
  isJoinPointsValid (top_go in_scope e) n jps = true.
Proof.
  (* TODO: Program Fixpoint proof on CoreLT. Requires ~200 lines
     of structural induction with exitifyRec_WellScoped_JPI at the
     Let/Rec/join case. *)
Admitted.

Lemma Forall_flattenBinds:
  forall {b} P (binds : list (Bind b)),
  Forall P (flattenBinds binds) <->
  Forall (fun bind => Forall P (flattenBinds [bind])) binds.
Proof.
  intros b P binds.
  induction binds as [|bind binds' IH].
  - simpl. split; constructor.
  - destruct bind as [v rhs | pairs].
    + simpl. split; intro H.
      * inversion H; subst. constructor.
        -- constructor; [assumption | constructor].
        -- apply IH. assumption.
      * inversion H; subst. inversion H2; subst.
        constructor; [assumption | apply IH; assumption].
    + simpl. split; intro H.
      * apply Forall_app in H. destruct H as [H1 H2].
        constructor; [|apply IH; assumption].
        rewrite Forall_app. split; [assumption | constructor].
      * inversion H; subst.
        apply Forall_app. split.
        -- rewrite Forall_app in H2. destruct H2. assumption.
        -- apply IH. assumption.
Qed.

Lemma bindersOfBinds_cons:
  forall bind (pgm : CoreProgram),
  bindersOfBinds (bind :: pgm) = bindersOf bind ++ bindersOfBinds pgm.
Proof.
  intros bind pgm.
  unfold bindersOfBinds.
  rewrite Foldable.hs_coq_foldr_list.
  simpl. reflexivity.
Qed.

(** ** Verification of [exitifyProgram] *)

(** Local definitions extracted from [exitifyProgram] for proof use. *)

Definition ep_in_scope (pgm : CoreProgram) :=
  CoreUtils.extendInScopeSetBndrs emptyInScopeSet pgm.

Definition ep_goTopLvl (in_scope : InScopeSet) (bind : CoreBind) :=
  match bind with
  | NonRec v e => NonRec v (top_go in_scope e)
  | Rec pairs => Rec (GHC.Base.map (Data.Bifunctor.second (top_go in_scope)) pairs)
  end.

Lemma exitifyProgram_eq pgm :
  exitifyProgram pgm = GHC.Base.map (ep_goTopLvl (ep_in_scope pgm)) pgm.
Proof. unfold exitifyProgram, ep_goTopLvl, ep_in_scope. f_equal. Qed.

Lemma bindersOf_ep_goTopLvl :
  forall in_scope bind, bindersOf (ep_goTopLvl in_scope bind) = bindersOf bind.
Proof.
  intros. unfold ep_goTopLvl. destruct bind.
  - reflexivity.
  - simpl. rewrite !bindersOf_Rec_cleanup.
    rewrite hs_coq_map. rewrite map_map.
    apply map_ext. intros [v rhs]. reflexivity.
Qed.

Lemma bindersOfBinds_ep_goTopLvl :
  forall in_scope pgm,
  bindersOfBinds (GHC.Base.map (ep_goTopLvl in_scope) pgm) = bindersOfBinds pgm.
Proof.
  intros. induction pgm as [|bind pgm' IH].
  - reflexivity.
  - rewrite hs_coq_map. simpl.
    rewrite !bindersOfBinds_cons.
    rewrite <- hs_coq_map. rewrite IH. f_equal.
    apply bindersOf_ep_goTopLvl.
Qed.

(* Each bind: foldBindersOfBindStrict = foldl' over bindersOf *)
Lemma foldBindersOfBindStrict_bindersOf :
  forall (s : VarSet) (bind : CoreBind),
  foldBindersOfBindStrict extendVarSet s bind =
  Data.Foldable.foldl' extendVarSet s (bindersOf bind).
Proof.
  intros s [v rhs | pairs0].
  - (* NonRec *)
    simpl. rewrite Foldable_foldl'_cons. rewrite Foldable_foldl'_nil. reflexivity.
  - (* Rec *)
    simpl. f_equal. symmetry. apply bindersOf_Rec_cleanup.
Qed.

(* Generalized: folding bind-by-bind = folding over flat binder list *)
Lemma foldBindersOfBindsStrict_bindersOfBinds :
  forall (s : VarSet) (pgm : CoreProgram),
  foldBindersOfBindsStrict extendVarSet s pgm =
  Data.Foldable.foldl' extendVarSet s (bindersOfBinds pgm).
Proof.
  intros s pgm. revert s.
  induction pgm as [|bind rest IH]; intro s.
  - (* nil *)
    unfold foldBindersOfBindsStrict. rewrite Foldable_foldl'_nil.
    replace (bindersOfBinds (@nil CoreBind)) with (@nil Var) by reflexivity.
    rewrite Foldable_foldl'_nil. reflexivity.
  - (* cons *)
    unfold foldBindersOfBindsStrict.
    rewrite Foldable_foldl'_cons.
    rewrite bindersOfBinds_cons.
    rewrite Foldable_foldl'_app.
    change (Data.Foldable.foldl' (foldBindersOfBindStrict extendVarSet)
              (foldBindersOfBindStrict extendVarSet s bind) rest)
      with (foldBindersOfBindsStrict extendVarSet
              (foldBindersOfBindStrict extendVarSet s bind) rest).
    rewrite IH.
    f_equal.
    apply foldBindersOfBindStrict_bindersOf.
Qed.

Lemma getInScopeVars_ep_in_scope pgm :
  getInScopeVars (ep_in_scope pgm) = mkVarSet (bindersOfBinds pgm).
Proof.
  unfold ep_in_scope, CoreUtils.extendInScopeSetBndrs, emptyInScopeSet.
  simpl.
  unfold mkVarSet, UniqSet.mkUniqSet, emptyVarSet, extendVarSet.
  rewrite foldBindersOfBindsStrict_bindersOfBinds.
  reflexivity.
Qed.

(** At last, the final result. *)

Theorem exitifyProgram_WellScoped_JPV:
  forall pgm,
  WellScopedProgram pgm ->
  isJoinPointsValidProgram pgm ->
  WellScopedProgram (exitifyProgram pgm) /\
  isJoinPointsValidProgram (exitifyProgram pgm).
Proof.
  intros pgm HWS HJPV.
  rewrite exitifyProgram_eq.

  destruct HWS as [HNoDup HWS].
  rewrite Forall'_Forall in HWS.
  unfold isJoinPointsValidProgram in HJPV.

  (* Helper: each bind individually preserves both invariants *)
  assert (Hbind: forall bind,
    Forall (fun p => WellScoped (snd p) (mkVarSet (bindersOfBinds pgm)))
           (flattenBinds [bind]) ->
    Forall (fun '(v,e) => isJoinId v = false /\
            isJoinPointsValid e 0 emptyVarSet = true) (flattenBinds [bind]) ->
    Forall (fun p => WellScoped (snd p) (mkVarSet (bindersOfBinds pgm)))
           (flattenBinds [ep_goTopLvl (ep_in_scope pgm) bind]) /\
    Forall (fun '(v,e) => isJoinId v = false /\
            isJoinPointsValid e 0 emptyVarSet = true)
           (flattenBinds [ep_goTopLvl (ep_in_scope pgm) bind])).
  { intros bind HbWS HbJPV.
    destruct bind as [v rhs | pairs0].
    - (* NonRec *)
      simpl in *.
      inversion_clear HbWS as [|?? Hws _].
      inversion_clear HbJPV as [|?? Hjpv _].
      simpl in Hjpv. destruct Hjpv as [HisJoinId Hjpv_rhs].
      pose proof (top_go_WellScoped_JPI rhs (ep_in_scope pgm) 0 emptyVarSet) as [HtgWS HtgJPV].
      { rewrite getInScopeVars_ep_in_scope. exact Hws. }
      { exact Hjpv_rhs. }
      { apply subVarSet_emptyVarSet. }
      split; (constructor; [|constructor]).
      + simpl. rewrite <- getInScopeVars_ep_in_scope. exact HtgWS.
      + simpl. exact (conj HisJoinId HtgJPV).
    - (* Rec *)
      simpl in *.
      rewrite app_nil_r in *.
      split.
      + rewrite hs_coq_map. rewrite Forall_map.
        rewrite Forall_forall. intros [v' e'] HIn'.
        rewrite Forall_forall in HbWS, HbJPV.
        specialize (HbWS _ HIn'). specialize (HbJPV _ HIn').
        simpl in *. destruct HbJPV as [? ?].
        pose proof (top_go_WellScoped_JPI e' (ep_in_scope pgm) 0 emptyVarSet) as [HtgWS HtgJPV].
        { rewrite getInScopeVars_ep_in_scope. exact HbWS. }
        { exact H0. }
        { apply subVarSet_emptyVarSet. }
        simpl. rewrite <- getInScopeVars_ep_in_scope. exact HtgWS.
      + rewrite hs_coq_map. rewrite Forall_map.
        rewrite Forall_forall. intros [v' e'] HIn'.
        rewrite Forall_forall in HbWS, HbJPV.
        specialize (HbWS _ HIn'). specialize (HbJPV _ HIn').
        simpl in *. destruct HbJPV as [? ?].
        pose proof (top_go_WellScoped_JPI e' (ep_in_scope pgm) 0 emptyVarSet) as [_ HtgJPV].
        { rewrite getInScopeVars_ep_in_scope. exact HbWS. }
        { exact H0. }
        { apply subVarSet_emptyVarSet. }
        split; [exact H | exact HtgJPV].
  }

  split.
  - (* WellScopedProgram *)
    unfold WellScopedProgram.
    rewrite bindersOfBinds_ep_goTopLvl.
    split; [exact HNoDup|].
    rewrite Forall'_Forall.
    rewrite Forall_flattenBinds in *.
    rewrite hs_coq_map. rewrite Forall_map.
    rewrite Forall_forall in *.
    intros bind HIn.
    exact (proj1 (Hbind bind (HWS bind HIn) (HJPV bind HIn))).
  - (* isJoinPointsValidProgram *)
    unfold isJoinPointsValidProgram.
    rewrite Forall_flattenBinds in *.
    rewrite hs_coq_map. rewrite Forall_map.
    rewrite Forall_forall in *.
    intros bind HIn.
    exact (proj2 (Hbind bind (HWS bind HIn) (HJPV bind HIn))).
Qed.

Print Assumptions exitifyProgram_WellScoped_JPV.
