Require Import GHC.Base.
Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

Require Import Psatz.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.

Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.

Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

Require Import JoinPointInvariants.
Require Import ScopeInvariant.
Require Import StateLogic.
Require Import CoreInduct.
Require Import Forall.
Require Import CoreLemmas.
Require Import CoreFVsLemmas.
Require Import Tactics.
Require Import NCore.
Require Import VectorUtils.

(** ** Punted-on lemmas about GHC functions *)

Instance EqLaws_Unique : EqLaws Unique.Unique. Admitted.
Instance EqExact_Unique : EqExact Unique.Unique. Admitted.

Axiom isJoinId_eq : forall v,
  isJoinId v = match isJoinId_maybe v with | None => false |Some _ => true end.

Axiom isJoinId_isJoinId_maybe: forall v,
  isJoinId v = true ->
  isJoinId_maybe v = Some (idJoinArity v).

Axiom idJoinArity_join: forall v a,
  isJoinId_maybe v = Some a -> idJoinArity v = a.

Axiom isJoinId_maybe_uniqAway:
  forall s v, 
  isJoinId_maybe (uniqAway s v) = isJoinId_maybe v.

Axiom isJoinId_maybe_setIdOccInfo:
  forall v occ_info, 
  isJoinId_maybe (setIdOccInfo v occ_info) = isJoinId_maybe v.

Axiom isJoinId_maybe_asJoinId:
  forall v a,
  isJoinId_maybe (asJoinId v a) = Some a.

Axiom dVarSet_freeVarsOf_Ann:
  (* @lastland, this is one spec that you might want to do *)
  forall ann_e, dVarSetToVarSet (freeVarsOf ann_e) = exprFreeVars (deAnnotate ann_e).

Axiom extendVarSetList_nil:
  forall s,
  extendVarSetList s [] = s.

Axiom extendVarSetList_cons:
  forall s v vs,
  extendVarSetList s (v :: vs) = extendVarSetList (extendVarSet s v) vs.

Axiom extendVarSetList_append:
  forall s vs1 vs2,
  extendVarSetList s (vs1 ++ vs2) = extendVarSetList (extendVarSetList s vs1) vs2.

Axiom elemVarSet_mkVarset_iff_In:
  forall v vs,
  elemVarSet v (mkVarSet vs) = true <->  In (varUnique v) (map varUnique vs).


Axiom elemVarSet_extendVarSet:
  forall v vs v',
  elemVarSet v (extendVarSet vs v') = (varUnique v == varUnique v') || elemVarSet v vs.

Axiom subVarSet_refl:
  forall vs1,
  subVarSet vs1 vs1 = true.

Axiom subVarSet_elemVarSet_true:
  forall v vs vs',
  subVarSet vs vs' = true ->
  elemVarSet v vs = true ->
  elemVarSet v vs' = true.

Axiom subVarSet_elemVarSet_false:
  forall v vs vs',
  subVarSet vs vs' = true ->
  elemVarSet v vs' = false ->
  elemVarSet v vs = false.

Axiom subVarSet_extendVarSetList_l:
  forall vs1 vs2 vs,
  subVarSet vs1 vs2 = true ->
  subVarSet vs1 (extendVarSetList vs2 vs) = true.

Axiom subVarSet_extendVarSetList_r:
  forall vs1 vs2 vs,
  subVarSet vs1 (mkVarSet vs) = true ->
  subVarSet vs1 (extendVarSetList vs2 vs) = true.


Axiom subVarSet_extendVarSet:
  forall vs1 vs2 v,
  subVarSet vs1 vs2 = true ->
  subVarSet vs1 (extendVarSet vs2 v) = true.

Axiom subVarSet_delVarSetList:
  forall vs1 vs2,
  subVarSet (delVarSetList vs1 vs2) vs1 = true.

Axiom disjointVarSet_mkVarSet:
  forall vs1 vs2,
  disjointVarSet vs1 (mkVarSet vs2) = true <->
  Forall (fun v => elemVarSet v vs1 = false) vs2.

Axiom disjointVarSet_subVarSet_l:
  forall vs1 vs2 vs3,
  disjointVarSet vs2 vs3 = true ->
  subVarSet vs1 vs2 = true ->
  disjointVarSet vs1 vs3 = true.
  

Axiom getInScopeVars_extendInScopeSet:
  forall iss v,
  getInScopeVars (extendInScopeSet iss v) = extendVarSet (getInScopeVars iss) v.

Axiom getInScopeVars_extendInScopeSetList:
  forall iss vs,
  getInScopeVars (extendInScopeSetList iss vs) = extendVarSetList (getInScopeVars iss) vs.

Axiom elemVarSet_uniqAway:
  forall v iss vs,
  subVarSet vs (getInScopeVars iss) = true ->
  elemVarSet (uniqAway iss v) vs = false.

Axiom WellScoped_extendVarSet_fresh:
  forall v e vs,
  elemVarSet v (exprFreeVars e) = false ->
  WellScoped e (extendVarSet vs v) <-> WellScoped e vs.

Axiom WellScoped_extendVarSetList_fresh:
  forall vs e vs1,
  disjointVarSet (exprFreeVars e) (mkVarSet vs) = true ->
  WellScoped e (extendVarSetList vs1 vs) <-> WellScoped e vs1.

Axiom WellScoped_extendVarSetList:
  forall vs e vs1,
  disjointVarSet vs1 (mkVarSet vs) = true ->
  WellScoped e vs1 -> WellScoped e (extendVarSetList vs1 vs).

Axiom WellScoped_subset:
  forall e vs,
  WellScoped e vs -> subVarSet (exprFreeVars e) vs = true.

Axiom WellScoped_mkLams:
  forall vs e isvs,
  WellScoped (mkLams vs e) isvs <-> WellScoped e (extendVarSetList  isvs vs).

Axiom WellScoped_mkVarApps:
  forall e vs isvs,
  WellScoped (mkVarApps e vs) isvs <-> WellScoped e isvs /\ Forall (fun v => WellScopedVar v isvs) vs.

Axiom exprFreeVars_mkLams:
  forall vs e,
  exprFreeVars (mkLams vs e) = delVarSetList (exprFreeVars e) vs.

Lemma WellScoped_extendVarSetList_fresh_under:
  forall vs1 vs2 e vs,
  disjointVarSet (exprFreeVars e) (mkVarSet vs1)  = true ->
  WellScoped e (extendVarSetList (extendVarSetList vs vs1) vs2) <-> WellScoped e (extendVarSetList vs vs2).
Proof.
  intros.
  rewrite <- WellScoped_mkLams.
  rewrite WellScoped_extendVarSetList_fresh.
  rewrite -> WellScoped_mkLams.
  reflexivity.
  rewrite exprFreeVars_mkLams.
  eapply disjointVarSet_subVarSet_l; only 1: eassumption.
  apply subVarSet_delVarSetList.
Qed.

Lemma WellScoped_MkLetRec: forall pairs body isvs,
  WellScoped (mkLetRec pairs body) isvs <-> WellScoped (Let (Rec pairs) body) isvs .
Proof.
  intros.
  unfold mkLetRec.
  destruct pairs; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

Axiom WellScoped_extended_filtered:
  forall vs e isvs,
  WellScoped e (extendVarSetList isvs vs) ->
  WellScoped e (extendVarSetList isvs (filter (fun v => elemVarSet v (exprFreeVars e)) vs)).

Axiom isJoinPointValidPair_extendVarSet:
  forall v rhs jps v',
  isJoinPointsValidPair v rhs jps = true ->
  isJoinPointsValidPair v rhs (extendVarSet jps v') = true.
  
Axiom WellScoped_collectNBinders:
  forall e n isvs body params,
  WellScoped e isvs ->
  collectNBinders n e = (params, body) ->
  WellScoped body (extendVarSetList isvs params).

Axiom WellScoped_collectNBinders2:
  forall e n isvs,
  WellScoped e isvs ->
  WellScoped (snd (collectNBinders n e)) (extendVarSetList isvs (fst (collectNBinders n e))).

(* Just [simpl] is too ugly; uses [flat_map] *)
Axiom deAnnBinds_AnnRec:
 forall {a v} (pairs : list (v * AnnExpr v a)),
 deAnnBind (AnnRec pairs) = Rec (map (fun p => (fst p, deAnnotate (snd p))) pairs).

Axiom deAnnotate_AnnLet_AnnRec:
 forall {a v} fvs pairs (e : AnnExpr a v),
 deAnnotate (fvs, AnnLet (AnnRec pairs) e)
  = Let (Rec (map (fun p => (fst p, deAnnotate (snd p))) pairs)) (deAnnotate e).

Axiom bindersOf_Rec:
  forall {v} (pairs : list (v * Expr v)),
  bindersOf (Rec pairs) = map fst pairs.

Axiom forallb_imp:
  forall a P Q (xs : list a),
  forallb P xs = true ->
  (forall x, P x = true -> Q x = true) ->
  forallb Q xs = true.

Axiom WellScopedVar_extendVarSetList_l:
  forall v vs1 vs2,
  WellScopedVar v vs1 ->
  elemVarSet v (mkVarSet vs2) = false ->
  WellScopedVar v (extendVarSetList vs1 vs2).

Axiom WellScopedVar_extendVarSetList_r:
  forall v vs1 vs2,
  In v vs2 ->
  NoDup (map varUnique vs2) ->
  WellScopedVar v (extendVarSetList vs1 vs2).

Lemma snd_unzip:
  forall a b (xs : list (a * b)),
  snd (List.unzip xs) = map snd xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl. f_equal. apply IHxs.
Qed.

Lemma snd_unzip_map:
  forall a b c (f : a -> b) (g : a -> c) xs,
  snd (List.unzip (map (fun x => (f x, g x)) xs)) = map g xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl. f_equal. apply IHxs.
Qed.


Lemma zip_unzip_map:
  forall a b c (f : b -> c) (xs : list (a * b)),
  List.zip (fst (List.unzip xs)) (Base.map f (snd (List.unzip xs)))
  = map (fun '(x,y) => (x, f y)) xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl. f_equal. apply IHxs.
Qed.

Lemma flat_map_unpack_cons_f:
  forall (A B C : Type) (f : A -> B -> C ) (xs : list (A * B)),
   flat_map (fun '(x,y) => [f x y]) xs = map (fun '(x,y) => f x y) xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl.
    f_equal. apply IHxs.
Qed.

Lemma forM_map:
  forall (m : Type -> Type) (a b c : Type) `{Monad m}
  (xs : list a) (act : b -> m c) (f : a -> b),
  Traversable.forM (map f xs) act = Traversable.forM xs (fun x => act (f x)).
Proof.
  intros.
  induction xs.
  * reflexivity.
  * cbv. f_equal. apply IHxs.
Qed.

Lemma forM_cong:
  forall {a m b} `{Monad m} (f g : a -> m b) (xs : list a),
  (forall x, In x xs -> f x = g x) ->
  Traversable.forM xs f = Traversable.forM xs g.
Proof.
  intros.
  rewrite <- forM_map with (act := fun x => x) (f := f).
  rewrite <- forM_map with (act := fun x => x) (f := g).
  f_equal.
  apply map_ext_in.
  assumption.
Qed.

(* This section reflects the context of the local definition of exitify *)
Section in_exitify.
  (* Parameters of exitify *)
  Variable in_scope : InScopeSet.
  Variable pairs : list NJPair.
  (* The actual parameter passed *)
  Definition in_scope2 := extendInScopeSetList in_scope (map (fun '(Mk_NJPair v _ _ _) => v) pairs).

  (* Parameters and assumptions of the proof *)
  Variable jps : VarSet.

  (* Giving names to the local functions of exitify.
     See http://www.joachim-breitner.de/blog/738-Verifying_local_definitions_in_Coq
     for more on that idiom.
   *)
  Definition recursive_calls := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x := ?rhs in ?body) => 
      exact rhs
    end).

  Definition go := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x := _ in let y := @?rhs x in _) => 
      let def := eval cbv beta in (rhs recursive_calls) in
      exact def
    end).

  Definition go_f := ltac:(
    let rhs := eval cbv delta [go] in go in
    lazymatch rhs with
      | @DeferredFix.deferredFix2 ?a ?b ?r ?HDefault ?f =>
      exact f
    end).

  (* Termination of [go] *)
  Lemma go_eq :
     forall captured e,
     go captured (freeVars (toExpr e)) = go_f go captured (freeVars (toExpr e)).
  Proof.
    intros.
    unfold go; fold go_f.
    unfold DeferredFix.deferredFix2.
    unfold DeferredFix.curry.
    rewrite DeferredFix.deferredFix_eq_on with
      (P := fun p => exists u, snd p = freeVars (toExpr u))
      (R := fun p1 p2 => AnnCoreLT (snd p1) (snd p2)).
    * reflexivity.
    * apply Inverse_Image.wf_inverse_image.
      apply AnnCoreLT_wf.
    * clear captured e.
      intros g h [captured ann_e] HP Hgh.
      destruct HP as [e Heq]. simpl in Heq. subst ann_e.

      simpl. cbv beta delta [go_f].
      repeat float_let; cse_let.

      enough (Hnext : j_37__ = j_37__0). {
        repeat (destruct_match; try reflexivity); try apply Hnext.
      }
      subst j_37__ j_37__0. cleardefs.

      enough (Hnext : j_36__ = j_36__0). {
        repeat (destruct_match; try reflexivity); try apply Hnext.
      }
      subst j_36__ j_36__0. cleardefs.

      enough (Hnext : j_35__ = j_35__0). {
        repeat (destruct_match; try reflexivity); try apply Hnext.
      }
      subst j_35__ j_35__0. cleardefs.

      enough (Hnext : j_22__ = j_22__0). {
        repeat (destruct_match; try reflexivity); try apply Hnext.
      }
      subst j_22__ j_22__0. cleardefs.

      subst j_4__.
      destruct e;
        simpl; rewrite ?freeVarsBind1_freeVarsBind;
        try destruct n;
        simpl;
        try destruct (isLocalVar _);
        repeat expand_pairs;
        simpl;
        repeat destruct_match;
        simpl; rewrite ?freeVarsBind1_freeVarsBind;
        rewrite ?collectNAnnBndrs_freeVars_mkLams in *;
        try (simpl in Heq);
        try (inversion Heq; subst; clear Heq);
        try solve [congruence];
        try reflexivity.
      - f_equal.
        apply Hgh; simpl.
        + eexists; reflexivity.
        + simpl; rewrite ?freeVarsBind1_freeVarsBind.
          simpl.
          AnnCore_termination.
      - f_equal.
        ** replace j with (length params) in Heq2 by congruence.
           rewrite collectNAnnBndrs_freeVars_mkLams in Heq2.
           inversion Heq2; subst; clear Heq2.
           apply Hgh; simpl.
           + eexists; reflexivity.
           + simpl; rewrite ?freeVarsBind1_freeVarsBind.
             simpl.
             admit.
        ** extensionality join_body'.
           f_equal.
           apply Hgh.
           + eexists; reflexivity.
           + simpl. expand_pairs.
             AnnCore_termination.
      - contradict H0.
        apply not_true_iff_false.
        rewrite zip_unzip_map.
        rewrite to_list_map.
        dependent inversion pairs0; subst.
        destruct h0.
        rewrite to_list_cons.
        simpl.
        rewrite isJoinId_eq. rewrite HnotJoin. reflexivity.
      - clear H0. f_equal.
        apply Hgh; simpl.
        + eexists; reflexivity.
        + simpl; rewrite ?freeVarsBind1_freeVarsBind.
          simpl. repeat expand_pairs. simpl.
          AnnCore_termination.
      - clear H0.
        rewrite zip_unzip_map.
        rewrite to_list_map.
        rewrite !forM_map.
        f_equal.
        ** apply forM_cong. intros [j params rhs HiNJ] HIn.
           simpl.
           expand_pairs.
           erewrite idJoinArity_join by eassumption.
           rewrite collectNAnnBndrs_freeVars_mkLams.
           f_equal.
           apply Hgh.
           + eexists; reflexivity.
           + simpl.
             rewrite ?freeVarsBind1_freeVarsBind. simpl.
             repeat expand_pairs. simpl.
             rewrite !zip_unzip_map. rewrite !to_list_map.
             rewrite map_map.
             admit.
        ** extensionality pairs'.
           f_equal.
           apply Hgh.
           + eexists; reflexivity.
           + simpl.
             rewrite ?freeVarsBind1_freeVarsBind. simpl.
             repeat expand_pairs. simpl.
             AnnCore_termination.
      - contradict H0.
        apply not_false_iff_true.
        rewrite zip_unzip_map.
        rewrite to_list_map.
        dependent inversion pairs0; subst.
        destruct h0.
        rewrite to_list_cons.
        simpl.
        rewrite isJoinId_eq. rewrite HisJoin. reflexivity.
      - f_equal.
        rewrite snd_unzip. rewrite !map_map, !forM_map.
        apply forM_cong. intros [[dc pats] rhs] HIn.
        simpl.
        f_equal. apply Hgh; clear Hgh.
        + eexists; reflexivity.
        + simpl. expand_pairs. simpl.
          rewrite snd_unzip, !map_map.
          admit.
  * eexists; reflexivity.
  Admitted.

  Definition ann_pairs := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let y := ?rhs in _) => 
      exact rhs
    end).

  Definition pairs'_exits := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let '(pairs',exits) := @?rhs x2 x3 in ?body) => 
      let def := eval cbv beta in (rhs go ann_pairs) in
      exact def
    end).
  Definition pairs' := fst pairs'_exits.
  Definition exits := snd pairs'_exits.
  
  Definition mkExitLets := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let '(pairs',exits) := _ in let y := ?rhs in ?body) => 
      exact rhs
    end).

  (** ** Scope validity *)
  Definition isvs := getInScopeVars in_scope.

  (** This predicate describes when a list of non-recursive bindings
      is ok to wrap around the [Let (Rec [pairs] body)] pair.

      (This could move to [ScopeInvariants])
  *)
  Definition WellScopedFloats floats :=
    (* All added bindings are fresh with regard to the environment *)
    Forall (fun 'p => elemVarSet (fst p) isvs = false) floats /\
    (* All added bindings are fresh with regard to each other  *)
    NoDup (map (fun p => varUnique (fst p)) floats) /\
    (* All added bindings are well-scoped in the original environment  *)
    Forall (fun 'p => WellScoped (snd p) isvs) floats.

  (* Here we do the actual wrapping *)
  Lemma mkExitLets_WellScoped:
    forall exits' e,
    (* The body is well-scoped in the extended environment *)
    WellScoped e (extendVarSetList isvs (map fst exits')) ->
    WellScopedFloats exits' ->
    (* Then wrapping these bindings around [e] is well-scoped *)
    WellScoped (mkExitLets exits' e) isvs.
  Proof.
    intros ?.
    unfold WellScopedFloats.
    generalize isvs as isvs.
    clear in_scope pairs jps.
    induction exits' as [|[v rhs] exits']; intros isvs' e Hbase Hfloats.
    * simpl. unfold Base.id. assumption.
    * simpl in *.
      destruct Hfloats as [Hfreshs [HNoDup Hrhss]].
      inversion HNoDup; subst; clear HNoDup. rename H1 into Hfresh, H2 into HNoDup.
      inversion_clear Hrhss. rename H into Hrhs, H0 into Hrhss.
      inversion_clear Hfreshs. rename H into Hfresh_v, H0 into Hfreshs.
      simpl in *.
      rewrite extendVarSetList_cons in Hbase.
      split; only 1: apply Hrhs.
      apply IHexits'.
      - assumption.
      - repeat split.
        + rewrite Forall_forall.
          rewrite Forall_forall in Hfreshs.
          rewrite in_map_iff in Hfresh.
          intros [v' rhs'] HIn.
          rewrite elemVarSet_extendVarSet.
          simpl_bool.
          split.
          ** simpl.
             destruct (Eq_eq (varUnique v') (varUnique v)); (reflexivity || exfalso).
             contradict Hfresh.
             exists (v', rhs'). split; assumption.
          ** apply Hfreshs. assumption.
        + assumption.
        + rewrite Forall_forall.
          rewrite Forall_forall in Hrhss.
          intros pair HIn. simpl.
          rewrite WellScoped_extendVarSet_fresh.
          apply Hrhss; assumption.
          eapply subVarSet_elemVarSet_false; only 2: eassumption.
          apply WellScoped_subset.
          apply Hrhss; assumption.
  Qed.

  (* the [addExit] function ensures that the new exit floats are well-scoped
     where we are going to put them.
   *)
  Lemma addExit_all_WellScopedFloats:
    forall captured ty ja e,
    WellScoped e isvs ->
    StateInvariant WellScopedFloats
                   (addExit (extendInScopeSetList in_scope2 captured) ty ja e).
  Proof.
    intros.
    (* This is much easier to prove by breaking the State abstraction and turning
       it into a simple function. *)
    unfold addExit, mkExitJoinId.
    unfold StateInvariant, SP,
           op_zgzgze__, return_, State.Monad__State, op_zgzgze____, return___,
           State.Monad__State_op_zgzgze__,
           State.Monad__State_return_,
           pure, State.Applicative__State , pure__,
           State.Applicative__State_pure,
           State.runState', State.get, State.put.
    simpl.
    intros floats Hfloats.
    set (v := uniqAway _ _).
    constructor; only 2: trivial.
    constructor; only 2: constructor; simpl.
    * constructor; only 2: apply Hfloats; simpl.
      unfold isvs, in_scope2 in *.
      apply elemVarSet_uniqAway.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      repeat apply subVarSet_extendVarSetList_l.
      apply subVarSet_refl.
    * constructor; only 2: apply Hfloats; simpl.
      rewrite <- map_map.
      rewrite <- elemVarSet_mkVarset_iff_In.
      rewrite not_true_iff_false.
      apply elemVarSet_uniqAway.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      apply subVarSet_extendVarSetList_r.
      apply subVarSet_refl.
    * constructor; only 2: apply Hfloats; simpl.
      assumption.
  Qed.

  (* [addExit] is called somewhere in [go], so we need to follow [go]'s traversal
     of the AST and collect all calls to [addExit].
   *)
  Program Fixpoint go_all_WellScopedFloats 
      captured e { measure e (NCoreLT)} : 
    WellScoped (toExpr e) (extendVarSetList (getInScopeVars in_scope2) captured) ->
    StateInvariant WellScopedFloats (go captured (freeVars (toExpr e))) := _.
  Next Obligation.
    rename go_all_WellScopedFloats into IH.
    rename H into  HWS.
    set (P := WellScopedFloats).
    rewrite go_eq.
    cbv beta delta [go_f]. (* No [zeta]! *)

    rewrite !dVarSet_freeVarsOf_Ann in *.
    rewrite !deAnnotate_freeVars in *.
    
    (* Float out lets *)
    repeat float_let.

    (* First case *)
    enough (Hnext: StateInvariant P j_37__). {
      clearbody j_37__; cleardefs.
      destruct (collectArgs _) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Second case *)
    subst j_37__.
    enough (Hnext: StateInvariant P j_36__). {
      destruct (is_exit && negb is_interesting) ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Third case *)
    subst j_36__.
    enough (Hnext: StateInvariant P j_35__). {
      destruct (is_exit && captures_join_points ) ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Third case: Actual exitification *)
    subst j_35__.
    enough (Hnext: StateInvariant P j_22__). {
      clearbody j_22__. 
      destruct is_exit eqn:? ; try apply Hnext.
      subst is_exit. unfold recursive_calls in Heqb.
      apply StateInvariant_bind_return.
      apply addExit_all_WellScopedFloats.
      rewrite WellScoped_mkLams.
      subst args fvs.
      rewrite hs_coq_filter.
      apply WellScoped_extended_filtered.
      unfold in_scope2 in HWS.
      rewrite getInScopeVars_extendInScopeSetList in HWS.
      fold isvs in HWS.
      rewrite map_map in Heqb.
      rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in Heqb
        by (intros; repeat expand_pairs; destruct a; reflexivity).
      eapply WellScoped_extendVarSetList_fresh_under; eassumption.
    }
    cleardefs.

    (* Fourth case: No exitification here, so descend*)
    subst j_22__.
    enough (Hnext: StateInvariant P j_4__). {
      clearbody j_4__.
      destruct e; try apply Hnext.
      * (* spurious case Mk_Var *)
        simpl in *. destruct (isLocalVar _); apply Hnext.
      * (* spurious case Lam *)
        simpl in *. repeat expand_pairs. apply Hnext.
      * (* Case [Let] *) 
        repeat float_let.
        simpl.
        do 2 expand_pairs. simpl.
        rewrite freeVarsBind1_freeVarsBind.
        unfold freeVarsBind.
        destruct n as [[x rhs] | [j params rhs] | n pairs' | n pairs']; simpl.
        + rewrite HnotJoin.
          simpl in *.
          apply StateInvariant_bind_return.
          apply IH.
          ** NCore_termination.
          ** simpl. 
             rewrite  extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
             apply HWS.
        + unfold CoreBndr in *.
          rewrite HisJoin.
          rewrite collectNAnnBndrs_freeVars_mkLams.
          apply StateInvariant_bind.
          ++ apply IH.
             ** NCore_termination.
             ** rewrite extendVarSetList_append.
                simpl in HWS.
                rewrite WellScoped_mkLams in HWS.
                apply HWS.
          ++ intros. apply StateInvariant_bind_return.
             apply IH.
             ** NCore_termination.
             ** rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
                apply HWS.
        + expand_pairs. simpl.
          rewrite to_list_map.
          rewrite !zip_unzip_map.
          rewrite !map_map.

          destruct (isJoinId _) eqn:Heq_isJoinId.
          Focus 1.
            exfalso.
            rewrite <- not_false_iff_true in Heq_isJoinId.
            contradict Heq_isJoinId.
            dependent inversion pairs'; subst; clear.
            dependent inversion h. simpl.
            rewrite isJoinId_eq. rewrite HnotJoin. reflexivity.
          clear Heq_isJoinId.

          apply StateInvariant_bind_return.
          apply IH.
          ** NCore_termination.
          ** rewrite !extendVarSetList_append.
             do 2 rewrite flat_map_unpack_cons_f.
             do 2 rewrite map_map.
             rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x)
                by (intros; repeat expand_pairs; destruct a; reflexivity).
             simpl in HWS.
             rewrite to_list_map in HWS.
             rewrite !map_map in HWS.
             rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x) in HWS
                by (intros; repeat expand_pairs; destruct a; reflexivity).
             apply HWS.
        + expand_pairs. simpl.
          rewrite to_list_map.
          rewrite !zip_unzip_map.
          rewrite !map_map.
          destruct (isJoinId _) eqn:Heq_isJoinId.
          Focus 2.
            exfalso.
            rewrite <- not_true_iff_false in Heq_isJoinId.
            contradict Heq_isJoinId.
            dependent inversion pairs'; subst; clear.
            dependent inversion h. simpl.
            rewrite isJoinId_eq. rewrite HisJoin. reflexivity.
          clear Heq_isJoinId.

          rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x)
             by (intros; repeat expand_pairs; destruct a; reflexivity).

          rewrite forM_map.
          apply StateInvariant_bind.
          - apply StateInvariant_forM.
            intros [j params rhs] HIn.
            simpl.
            erewrite idJoinArity_join by eassumption.
            rewrite collectNAnnBndrs_freeVars_mkLams.

            apply StateInvariant_bind_return.
            apply IH.
            ** NCore_termination.
            ** rewrite !extendVarSetList_append.
               destruct HWS as [_ [HWS _]].
               rewrite Forall'_Forall in HWS.
               rewrite to_list_map in HWS.
               rewrite Forall_map in HWS.
               rewrite Forall_forall in HWS.
               simpl in HWS.
               rewrite !map_map in HWS.
               rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in HWS
                 by (intros; repeat expand_pairs; destruct a; reflexivity).
               apply WellScoped_mkLams.
               eapply (HWS _ HIn).
          - intro x.
            apply StateInvariant_bind_return.
            apply IH.
            ** NCore_termination.
            ** rewrite !extendVarSetList_append.
               destruct HWS as [_ [_ HWS]].
               rewrite to_list_map in HWS.
               rewrite map_map in HWS.
               rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in HWS
                 by (intros; repeat expand_pairs; destruct a; reflexivity).
               apply HWS.

      * (* Case [Case] *)
        simpl in *.

        do 2 expand_pairs. simpl.
        rewrite snd_unzip, !map_map.
        rewrite forM_map.
        apply StateInvariant_bind_return.
        apply StateInvariant_forM.
        intros [[dc pats] rhs] HIn.
        apply StateInvariant_bind_return.
        apply IH.
        ** NCore_termination.
        ** (* This needs automation! *)
           destruct HWS as [_ HWSpairs].
           rewrite extendVarSetList_append.
           rewrite Forall'_Forall in HWSpairs.
           rewrite Forall_map in HWSpairs.
           rewrite Forall_forall in HWSpairs.
           apply (HWSpairs (dc, pats, rhs)).
           assumption.
    }

    subst j_4__.
    apply StateInvariant_return.
  Admitted.

  (* Clearly we expect the input pairs be well-scoped *)
  Variable pairs_WS :
    Forall (fun p => WellScoped (snd p) (extendVarSetList (getInScopeVars in_scope) (map (fun '(Mk_NJPair v _ _ _) => v) pairs)))
           (map toJPair pairs) .

  Lemma all_exists_WellScoped:
    WellScopedFloats exits.
  Proof.
    unfold exits.
    unfold pairs'_exits.
    unfold ann_pairs.
    rewrite hs_coq_map.
    do 2 rewrite forM_map.
    eapply SP_snd_runState.
    * apply StateInvariant_forM.
      intros [v params rhs HisJoin] HIn.
      do 2 expand_pairs. simpl.
      erewrite idJoinArity_join by eassumption.
      rewrite collectNAnnBndrs_freeVars_mkLams.
      apply StateInvariant_bind_return.
      apply go_all_WellScopedFloats.
      + rewrite <- WellScoped_mkLams.
        rewrite Forall_map in pairs_WS.
        rewrite Forall_forall in pairs_WS.
        unfold in_scope2.
        rewrite getInScopeVars_extendInScopeSetList.
        apply (pairs_WS _ HIn).
    * repeat split; constructor.
  Qed.

  Definition sublistOf {a} (xs ys : list a) := incl ys xs.

  Lemma sublistOf_cons {a} x (xs ys : list a):
    sublistOf ys (x :: xs) <-> (In x ys /\ sublistOf ys xs).
  Proof.
    intros.
    unfold sublistOf, incl.
    intuition.
    destruct H; subst; auto.
  Qed.
  
  Lemma extend_scope_with_exits:
     forall e, WellScoped e isvs -> WellScoped e (extendVarSetList isvs (map fst exits)).
  Proof.
    intros.
    apply WellScoped_extendVarSetList.
    rewrite disjointVarSet_mkVarSet.
    rewrite Forall_map. simpl.
    apply all_exists_WellScoped.
    assumption.
  Qed.
  
  Lemma addExit_all_WellScopedVar:
    forall captured ty ja e,
    let after := extendVarSetList (extendVarSetList (extendVarSetList isvs (map fst exits)) (map (fun '(Mk_NJPair v _ _ _) => v) pairs)) captured in
    RevStateInvariant (sublistOf exits) 
         (addExit (extendInScopeSetList in_scope2 captured) ty ja e)
         (fun v => WellScopedVar v after).
  Proof.
    intros.
    (* This is much easier to prove by breaking the State abstraction and turning
       it into a simple function. *)
    unfold addExit, mkExitJoinId.
    unfold RevStateInvariant, SP,
           op_zgzgze__, return_, State.Monad__State, op_zgzgze____, return___,
           State.Monad__State_op_zgzgze__,
           State.Monad__State_return_,
           pure, State.Applicative__State , pure__,
           State.Applicative__State_pure,
           State.runState', State.get, State.put.
    simpl.
    intros floats Hfloats.
    set (v := uniqAway _ _) in *.
    apply sublistOf_cons in Hfloats.
    destruct Hfloats as [HIn HsublistOf].
    apply in_map with (f := fst) in HIn. simpl in HIn.
    split; only 1: assumption.
    subst after.
    apply WellScopedVar_extendVarSetList_l; only 1: apply WellScopedVar_extendVarSetList_l.
    * apply WellScopedVar_extendVarSetList_r; only 1: assumption.
      rewrite map_map.
      apply all_exists_WellScoped.
    * apply elemVarSet_uniqAway.
      unfold in_scope2.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      apply subVarSet_extendVarSetList_l.
      apply subVarSet_extendVarSetList_l.
      apply subVarSet_extendVarSetList_r.
      apply subVarSet_refl.
    * apply elemVarSet_uniqAway.
      unfold in_scope2.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      apply subVarSet_extendVarSetList_l.
      apply subVarSet_extendVarSetList_r.
      apply subVarSet_refl.
  Qed.

  (* No we go throught [go] again and see that pairs' is well-scoped.
     We start assuming that the result of the computation is a subset of exits'
     for which we already know [WellScopedFloats]. By going backwards,
     we will recover that [mkExit] produces a name of this set.
  *)
  Lemma go_res_WellScoped:
    forall captured ann_e,
    let orig := extendVarSetList (extendVarSetList isvs (map (fun '(Mk_NJPair v _ _ _) => v) pairs)) captured in
    let after := extendVarSetList (extendVarSetList (extendVarSetList isvs (map fst exits)) (map (fun '(Mk_NJPair v _ _ _) => v) pairs)) captured in
    WellScoped (deAnnotate ann_e) orig ->
    RevStateInvariant (sublistOf exits) (go captured ann_e) (fun e' => WellScoped e' after) .
  Proof.
    (* This cannot be structural recursion. Will need a size on expressions. *)
    fix 2. rename go_res_WellScoped into IH.
    intros ??? ? HWS.
    set (P := fun x => RevStateInvariant (sublistOf exits) x (fun e' => WellScoped e' after)).
    change (P (go captured ann_e)).
    replace go with (go_f go) by admit. (* Need to use [go_eq] here *)
    cbv beta delta [go_f]. (* No [zeta]! *)
    (* Float out lets *)
    repeat float_let.
    
    (* Common case *)
    assert (Hreturn : P (return_ e)). {
       apply RevStateInvariant_return. cleardefs.
       subst after.
       do 2 rewrite <- WellScoped_mkLams.
       apply extend_scope_with_exits.
       do 2 rewrite -> WellScoped_mkLams.
       assumption.
    } 

    (* First case *)
    enough (Hnext: P j_37__). {
      clearbody j_37__; cleardefs.
      destruct (collectArgs e) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply Hreturn.
    }
    cleardefs.

    (* Second case *)
    subst j_37__.
    enough (Hnext: P j_36__). {
      destruct (is_exit && negb is_interesting) ; try apply Hnext.
      apply Hreturn.
    }
    cleardefs.

    (* Third case *)
    subst j_36__.
    enough (Hnext: P j_35__). {
      destruct (is_exit && captures_join_points ) ; try apply Hnext.
      apply Hreturn.
    }
    cleardefs.

    (* Third case: Actual exitification *)
    subst j_35__.
    enough (Hnext: P j_22__). {
      clearbody j_22__. 
      destruct is_exit eqn:? ; try apply Hnext.
      clear Hnext j_22__. subst P. cleardefs. 
      subst is_exit. unfold recursive_calls in Heqb.
      eapply RevStateInvariant_bind; only 1: apply addExit_all_WellScopedVar.
      intro v.
      apply RevStateInvariant_return.
      intro HWSv.
      rewrite WellScoped_mkVarApps.
      split; only 1 : apply HWSv.
      subst args.
      admit. (* somewhere here is the bug. not all variables in [captured] are in scope here. *)
    }
    cleardefs.

    (* Fourth case: No exitification here, so descend*)
    subst j_22__.
    enough (Hnext: P j_4__). {
      clearbody j_4__. clear Hreturn. cleardefs.
      destruct ann_e as [fvs e] eqn:Hann.
      destruct e; try apply Hnext;
        clear Hnext j_4__; cleardefs.
      * (* Case [Case] *)
        destruct HWS as [Hscrut HWSalts].
        rewrite Forall'_Forall in HWSalts.
        rewrite Forall_map in HWSalts.
        rewrite Forall_forall in HWSalts.


        eapply RevStateInvariant_bind.
        + apply RevStateInvariant_forM with (R := fun alt => WellScopedAlt c alt after).
          intros [[dc pats] rhs] HIn.
          eapply RevStateInvariant_bind.
          - apply IH.
            (* This needs automation! *)
            rewrite extendVarSetList_append.
            specialize (HWSalts (dc, pats, rhs)). simpl in HWSalts.
            apply HWSalts.
            assumption.
          - intro e; apply RevStateInvariant_return; intro He.
            rewrite extendVarSetList_append in He.
            apply He.
        + intros alts'; apply RevStateInvariant_return; intro He.
          simpl. split.
          - subst after.
            do 2 rewrite <- WellScoped_mkLams.
            apply extend_scope_with_exits.
            do 2 rewrite -> WellScoped_mkLams.
            assumption.
          - rewrite Forall'_Forall.
            apply He.

      * (* Case [Let] *) 
        repeat float_let.

        enough (Hnext': P j_18__). {
          clearbody j_18__.
          destruct a as [j rhs|pairs']; try apply Hnext'.
          destruct (isJoinId_maybe j) as [join_arity|] eqn:HiJI; try apply Hnext'.
          unfold CoreBndr in *.
          destruct (collectNAnnBndrs join_arity rhs) as [params join_body] eqn:HcAB.
          eapply RevStateInvariant_bind.
          + apply IH.
            ** rewrite extendVarSetList_append.
               simpl in HWS.
               eapply WellScoped_collectNBinders; only 1: apply HWS.
               Fail apply collectAnnNBndrs_collectNBinders.
               admit.
          + intros body'. eapply RevStateInvariant_bind.
            - apply IH.
              ** rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
                 apply HWS.
            - intro e'; apply RevStateInvariant_return; intros He' Hbody'.
              split.
              ++ rewrite WellScoped_mkLams.
                 rewrite extendVarSetList_append in Hbody'.
                 apply Hbody'.
              ++ rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil in He'.
                 apply He'.
        }

        subst j_18__.
        enough (Hnext': P j_10__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          destruct (isJoinId _); try apply Hnext'.
          + intros.

            rewrite deAnnotate_AnnLet_AnnRec in HWS.
            destruct HWS as [HNoDup [HWS HWSbody]].
            rewrite Forall'_Forall in HWS.
            rewrite !map_map in HWS.
            rewrite !map_map in HNoDup.
            rewrite !map_map in HWSbody.

            eapply RevStateInvariant_bind.
            - apply RevStateInvariant_forM2 with
                (R := fun p p' =>
                    fst p = fst p' /\
                    WellScoped (snd p') (extendVarSetList after (map fst pairs'))).
              intros [j rhs] HIn.
              repeat float_let.
              destruct (collectNAnnBndrs join_arity rhs) as [params join_body] eqn:HcAB.
              eapply RevStateInvariant_bind.
              ++ apply IH.
                 ** rewrite !extendVarSetList_append.
                    rewrite Forall_map in HWS.
                    rewrite Forall_forall in HWS.
                    eapply WellScoped_collectNBinders; only 1: apply HWS.
                    eassumption.
                    Fail apply collectAnnNBndrs_collectNBinders; eassumption.
                    admit.
              ++ intro e'; apply RevStateInvariant_return; intro He'.
                 simpl.
                 rewrite WellScoped_mkLams.
                 rewrite !extendVarSetList_append in He'.
                 split; only 1: reflexivity.
                 apply He'. 
            - intro pairs''.
              eapply RevStateInvariant_bind.
              ++ apply IH.
                 ** rewrite !extendVarSetList_append.
                    apply HWSbody.
              ++ intro e'; apply RevStateInvariant_return; intros He' Hpairs''.
                 apply Forall2_and in Hpairs''.
                 destruct Hpairs'' as [Hfst Hpairs''].
                 apply Forall2_const_Forall in Hpairs''.
                 eapply Forall2_eq with (f := fst) (g := fst) in Hfst.
                 symmetry in Hfst.
                 change ((@map (CoreBndr * Expr CoreBndr) CoreBndr (@fst CoreBndr (Expr CoreBndr)) pairs'') = map fst pairs') in Hfst.
                 simpl.
                 rewrite Hfst.
                 split; only 2: split.
                 -- simpl in HNoDup.
                    rewrite map_map.
                    apply HNoDup.
                 -- rewrite Forall'_Forall.
                    apply Hpairs''.
                 -- rewrite !extendVarSetList_append in He'.
                    apply He'.
        }

        subst j_10__.
        eapply RevStateInvariant_bind.
        - apply IH.
          ** rewrite !extendVarSetList_append.
             subst bind.
             destruct a as [v rhs|apairs].
             ++ simpl in *.
                rewrite extendVarSetList_cons, extendVarSetList_nil.
                apply HWS.
             ++ rewrite deAnnotate_AnnLet_AnnRec in HWS.
                rewrite deAnnBinds_AnnRec.
                rewrite bindersOf_Rec.
                destruct HWS as [_ [_ HWS]].
                rewrite map_map in HWS. simpl in HWS.
                rewrite map_map; simpl.
                apply HWS.
        - intro e'; apply RevStateInvariant_return; intros He'.
          simpl.
          subst bind.
          destruct a as [v rhs|apairs].
          ++ simpl in *.
             rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil in He'.
             split.
             + subst after.
               do 2 rewrite <- WellScoped_mkLams.
               apply extend_scope_with_exits.
               do 2 rewrite -> WellScoped_mkLams.
               apply HWS.
             + apply He'.
          ++ rewrite deAnnotate_AnnLet_AnnRec in HWS. simpl in HWS.
             rewrite deAnnBinds_AnnRec.
             destruct HWS as [HNoDups [HWS _]].
             rewrite !map_map in HNoDups. simpl in HNoDups.
             split; only 2: split.
             + rewrite !map_map. simpl. apply HNoDups .
             + rewrite Forall'_Forall in *.
               eapply Forall_impl; only 2: apply HWS.
               intros [v rhs] HWSv. simpl in *.
               fold orig in HWSv.
               subst after.
               do 3 rewrite <- WellScoped_mkLams.
               apply extend_scope_with_exits.
               do 3 rewrite -> WellScoped_mkLams.
               apply HWSv.
             + rewrite extendVarSetList_append in He'.
               fold after in He'.
               rewrite deAnnBinds_AnnRec in He'.
               rewrite bindersOf_Rec in He'.
               apply He'.
    }

    subst j_4__.
    apply Hreturn.

  (* TODO: Not structurally recursive *)
  Fail Guarded.
  Admitted.

  Lemma pairs'_WS:
    Forall (fun p => WellScoped (snd p) (extendVarSetList (extendVarSetList isvs (map fst exits)) (map (fun '(Mk_NJPair v _ _ _) => v) pairs))) pairs'.
  Proof.
    unfold pairs', pairs'_exits, ann_pairs.
    eapply RevStateInvariant_runState with (P := sublistOf exits).
    * apply RevStateInvariant_forM.
      intros [v rhs] HIn.
      destruct (collectNAnnBndrs (idJoinArity v) rhs) as [params join_body] eqn:HcAB.
      apply RevStateInvariant_bind_return. simpl.
      eapply RevStateInvariant_impl.
      + apply go_res_WellScoped.
        - admit.
          (*
          eapply WellScoped_collectNBinders;
            only 2: (apply collectAnnNBndrs_collectNBinders; eassumption).
          rewrite Forall_forall in pairs_WS.
          specialize (pairs_WS (v, deAnnotate rhs)).
          apply pairs_WS.
          unfold ann_pairs in HIn.
          rewrite in_map_iff in HIn.
          destruct HIn as [[v' rhs'] [Heq HIn]].
          inversion Heq. unfold id in H0. subst.
          rewrite deAnnotate_freeVars.
          assumption.
          *)
      + intros. simpl in *.
        rewrite WellScoped_mkLams.
        assumption.
    * change (sublistOf exits exits).
      intro. auto.
  Admitted.

  Lemma map_fst_pairs':
    map fst pairs' = (map (fun '(Mk_NJPair v _ _ _) => v) pairs).
  Proof.
    intros.
    unfold pairs', pairs'_exits, ann_pairs.
    unfold Traversable.forM, flip.
    unfold Traversable.mapM, Traversable.Traversable__list, Traversable.mapM__, Traversable.Traversable__list_mapM.
    unfold Traversable.Traversable__list_traverse.
    unfold liftA2, State.Applicative__State, liftA2__, State.Applicative__State_liftA2.
    unfold State.Applicative__State_op_zlztzg__.
    unfold State.runState.
    expand_pairs; simpl.
    unfold pure, pure__, State.Applicative__State_pure.
    unfold op_zgzgze__, State.Monad__State, op_zgzgze____,State.Monad__State_op_zgzgze__.
    unfold Bifunctor.second, Bifunctor.Bifunctor__pair_type, Bifunctor.second__,
           Bifunctor.Bifunctor__pair_type_second, Bifunctor.Bifunctor__pair_type_bimap.
    unfold id.
    generalize (@nil (CoreBndr * Expr CoreBndr)) as s.
    clear pairs_WS.
    induction pairs.
    * reflexivity.
    * intro.
      simpl. repeat (expand_pairs; simpl); destruct a; simpl.
      f_equal.
      apply IHl.
  Qed.

  (** Main well-scopedness theorem:
      If the input is well-scoped, then so is the output of [exitify].*)
  Theorem exitify_WellScoped:
    forall body,
    NoDup (map varUnique (map (fun '(Mk_NJPair v _ _ _) => v) pairs)) ->
    WellScoped body (extendVarSetList (getInScopeVars in_scope) (map (fun '(Mk_NJPair v _ _ _) => v) pairs)) ->
    WellScoped (exitify (extendInScopeSetList in_scope (map (fun '(Mk_NJPair v _ _ _) => v) pairs)) (map toJPair pairs) body)
               (getInScopeVars in_scope).
  Proof.
    intros ? HNoDup HWSbody.
    cbv beta delta [exitify].
    cbv zeta.
    fold recursive_calls.
    fold go.
    fold ann_pairs.
    fold pairs'_exits.
    fold mkExitLets.
    expand_pairs.
    fold pairs'.
    fold exits.
    change (WellScoped (mkExitLets exits (mkLetRec pairs' body)) (getInScopeVars in_scope)).
    assert (WellScopedFloats exits). {
      apply all_exists_WellScoped.
    }
    apply mkExitLets_WellScoped.
    * apply WellScoped_MkLetRec.
      simpl in *.
      rewrite map_fst_pairs'.
      repeat split.
      + assumption.
      + rewrite Forall'_Forall in *.
        apply pairs'_WS.
      + rewrite <- WellScoped_mkLams.
        rewrite <- WellScoped_mkLams in HWSbody.
        apply WellScoped_extendVarSetList; only 2: assumption.
        rewrite disjointVarSet_mkVarSet.
        rewrite Forall_map.
        apply H.
    * apply H.
  Qed.

  (** ** Join point validity *)

  (** When is the result of [mkExitLets] valid? *)
  
  Lemma mkExitLets_JPI:
    forall exits' e jps',
    isJoinPointsValid e 0 (updJPSs jps' (map fst exits')) = true ->
    forallb (fun '(v,rhs) => isJoinId v) exits' = true ->
    forallb (fun '(v,rhs) => isJoinPointsValidPair v rhs jps') exits' = true ->
    isJoinPointsValid (mkExitLets exits' e) 0 jps' = true.
  Proof.
    intros ??.
    induction exits' as [|[v rhs] exits']; intros jps' Hbase HiJI Hpairs.
    * simpl. unfold Base.id. assumption.
    * simpl in *; fold isJoinPointsValidPair in *.
      simpl_bool.
      destruct HiJI as [HiJIv HiJIvs].
      destruct Hpairs as [Hpair Hpairs].
      split.
      - assumption. 
      - apply IHexits'.
        + assumption.
        + assumption.
        + eapply forallb_imp. apply Hpairs.
          intros [v' rhs'].
          unfold updJPS. rewrite HiJIv.
          apply isJoinPointValidPair_extendVarSet.
  Qed.


  Lemma addExit_all_joinIds:
    forall in_scope_set ty ja e,
    StateInvariant (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)
                   (addExit in_scope_set ty ja e).
  Proof.
    set (P := (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)).
    intros.
    unfold addExit.
    eapply SP_bind with (R := fun v => isJoinId v = true).
    * unfold mkExitJoinId.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply SP_return.
        (* Here we actually show that we only generate join ids *)
        rewrite isJoinId_eq.
        rewrite isJoinId_maybe_uniqAway.
        rewrite isJoinId_maybe_setIdOccInfo.
        rewrite isJoinId_maybe_asJoinId.
        reflexivity.
    * intros x HiJI.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply StateInvariant_bind_return.
        apply SP_put.
        subst P.
        simpl; simpl_bool. split; assumption.
  Qed.

  Lemma go_all_joinIds:
    forall captured ann_e,
    StateInvariant (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)
                   (go captured ann_e).
  Proof.
    set (P := (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)).
    (* This cannot be structural recursion. Will need a size on expression. *)
    fix 2. rename go_all_joinIds into IH.
    intros.
    replace go with (go_f go) by admit. (* Need to use [go_eq] here *)
    cbv beta delta [go_f]. (* No [zeta]! *)
    (* Float out lets *)
    repeat float_let.

    (* First case *)
    enough (Hnext: StateInvariant P j_37__). {
      destruct (collectArgs e) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Second case *)
    subst j_37__.
    enough (Hnext: StateInvariant P j_36__). {
      destruct (is_exit && negb is_interesting) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Third case *)
    subst j_36__.
    enough (Hnext: StateInvariant P j_35__). {
      destruct (is_exit && captures_join_points ) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Third case: Actual exitification *)
    subst j_35__.
    enough (Hnext: StateInvariant P j_22__). {
      destruct is_exit ; try apply Hnext.
      apply StateInvariant_bind_return.
      apply addExit_all_joinIds.
    }
    clear is_exit isCapturedVarArg is_interesting captures_join_points args e fvs.

    (* Fourth case: No exitification here, so descend*)
    subst j_22__.
    enough (Hnext: StateInvariant P j_4__). {
      destruct ann_e as [fvs e] eqn:Hann.
      destruct e; try apply Hnext.
      * (* Case [Case] *)
        apply StateInvariant_bind_return.
        apply StateInvariant_forM.
        intros [[dc pats] rhs] HIn.
        apply StateInvariant_bind_return.
        apply IH.
      * (* Case Let *) 
        repeat float_let.

        enough (Hnext': StateInvariant P j_18__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          destruct (isJoinId_maybe j) as [join_arity|] eqn:HiJI; try apply Hnext'.
          destruct (collectNAnnBndrs join_arity rhs) as [params join_body].
          apply StateInvariant_bind.
          + apply IH.
          + intros. apply StateInvariant_bind_return.
            apply IH.
        }

        subst j_18__.
        enough (Hnext': StateInvariant P j_10__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          destruct (isJoinId (Tuple.fst (Panic.head pairs'))); try apply Hnext'.
          + intros.
            apply StateInvariant_bind.
            - apply StateInvariant_forM.
              intros [j rhs] HIn.
              repeat float_let.
              destruct (collectNAnnBndrs join_arity rhs) as [params join_body].
              apply StateInvariant_bind_return.
              apply IH.
            - intro x.
              apply StateInvariant_bind_return.
              apply IH.
        }

        subst j_10__.
        apply StateInvariant_bind_return.
        apply IH.
    }

    subst j_4__.
    apply StateInvariant_return.

  (* Not structurally recursive *)
  Fail Guarded.
  Admitted.

  Lemma all_exists_joinIds:
    forallb (fun '(v, _) => isJoinId v) exits = true.
  Proof.
    unfold exits.
    unfold pairs'_exits.
    eapply SP_snd_runState.
    * apply StateInvariant_forM.
      intros [v rhs] HIn.
      expand_pairs.
      apply StateInvariant_bind_return.
      apply go_all_joinIds.
    * reflexivity.
  Qed.

  (* TODO: There would be less repetition if we have a 
    [isJoinPointsValidJoinPair] that implies both 
    [isJoinPointsValidPair] and [isJoinId] *)
    
  Lemma isJoinPointsValid_delVarSet_nonJP:
    forall e jps n a,
    isJoinId a = false ->
    isJoinPointsValid e n (delVarSet jps a) = isJoinPointsValid e n jps.
  Admitted.
  Lemma isJoinPointsValid_delVarSetList_mono:
    forall e jps n vs,
    isJoinPointsValid e n (delVarSetList jps vs) = true -> isJoinPointsValid e n jps = true.
  Admitted.

  Lemma isJoinPointsValid_updJPSs_irrelevant:
    forall e jps n vs,
    forallb (fun v => negb (isJoinId v) || negb (elemVarSet v (exprFreeVars e))) vs = true ->
    isJoinPointsValid e n (updJPSs jps vs) = true ->
    isJoinPointsValid e n jps = true.
  Admitted.

  Lemma isJoinPointvalid_collectNBinders:
    forall v rhs jps ja args body,
    isJoinPointsValidPair v rhs jps = true ->
    isJoinId_maybe v = Some ja ->
    collectNBinders ja rhs = (args,body) ->
    isJoinPointsValid body 0 (updJPSs jps args) = true.
  Admitted.

  Lemma addExit_all_valid:
    forall in_scope_set jps ty ja args e,
    (* The RHS needs to be valid *)
    isJoinPointsValid e 0 jps = true -> 
    (* The join arity should match the number of lambdas added *)
    ja = (length args) ->
    (* No argument may be a join point *)
    forallb (fun a => negb (isJoinId a)) args = true ->

    StateInvariant (fun xs => forallb (fun '(v, rhs) => isJoinPointsValidPair v rhs jps) xs = true)
                   (addExit in_scope_set ty ja (mkLams args e)).
  Proof.
    clear jps.
    intros.
    set (P := (fun xs => forallb _ xs = true)).
    unfold addExit.
    eapply SP_bind with (R := fun v => isJoinId_maybe v = Some ja).
    * unfold mkExitJoinId.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply SP_return.
        (* Here we actually show that we only generate join ids *)
        rewrite isJoinId_maybe_uniqAway.
        rewrite isJoinId_maybe_setIdOccInfo.
        rewrite isJoinId_maybe_asJoinId.
        reflexivity.
    * intros x HiJI.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply StateInvariant_bind_return.
        apply SP_put.
        subst P.
        simpl; simpl_bool.
        split; only 2: assumption.
        unfold isJoinPointsValidPair, isJoinPointsValidPair_aux.
        rewrite HiJI.
        subst.
        (* Zoom past the Lams *)
        clear HPxs.
        clear HiJI.
        revert dependent jps.  clear jps.
        induction args; intros jps HiJPVe.
        + simpl. cbn. assumption.
        + replace ((length (a :: args))) with (1 + (length args)) by admit.
          destruct (Nat.eqb_spec (1 + (length args)) 0); only 1: lia.
          replace (mkLams (a :: args) e) with (Lam a (mkLams args e)) by reflexivity.
          cbn -[Nat.add].
          destruct (Nat.ltb_spec (1 + (length args)) 1); only 1: lia.
          replace (1 +  (length args) =? 1) with ((length args) =? 0) by admit.
          replace (1 +  (length args) - 1) with ( (length args)) by admit.
          simpl in H1. simpl_bool. destruct H1.
          apply IHargs.
          ** apply H1.
          ** rewrite negb_true_iff in H0.
             rewrite isJoinPointsValid_delVarSet_nonJP by assumption.
             assumption.
  Admitted.

  Lemma go_all_valid:
    forall captured ann_e,
    isJoinPointsValid (deAnnotate ann_e) 0 (updJPSs jps captured) = true ->
    StateInvariant (fun xs => forallb (fun '(v, rhs) => isJoinPointsValidPair v rhs jps) xs = true)
                   (go captured ann_e).
  Proof.
    set (P := (fun xs => forallb _ xs = true)).
    (* This cannot be structural recursion. Will need a size on expression. *)
    fix 2. rename go_all_valid into IH.
    intros ?? HiJPVe.
(*     rewrite go_eq. *)
    replace go with (go_f go) by admit. (* Need to use [go_eq] here *)
    cbv beta delta [go_f]. (* No [zeta]! *)
    (* Float out lets *)
    repeat float_let.

    (* First case *)
    enough (Hnext: StateInvariant P j_37__). {
      destruct (collectArgs e) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Second case *)
    subst j_37__.
    enough (Hnext: StateInvariant P j_36__). {
      destruct (is_exit && negb is_interesting) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Third case *)
    subst j_36__.
    enough (Hnext: (is_exit && captures_join_points = false) ->
                   StateInvariant P j_35__). {
      destruct (is_exit && captures_join_points).
      * apply StateInvariant_return.
      * apply Hnext. reflexivity.
    }
    intro Hno_capture.

    (* Third case: Actual exitification *)
    subst j_35__.
    enough (Hnext: StateInvariant P j_22__). {
      clearbody j_22__ j_4__.
      destruct is_exit ; try apply Hnext.
      apply StateInvariant_bind_return.
      assert (HniJIargs: forallb (fun a : Var => negb (isJoinId a)) args = true)
        by admit. (* Needs to relate [any] to [forallb] *)
      apply addExit_all_valid.
      * apply isJoinPointsValid_updJPSs_irrelevant with (vs := captured).
        + admit. (* Need lemma about [forallb] and [filter] *)
        + assumption.
      * admit. (* Need Base theory here *)
      * assumption.
    }
    clear is_exit is_interesting captures_join_points args e fvs Hno_capture.

    (* Fourth case: No exitification here, so descend*)
    subst j_22__.
    enough (Hnext: StateInvariant P j_4__). {
      destruct ann_e as [fvs e] eqn:Hann.
      destruct e; try apply Hnext.
      * (* Case [Case] *)
        apply StateInvariant_bind_return.
        apply StateInvariant_forM.
        intros [[dc pats] rhs] HIn.
        apply StateInvariant_bind_return.
        apply IH.
        (* This is boring stuff here... *)
        simpl in HiJPVe. simpl_bool. destruct HiJPVe.
        rewrite forallb_forall in H0.
        specialize (H0 (dc, pats, deAnnotate rhs)).
        simpl; rewrite updJPSs_append, updJPSs_cons.
        simpl_bool.
        apply H0.
        rewrite in_map_iff.
        exists (dc, pats, rhs). split. reflexivity. assumption.

      * (* Case Let *) 
        repeat float_let.

        enough (Hnext': StateInvariant P j_18__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          destruct (isJoinId_maybe j) as [join_arity|] eqn:HiJI; try apply Hnext'.
          destruct (collectNAnnBndrs _ _) as [params join_body] eqn:Hrhs.
          assert (collectNBinders join_arity (deAnnotate rhs) = (params, deAnnotate join_body)) by admit.
          apply StateInvariant_bind.
          + apply IH.
            (* Boring stuff *)
            simpl in HiJPVe. simpl_bool. destruct HiJPVe.
            rewrite updJPSs_append.
            eapply isJoinPointvalid_collectNBinders; try eassumption.
          + intros. apply StateInvariant_bind_return.
            apply IH.
            simpl in HiJPVe. simpl_bool. destruct HiJPVe.
            rewrite updJPSs_append, updJPSs_cons, updJPSs_nil.
            apply H1.
        }

        subst j_18__.
        enough (Hnext': StateInvariant P j_10__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          simpl deAnnotate in HiJPVe.
          replace (flat_map _ _) with (map (fun '(v,e) => (v, deAnnotate e)) pairs') in HiJPVe by admit.
          simpl in HiJPVe. simpl_bool. destruct HiJPVe. destruct H. destruct H0.
          rewrite orb_true_iff in H1.
          destruct H1.
          + (* No join ids *)
            replace (isJoinId (Tuple.fst _)) with false.
            assumption.
            symmetry.
            destruct pairs' as [|[j rhs] pairs'']; try inversion H.
            simpl in H1. simpl_bool. destruct H1. rewrite negb_true_iff in H1. simpl in H1.
            admit. (* Need to unfold Panic.head *)
          + (* All join ids *)
            replace (isJoinId (Tuple.fst _)) with true by admit. (* like above *)

            rewrite forallb_forall in H0.
            rewrite forallb_forall in H1.
            rewrite !map_map in *.
            replace (map _ _) with (map fst pairs') in H0
                  by (apply map_ext; intro; destruct a; reflexivity).
            replace (map _ _) with (map fst pairs') in H2
                  by (apply map_ext; intro; destruct a; reflexivity).

            apply StateInvariant_bind.
            - apply StateInvariant_forM.
              intros [j rhs] HIn.
              repeat float_let.
              destruct (collectNAnnBndrs join_arity rhs) as [params join_body] eqn:Hrhs.
              assert (collectNBinders join_arity (deAnnotate rhs) = (params, deAnnotate join_body)) by admit.
              apply StateInvariant_bind_return.
              apply IH.
              rewrite !updJPSs_append.
              eapply isJoinPointvalid_collectNBinders.
              ** Fail apply H0. (* ugh *)
                 specialize (H0 (j, deAnnotate rhs)).
                 simpl in H0.
                 apply H0.
                 apply in_map_iff. eexists. split; [|eassumption]. reflexivity.
              ** apply isJoinId_isJoinId_maybe.
                 specialize (H1 (j, deAnnotate rhs)). simpl in H1.
                 apply H1.
                 apply in_map_iff. eexists. split; [|eassumption]. reflexivity.
              ** apply H3.
            - intro x.
              apply StateInvariant_bind_return.
              apply IH.
              rewrite updJPSs_append.
              apply H2.
        }

        subst j_10__.
        apply StateInvariant_bind_return.
        apply IH.
        rewrite updJPSs_append.
        simpl (deAnnotate _) in HiJPVe.
        admit. (* We need to again look at both cases of Rec and NonRec,
                  deal with deAnnotate, to get to the statement about the base case.
                  (Or refactor isJoinPointsValid to not require that) *)
    }

    subst j_4__.
    apply StateInvariant_return.

  (* Not structurally recursive *)
  Fail Guarded.
  Admitted.

  Lemma all_exists_valid:
    forallb (fun '(v, rhs) => isJoinPointsValidPair v rhs jps) exits = true.
  Proof.
    unfold exits.
    unfold pairs'_exits.
    eapply SP_snd_runState.
    * apply StateInvariant_forM.
      intros [v rhs] HIn.
      expand_pairs.
      apply StateInvariant_bind_return.
      apply go_all_valid.
      eapply isJoinPointvalid_collectNBinders.
      + admit. (* Need to thread in invariant here *)
      + admit. (* Yeah, we really should also show that these are join ids here *)
      + admit. (* Lemma bout collectNBinders and collectNAnnBndrs. @lastland? *)
    * reflexivity.
  Admitted.

  (** Main result *)

  Theorem exitify_JPI:
    forall body,
    pairs <> [] ->
    isJoinPointsValid (Let (Rec (map toJPair pairs)) body) 0 jps = true ->
    isJoinPointsValid (exitify (extendInScopeSetList in_scope (map (fun '(Mk_NJPair v _ _ _) => v) pairs)) (map toJPair pairs) body) 0 jps = true.
  Proof.
    intros.
    cbv beta delta [exitify].
    cbv zeta.
    fold recursive_calls.
    fold go.
    fold ann_pairs.
    fold pairs'_exits.
    fold mkExitLets.
    expand_pairs.
    fold pairs'.
    fold exits.
    change (isJoinPointsValid (mkExitLets exits (mkLetRec pairs' body)) 0 jps = true).
    apply mkExitLets_JPI.
    * admit.
    * apply all_exists_joinIds.
    * apply all_exists_valid.
  Admitted.

End in_exitify.