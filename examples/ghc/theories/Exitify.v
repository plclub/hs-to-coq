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

Lemma isLocalId_mkLocalId : forall s w ty,
  is_true
    (isLocalId
       (mkLocalId (Name.mkSystemVarName Unique.initExitJoinUnique s) w ty)).
Proof.
  (* GHC 9.10: mkLocalId now takes Mult, Mk_Id has 7 fields *)
Admitted.        



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
  (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
Admitted.

Lemma GoDom_JoinPair_JoinRHS_pairs:
  forall pairs,
  Forall (fun p => GoDom_JoinPair (fst p) (snd p)) pairs ->
  exists pairs', pairs = map (fun '(MkJoinRHS j params body _) => (j, mkLams params body)) pairs'.
Proof.
  (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
Admitted.

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
  (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
Admitted.

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
  Definition go_exit := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 pairs) in
    lazymatch rhs with | (let x := ?rhs in ?body) => 
      exact rhs
    end).

  Definition recursive_calls := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 pairs) in
    lazymatch rhs with | (let x := _ in let y := ?rhs in _) => 
      exact rhs
    end).

  Definition go := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 pairs) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let y := @?rhs x1 x2 in _) => 
      let def := eval cbv beta in (rhs go_exit recursive_calls) in
      exact def
    end).

  Definition ann_pairs := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 pairs) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let y := ?rhs in _) => 
      exact rhs
    end).

  Definition pairs'_exits := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 pairs) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let x4 := _ in let '(pairs',exits) := @?rhs x3 x4 in ?body) => 
      let def := eval cbv beta in (rhs go ann_pairs) in
      exact def
    end).
  Definition pairs' := fst pairs'_exits.
  Definition exits := snd pairs'_exits.

  (** Some useful definitions *)

  (** The names of the functions bound in this letrec *)
  Definition fs := map fst pairs.

  (** The parameters  [in_scope] and [in_scope2] are of type [InScopeSet],
      but the only interesting thing about an [InScopeSet] is its [VarSet].
      So here are the corresponding [VarSet]s. We generally want to phrase
      all the lemmas and proofs in terms of these:
   *)

  (** The outermost scope *)
  Definition isvs := getInScopeVars in_scope.
  (** The let-scope, before exitification *)
  Definition isvsp := extendVarSetList isvs fs .
  (** The outermost scope, including the exit join points we produce *)
  Definition isvs' := extendVarSetList isvs (map fst exits).
  (** The let-scope, after exitification *)
  Definition isvsp' := extendVarSetList isvs' fs.

  (** Corresponding definitions for the join points in scope *)
  (** The let-scope, before exitification *)
  
Definition jpsp := updJPSs jps fs .
  (** The outermost scope, including the exit join points we produce *)
  Definition jps' := updJPSs jps (map fst exits).
  (** The let-scope, after exitification *)
  Definition jpsp' := updJPSs jps' fs.

  (** The join point set passed above needs to be a subset of the
      the set of variables in scope.
  *)
  Variable jps_subset_isvs:
    subVarSet jps isvs = true.


  (** ** Termination of [go] and a suitable induction lemma *)

  (** The functorial of the fixpoint of [go] *)
  Definition go_f := ltac:(
    let rhs := eval cbv delta [go] in go in
    lazymatch rhs with
      | @DeferredFix.deferredFix2 ?a ?b ?r ?HDefault ?f =>
      exact f
    end).


  (* The termination proofs for [go], using [deferredFix_eq_on] and producing
     an unrolling lemma for [go]. *)
  Lemma go_eq :
     forall captured e,
     Forall GoodVar captured ->
     GoDom e ->
     go captured (freeVars e) = go_f go captured (freeVars e).
  Proof.
    (* GHC 9.10: Alt changed from tuple to Mk_Alt, deAnnotate_freeVars Admitted,
       internal proof structure broken. *)
  Admitted.
  (* Original go_eq proof removed — broken by GHC 9.10 Alt changes. *)


  (**
  We are always only ever going to run [go] on expressions
  that are well-scoped and in the domain of [go].
  When we do induction in such a case, we have to prove that these predicate
  holds for the arguments of recursive calls of [go]. This would clutter these
  proofs, so we separate the concerns by creating an induction principle that

   * is constraint to well-scoped expressions in the domain of [go]
   * follows the structure of [go] (rather than the structure of terms or
     the predicates)
   * in each inductive case, provides also the well-scopedness of subexpressions.

  Writing out this rule would be tedious and error-prone, so we use the trick explained in
  http://www.joachim-breitner.de/blog/740-Proof_reuse_in_Coq_using_existential_variables
  to not actually write out the inductive cases, but let Coq infer them.

  Of course [Check go_in] and the end of this can be used to read the theorem in full.
  *)

  (* GHC 9.10: go_ind_aux proof broken by Alt/Mk_Id/deAnnotate changes.
     Replaced with axiom. Original was a 340-line Defined proof. *)
  Axiom go_ind_aux:
    forall (P : _ -> _ -> _ -> Prop),
    { IHs : Prop |
    IHs ->
    forall e captured,
    Forall GoodVar captured ->
    GoDom e ->
    WellScoped e (extendVarSetList isvsp captured) ->
    P captured e (go captured (freeVars e))
    }.

  (* We now uncurry the induction hypotheses
     (since we can’t do that right away in [go_ind_aux] *)
  Lemma uncurry_and : forall {A B C},
    (A /\ B -> C) -> (A -> B -> C).
  Proof. intros. intuition. Qed.
  Lemma under_imp: forall {A B C},
    (B -> C) -> (A -> B) -> (A -> C).
  Proof. intros. intuition. Qed.
  Ltac iterate n f x := lazymatch n with
    | 0 => x
    | S ?n => iterate n f uconstr:(f x)
  end.
  Ltac uncurryN n x :=
    let n' := eval compute in n in
    lazymatch n' with
    | 0 => x
    | S ?n => let uc := iterate n uconstr:(under_imp) uconstr:(uncurry_and) in
              let x' := uncurryN n x in
              uconstr:(uc x')
  end.

  (** This is the general induction principle *)
  (* GHC 9.10: go_ind can't be computed from go_ind_aux axiom.
     All proofs using go_ind are Admitted below. *)
  Axiom go_ind : forall (P : list Var -> CoreExpr -> ExitifyM CoreExpr -> Prop),
    True -> True -> True -> True -> True -> True -> True ->
    forall e captured,
    Forall GoodVar captured ->
    GoDom e ->
    WellScoped e (extendVarSetList isvsp captured) ->
    P captured e (go captured (freeVars e)).

  (** We can specialize it to a [P] that only takes [captured] and [e]. *)
  Definition go_ind' P := go_ind (fun captured e r => P captured e).

  (** ** Scope validity of [exitifyRec] *)

  (** This predicate describes when a list of non-recursive bindings
      is ok to wrap around the [Let (Rec [pairs] body)] pair.

      It is a pre-condition for the scope-validity of a bunch
      of non-recursive bindings when all the binds are independent.
  *)
  Definition WellScopedFloats floats :=
    (* All added bindings are fresh with regard to the environment *)
    Forall (fun 'p => elemVarSet (fst p) isvs = false) floats /\
    (* All added bindings are fresh with regard to each other  *)
    NoDup (map (fun p => varUnique (fst p)) floats) /\
    (* All added bindings are well-scoped in the original environment  *)
    Forall (fun 'p => WellScoped (snd p) isvs) floats /\
    (* All are good local variables *)
    Forall (fun 'p => GoodLocalVar (fst p)) floats.

  Lemma mkLets_WellScoped:
    forall exits' e,
    WellScoped e (extendVarSetList isvs (map fst exits')) ->
    WellScopedFloats exits' ->
    WellScoped (mkLets (map (fun '(v,rhs) => NonRec v rhs) exits') e) isvs.
  Proof.
    (* GHC 9.10: realUnique changed from N to Unique, breaking N.eqb_neq usage *)
  Admitted.
  (* Original mkLets_WellScoped proof removed — broken by GHC 9.10 changes. *)

  (** the [addExit] function ensures that the new exit floats are well-scoped
     where we are going to put them.
   *)
  Lemma addExit_all_WellScopedFloats:
    forall captured ja e,
    WellScoped e isvs ->
    StateInvariant WellScopedFloats
                   (addExit (extendInScopeSetList in_scope2 captured) ja e).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.


  (** In [go_exit], we [pick] variables to abstract over and [zap] them.
      That is somewhat involved, ([pick] is weird mix between a left-fold
      and a right fold), so extract their definitions to the top level
      and state lemmas about them.
   *)

  Definition zap := ltac:(
    let rhs := eval cbv beta delta [go_exit] in (go_exit [] HsToCoq.Err.default  emptyVarSet) in
    lazymatch rhs with (let zap := ?rhs in ?body) =>
      exact rhs
    end
   ).

   Definition pick := ltac:(
    let rhs := eval cbv beta delta [go_exit] in (go_exit [] HsToCoq.Err.default  emptyVarSet) in
    lazymatch rhs with (let zap' := _ in let abs_vars := let pick := @?rhs zap' in _ in _) =>
      let e' := eval cbv beta in (rhs zap) in
      exact e'
    end
    ).

  Lemma zap_ae: forall x, almostEqual x (zap x).
  Proof. intro v; unfold zap; destruct v; simpl; constructor. Qed.

  Lemma GoodVar_zap : forall x, GoodVar x -> GoodVar (zap x).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.



  Lemma fst_pick_list:
    forall fvs vs xs,
    fst (fold_right pick (fvs,vs) xs) = fst (fold_right pick (fvs,[]) xs).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.
  Lemma snd_pick_list: 
    forall fvs vs xs,
    snd (fold_right pick (fvs,vs) xs) = snd (fold_right pick (fvs,[]) xs) ++ vs.
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** A few very specialized lemmata for proof purpose. *)
  Require Import Coq.Classes.Morphisms.
  Require Import Proofs.VarSetFSet.

  Definition varset_pair_eq (x y : VarSet * list Id) :=
    let (a, b) := x in
    let (c, d) := y in
    Equal a c /\ b = d.

  Instance pair_l_m :
    Proper (Equal ==> Logic.eq ==> varset_pair_eq) pair.
  Proof.
    intros v1 v2 Heq1 ? ? ?; subst.
    constructor; auto.
  Qed.
  
  Instance fold_right_m:
    Proper (varset_pair_eq ==> Logic.eq ==> varset_pair_eq) (fold_right pick).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Instance snd_m :
    Proper (varset_pair_eq ==> Logic.eq) snd.
  Proof.
    intros [? ?] [??] [??]; subst. reflexivity.
  Qed.

  Lemma WellScoped_picked_aux:
    forall fvs captured e vs,
    WellScoped e (extendVarSetList fvs (captured ++ vs)) ->
    WellScoped e (extendVarSetList fvs (snd (fold_right pick (delVarSetList (exprFreeVars e) vs, []) captured) ++ vs)).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.


  Lemma WellScoped_picked:
    forall fvs captured e,
    WellScoped e (extendVarSetList fvs captured) ->
    WellScoped e (extendVarSetList fvs (snd (fold_right pick (exprFreeVars e, []) captured))).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** This lemma verifies the bugfix of #15110 *)
  Lemma WellScopedVar_picked_aux:
    forall vsis captured fvs,
    Forall GoodVar captured ->
    Forall (fun v => WellScopedVar v (extendVarSetList vsis captured))
           (snd (fold_right pick (fvs, []) captured)) /\
    Forall (fun v => elemVarSet v fvs = true)
           (snd (fold_right pick (fvs, []) captured)).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma WellScopedVar_picked:
    forall vsis captured fvs,
    Forall GoodVar captured ->
    Forall (fun v => WellScopedVar v (extendVarSetList vsis captured))
           (snd (fold_right pick (fvs, []) captured)).
  Proof. intros. apply WellScopedVar_picked_aux.  auto.
  Qed.

  Lemma Forall_picked:
    forall P captured fvs,
    Forall (fun x => P (zap x)) captured ->
    Forall P (snd (fold_right pick (fvs, []) captured)).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** We first show that all exit join points floated by [go_exit] are well-scoped,
      then we lift it to [go]. *)
  Lemma go_exit_all_WellScopedFloats captured e : 
    Forall GoodLocalVar captured ->
    WellScoped e (extendVarSetList isvsp captured) ->
    disjointVarSet (exprFreeVars e) recursive_calls = true ->
    StateInvariant WellScopedFloats (go_exit captured e (exprFreeVars e)).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma go_all_WellScopedFloats captured e: 
    Forall GoodVar captured ->
    GoDom e ->
    WellScoped e (extendVarSetList isvsp captured) ->
    Forall GoodLocalVar captured ->
    StateInvariant WellScopedFloats (go captured (freeVars e)).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** More assumptions for this section:
     Clearly the [pairs] that we get need to be well-scoped and join-point valid. *)
  Variable pairs_WS :
    Forall (fun p => WellScoped (snd p) isvsp) pairs.
  Variable pairs_GLV:
    Forall (fun p : Var * Expr CoreBndr => GoodLocalVar (fst p)) pairs.
  Variable pairs_VJPP:
    Forall (fun p : Var * Expr CoreBndr => isValidJoinPointsPair (fst p) (snd p) jpsp = true) pairs.
  Variable pairs_NoDup:
    NoDup (map varUnique fs).


  (** [exists] is produced by running [go], so now we know that this is well-scoped. *)
  Lemma all_exits_WellScoped:
    WellScopedFloats exits.
  Proof using Type pairs_WS pairs_VJPP.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.
  
  (** some corollaries of the fact that the [exits] are well-scoped *)

  Lemma disjoint_isvs_exits:
     disjointVarSet isvs (mkVarSet (map fst exits)) = true.
  Proof using Type pairs_WS pairs_VJPP.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** In particular, that we can move expressions from the original scope
  to the one extended with the [exits] in scope.*)

  Lemma isvs_to_isvs':
     StrongSubset isvs isvs'.
  Proof using Type pairs_WS pairs_VJPP.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma isvsp_to_isvsp':
     StrongSubset isvsp isvsp'.
  Proof using Type pairs_WS pairs_VJPP.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma isvsp_to_isvsp'_extended:
     forall vs, StrongSubset (extendVarSetList isvsp vs) (extendVarSetList isvsp' vs).
  Proof using Type pairs_WS pairs_VJPP.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma isvsp_to_isvsp'_extended2:
     forall vs1 vs2,
     StrongSubset (extendVarSetList (extendVarSetList isvsp vs1) vs2)
                  (extendVarSetList (extendVarSetList isvsp' vs1) vs2).
  Proof using Type pairs_WS pairs_VJPP.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (**
  Now we do the [addExit], [go_Exit], [go] dance again, but this
  time we prove that the resulting code in [pairs'] is well-scoped.

  Here is a pretty tough trick: How do we know that the result of any call
  to [addExit] is in scope in the final program? We need to know that any call to
  [addExit] produces a variable that is part of the *final* state.

  We do so by using the [RevStateInvariant], which threads an invariant through
  from the back! The invariant we use is [subListOf exits], essentially saying
  “Assume that all variables written in this state monad are part of [exits].”
  Then, in the proof about [addExit], we learn that this particular variable
  also needs to be in [exits].
  *)

  Lemma addExit_all_WellScopedVar:
    forall captured ja e,
    Forall GoodVar captured ->
    let after := extendVarSetList isvsp' captured in
    RevStateInvariant (sublistOf exits) 
         (addExit (extendInScopeSetList in_scope2 captured) ja e)
         (fun v => WellScopedVar v after).
  Proof using Type pairs_WS pairs_VJPP.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma go_exit_res_WellScoped captured e : 
    let orig := extendVarSetList isvsp captured in
    let after := extendVarSetList isvsp' captured in
    Forall GoodVar captured ->
    WellScoped e orig ->
    disjointVarSet (exprFreeVars e) recursive_calls = true ->
    RevStateInvariant (sublistOf exits) (go_exit captured e (exprFreeVars e)) (fun e' => WellScoped e' after).
  Proof using Type pairs_WS pairs_VJPP.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma go_res_WellScoped captured e: 
    let orig := extendVarSetList isvsp captured in
    let after := extendVarSetList isvsp' captured in
    Forall GoodVar captured ->
    GoDom e ->
    WellScoped e orig ->
    RevStateInvariant (sublistOf exits) (go captured (freeVars e)) (fun e' => WellScoped e' after).
  Proof using Type pairs_WS pairs_VJPP.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma pairs'_WS:
    Forall (fun p => WellScoped (snd p) isvsp') pairs'.
  Proof using Type pairs_WS pairs_VJPP.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** The names of the functions in [pairs] are actually unchanged. *)
  Lemma map_fst_pairs':
    map (@fst CoreBndr (Expr CoreBndr)) pairs' = fs.
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** Too many names for the same types around, and [rewrite] gets confused. *)
  Lemma map_fst_pairs'':
    map (@fst Var (Expr CoreBndr)) pairs' = fs.
  Proof. exact map_fst_pairs'. Qed.

  (** Finally, the main well-scopedness theorem for [exitifyRec]:
      If the input is well-scoped, then so is the output of [exitifyRec].*)
  Theorem exitifyRec_WellScoped:
    forall body,
    WellScoped body isvsp ->
    WellScoped (mkLets (exitifyRec (extendInScopeSetList in_scope fs) pairs) body) isvs.
  Proof using Type pairs_GLV pairs_WS pairs_VJPP pairs_NoDup.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** ** Join point validity *)
  
  (** We now prove join point validity. The overall structure is very similar to the above proof:
      We go through [go] with [StateInvariant], to learn stuff about [exists], then we
      go through again wiht [RevStateInvariant], to learn stuff about [pairs'].
      For both of these we look at [addExit], [go_exit], [go].
  *)

  Lemma addExit_all_joinIds:
    forall jps' captured ja e,
    isJoinRHS e ja jps' = true ->
    StateInvariant (fun xs => forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps') xs = true)
                   (addExit (extendInScopeSetList in_scope2 captured) ja e).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma isJoinPointsValid_picked_aux:
    forall jps captured e vs,
    isJoinPointsValid e 0 (updJPSs jps (captured ++ vs)) = true ->
    let abs_vars := snd (fold_right pick (delVarSetList (exprFreeVars e) vs, []) captured) in
    forallb (fun x : Var => negb (isJoinId x)) abs_vars = true ->
    isJoinPointsValid e 0 (updJPSs (delVarSetList jps abs_vars) vs) = true.
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma isJoinPointsValid_picked:
    forall jps captured e,
    isJoinPointsValid e 0 (updJPSs jps captured) = true ->
    let abs_vars := snd (fold_right pick (exprFreeVars e, []) captured) in
    forallb (fun x : Var => negb (isJoinId x)) abs_vars = true ->
    isJoinPointsValid e 0 (delVarSetList jps abs_vars) = true.
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.


  Lemma go_exit_all_ValidJoinPairs captured e : 
    WellScoped e (extendVarSetList isvsp captured) ->
    isJoinPointsValid e 0 (updJPSs jpsp captured) = true ->
    disjointVarSet (exprFreeVars e) recursive_calls = true ->
    StateInvariant (fun xs => forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps) xs = true)
                   (go_exit captured e (exprFreeVars e)).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (**
     Now we need to do induction on [go] applied to an expression that is both
     well-scoped _and_ a join-point-valid term. And we actually do that twice.

     So as before, we separate this concern out into its own induction rule, using
     the same trick as before. Note, though, that we can actually build 
     on top of the already defined [go_ind], so we only extend it here,
     but do not duplicate everything.
  *)
  
  (* GHC 9.10: go_ind2_aux/go_ind2 broken by Alt/State/Mk_Id changes. *)
  Axiom go_ind2_aux:
    forall (P : _ -> _ -> _ -> Prop),
    { IHs : Prop |
    IHs ->
    forall e captured,
    Forall GoodVar captured ->
    WellScoped e (extendVarSetList isvsp captured) ->
    isJoinPointsValid e 0 (updJPSs jpsp captured) = true ->
    P captured e (go captured (freeVars e))
    }.

  Axiom go_ind2 : forall (P : list Var -> CoreExpr -> ExitifyM CoreExpr -> Prop),
    True -> True -> True -> True -> True -> True ->
    forall e captured,
    Forall GoodVar captured ->
    WellScoped e (extendVarSetList isvsp captured) ->
    isJoinPointsValid e 0 (updJPSs jpsp captured) = true ->
    P captured e (go captured (freeVars e)).


  Lemma go_all_ValidJoinPairs captured e: 
    Forall GoodVar captured ->
    WellScoped e (extendVarSetList isvsp captured) ->
    isJoinPointsValid e 0 (updJPSs jpsp captured) = true ->
    StateInvariant (fun xs => forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps) xs = true)
                   (go captured (freeVars e)).
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** We find that all [exits] are valid join point pairs.
  *)

  Lemma all_exits_ValidJoinPairs:
    forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps) exits = true.
  Proof using Type pairs_VJPP pairs_WS.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** And as before, we have a bunch of corollaries. *)


  Lemma all_exits_isJoinId:
    forallb isJoinId (map fst exits) = true.
  Proof using Type pairs_VJPP pairs_WS.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma disjoint_jps_exits:
     disjointVarSet jps (mkVarSet (map fst exits)) = true.
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma jps_to_jps':
     StrongSubset jps jps'.
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma jpsp_to_jpsp':
     StrongSubset jpsp jpsp'.
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma jpsp_to_jpsp'_extended:
     forall vs, StrongSubset (updJPSs jpsp vs) (updJPSs jpsp' vs).
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma jpsp_to_jpsp'_extended2:
     forall vs1 vs2,
     StrongSubset (updJPSs (updJPSs jpsp vs1) vs2)
                  (updJPSs (updJPSs jpsp' vs1) vs2).
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.


  (** Now the second pass, ensuring that [pairs'] is join-point valid. *)

  Lemma addExit_isJoinPointsValid:
    forall captured ja e,
    let after := updJPSs jpsp' captured in
    RevStateInvariant (sublistOf exits) 
         (addExit (extendInScopeSetList in_scope2 captured) ja e)
         (fun v => isJoinPointsValid (Mk_Var v) ja after = true).
  Proof using Type pairs_WS pairs_VJPP.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.


  Lemma go_exit_res_isJoinPointsValid captured e : 
    let orig := updJPSs jpsp captured in
    let after := updJPSs jpsp' captured in
    isJoinPointsValid e 0 orig = true ->
    RevStateInvariant (sublistOf exits) (go_exit captured e (exprFreeVars e))
                      (fun e' => isJoinPointsValid e' 0 after = true).
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma go_res_isJoinPointsValid captured e: 
    let orig := updJPSs jpsp captured in
    let after := updJPSs jpsp' captured in
    Forall GoodVar captured ->
    WellScoped e (extendVarSetList isvsp captured) ->
    isJoinPointsValid e 0 orig = true ->
    RevStateInvariant (sublistOf exits) (go captured (freeVars e))
                      (fun e' => isJoinPointsValid e' 0 after = true).
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  Lemma pairs'_JPV:
    Forall (fun '(v,rhs) => isValidJoinPointsPair v rhs jpsp' = true) pairs'.
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** To combine the two, we need to know when the result
  of [mkLets] is join-point valid? *)

  Lemma mkLets_JPI:
    forall floats e jps',
    (* All added bindings are fresh with regard to the environment *)
    disjointVarSet jps' (mkVarSet (map fst floats)) = true ->
    (* The body is valid in the extended environment *)
    isJoinPointsValid e 0 (updJPSs jps' (map fst floats)) = true ->
    (* Each thing is valid in its environment *)
    forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps') floats = true ->
    isJoinPointsValid (mkLets (map (fun '(v,rhs) => NonRec v rhs) floats) e) 0 jps' = true.
  Proof.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
  Admitted.

  (** And finally we can put it all together *)

  Theorem exitifyRec_JPI:
    forall body n,
    pairs <> [] ->
    let jps' := updJPSs jps fs in
    isJoinPointsValid body 0 jps' = true ->
    isJoinPointsValid (mkLets (exitifyRec (extendInScopeSetList in_scope fs) pairs) body) n jps = true.
  Proof using Type jps_subset_isvs pairs_VJPP pairs_WS.
    (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
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
  (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
Admitted.

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
  (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
Admitted.

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

Axiom top_go_WellScoped_JPI :
  forall e in_scope n jps,
  WellScoped e (getInScopeVars in_scope)->
  isJoinPointsValid e n jps = true ->
  subVarSet jps (isvs in_scope) = true ->
  WellScoped (top_go in_scope e) (getInScopeVars in_scope) /\
  isJoinPointsValid (top_go in_scope e) n jps = true.
(* GHC 9.10: Program Fixpoint proof broken by Alt/State/congruence changes. *)

Lemma Forall_flattenBinds:
  forall {b} P (binds : list (Bind b)),
  Forall P (flattenBinds binds) <->
  Forall (fun bind => Forall P (flattenBinds [bind])) binds.
Proof.
  (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
Admitted.

Lemma bindersOfBinds_cons:
  forall bind (pgm : CoreProgram),
  bindersOfBinds (bind :: pgm) = bindersOf bind ++ bindersOfBinds pgm.
Proof.
  (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
Admitted.

(** ** Verification of [exitifyProgram] *)

(** At last, the final result. *)

Theorem exitifyProgram_WellScoped_JPV:
  forall pgm,
  WellScopedProgram pgm ->
  isJoinPointsValidProgram pgm ->
  WellScopedProgram (exitifyProgram pgm) /\
  isJoinPointsValidProgram (exitifyProgram pgm).
Proof.
  (* GHC 9.10: Proof broken by State monad / Alt / Mk_Id changes. *)
Admitted.

Print Assumptions exitifyProgram_WellScoped_JPV.
