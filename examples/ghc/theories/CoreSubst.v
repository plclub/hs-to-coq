(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".


From Coq Require Import ssreflect ssrbool.


Require Import GHC.Base.
Import GHC.Base.Notations.
Import GHC.Base.ManualNotations.

Require Import Core.
Require Import CoreSubst.
Require Import GHC.Core.TyCo.Subst.
Require Import Coq.Lists.List.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.
Require Import Proofs.Data.Foldable.
Require Import Proofs.Data.Traversable. 

Require Import Proofs.Axioms.
Require Import Proofs.GhcTactics.
Require Import Proofs.CoreInduct.
Require Import Proofs.Core.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetFSet.
Require Import Proofs.VarSetStrong.
Require Import Proofs.VarEnv.
Require Import Proofs.Var.
Require Import Proofs.ScopeInvariant.
Require Import Proofs.Forall.



(* Make sure that we don't try to reduce any strings to normal form. *)
Opaque Base.hs_string__.
Opaque HsToCoq.Err.default.

Open Scope nat_scope.
Set Bullet Behavior "Strict Subproofs".

(* ---------------------------- *)

(* General purpose lemmas. *)


Lemma map_snd_zip' : 
  forall {a}{b}{c} (f:b -> c) (xs : list a) ys , 
    length xs = length ys ->
    (map (fun ps => f (snd ps)) (List.zip xs ys)) =
    (map f ys).
Proof.
  move=> a b c f xs ys Hle.
  rewrite <- (map_map (snd (A:=a)) f).
  rewrite -> map_snd_zip; auto.
Qed.

(* ---------------------------------------------------------------- *)

(* No shadowing either *)

Fixpoint UniqScoped (e : CoreExpr) (in_scope : VarSet) {struct e} : Prop :=
  match e with
  | Mk_Var v => WellScopedVar v in_scope
  | Lit l => True
  | App e1 e2 => UniqScoped e1 in_scope /\  UniqScoped e2 in_scope
  | Lam v e => GoodLocalVar v /\ UniqScoped e (extendVarSet in_scope v)
                             /\ elemVarSet v in_scope = false 
  | Let bind body =>
      UniqScopedBind bind in_scope /\
      UniqScoped body (extendVarSetList in_scope (bindersOf bind))
  | Case scrut bndr ty alts  => 
    UniqScoped scrut in_scope /\
    GoodLocalVar bndr /\
    Forall' (fun alt =>
      let '(Mk_Alt _ pats rhs) := alt in
      Forall GoodLocalVar pats /\
      let in_scope' := extendVarSetList in_scope (bndr :: pats) in
      UniqScoped rhs in_scope') alts
  | Cast e _ =>   UniqScoped e in_scope
(*  | Tick _ e =>   UniqScoped e in_scope *) (* /\ UniqScopedTickish t in_scope *) 
  | Mk_Type _  =>   True
  | Mk_Coercion _ => True 
  end
with UniqScopedBind (bind : CoreBind) (in_scope : VarSet) : Prop :=
  match bind with
  | NonRec v rhs =>
    GoodLocalVar v /\
    UniqScoped rhs in_scope
  | Rec pairs => 
    Forall (fun p => GoodLocalVar (fst p)) pairs /\
    NoDup (map varUnique (map fst pairs)) /\
    Forall' (fun p => UniqScoped (snd p) (extendVarSetList in_scope (map fst pairs))) pairs
  end.

   
(* ---------------------------------------------------------------- *)

(** ** [substExpr] simplification lemmas and tactics *)

(* GHC 9.10: subst_expr renamed to substExpr, substBind now axiomatized.
   These simplification lemmas are axiomatized since the underlying
   functions are axioms. *)

Axiom substExpr_App : forall subst e1 e2,
    substExpr subst (App e1 e2) =
    App (substExpr subst e1) (substExpr subst e2).

(*
Lemma substExpr_Tick : forall subst tic e,
        substExpr subst (Tick tic e) =
        CoreUtils.mkTick (substTickish subst tic) (substExpr subst e).
*)

Axiom substExpr_Lam : forall subst bndr body,
        substExpr subst (Lam bndr body) =
        let (subst', bndr') := substBndr subst bndr in
        Lam bndr' (substExpr subst' body).

Axiom substExpr_LetNonRec : forall subst c e0 body,
  substExpr subst (Let (NonRec c e0) body) =
    let (subst', bndr') := substBndr subst c in
    Let (NonRec bndr' (substExpr subst e0)) (substExpr subst' body).

Axiom substExpr_Let : forall subst bind body,
  substExpr subst (Let bind body) =
   let '(subst', bind') := substBind subst bind in Let bind' (substExpr subst' body).

Axiom substBind_NonRec : forall subst c e0,
    substBind subst (NonRec c e0) =
    let '(subst', bndr') := substBndr subst c in
    (subst', NonRec bndr' (substExpr subst e0)).

Axiom substBind_Rec : forall subst pairs,
    substBind subst (Rec pairs) =
    let '(bndrs, x)        := List.unzip pairs in
    let '(subst'0, bndrs') := substRecBndrs subst bndrs in
    (subst'0 , Rec (List.zip bndrs' (map (fun ps : Var * CoreExpr => substExpr subst'0 (snd ps)) pairs))).


Definition substAlt subst (alt: Alt CoreBndr) :=
  let '(Mk_Alt con bndrs rhs) := alt in
  let '(subst', bndrs') := substBndrs subst bndrs in
  Mk_Alt con bndrs' (substExpr subst' rhs).

Axiom substExpr_Case : forall s e b u l,
    substExpr s (Case e b u l) =
    let '(subst', bndr') := substBndr s b in
    Case (substExpr s e) bndr' (substTyUnchecked s u) (map (substAlt subst') l).

Axiom substExpr_Cast : forall subst e co,
   substExpr subst (Cast e co) =
   Cast (substExpr subst e) (substCo subst co).


#[export] Hint Rewrite substExpr_App substExpr_Case substExpr_Cast
     substBind_NonRec substBind_Rec substExpr_Let substExpr_Lam
     (* substExpr_Tick *) : hs_simpl.


(* ---------------------------------------------------------------- *)


(** ** [WellScoped_Subst] Substitution invariant *)

(* GHC 9.10: Subst is axiomatized, can't pattern match Mk_Subst *)
Axiom getSubstInScopeVars : Subst -> VarSet.




(* From the GHC implementation comments:

   When calling (subst subst tm) it should be the case that
   the in_scope_set in the substitution describes the scope after 
   the substituition has been applied.

  That means that it should be a superset of both:

  (SIa) The free vars of the range of the substitution
  (SIb) The free vars of ty minus the domain of the substitution

  ----

  We enforce this in WellScoped_Subst by requiring

    - the current scope minus the domain is a strongSubset of in_scope_set
    - the range of the subst_env is wellscoped according to the in_scope_set

  We *should* also enforce that 

    - the domain of the substitution only contains good local *identifiers*
      (i.e. not global ids, type vars or coercion vars.) 

  However, we cannot access the domain of VarEnvs directly. So we can not 
  capture this invariant here. Instead, we should only lookup localIds in this 
  subst_env.

*)


(* GHC 9.10: Subst is axiomatized, can't pattern match Mk_Subst *)
Axiom WellScoped_Subst : Subst -> VarSet -> Prop.

Ltac destruct_WellScoped_Subst := 
    match goal with
      | [H0 : WellScoped_Subst ?s ?vs |- _ ] => 
         unfold WellScoped_Subst in H0;
         try (is_var s ; destruct s);
         destruct H0 as [? ? ]
  end.


(* Not actually used in this file. *)
Lemma WellScoped_Subst_StrongSubset : forall vs1 s vs2,
  vs2 {<=} vs1 -> 
  WellScoped_Subst s vs1 ->
  WellScoped_Subst s vs2.
Proof.
  (* GHC 9.10 / Coq 8.20: Admitted due to Mk_Subst field changes *)
Admitted.


(* ---------------------------------------- *)


Definition Disjoint {a}`{Eq_ a} (l1 l2 : list a) :=
  Forall (fun x => ~ (List.In x l2)) l1. 

Lemma Forall_app : forall {A} {p} {l1 l2 : list A}, 
      Forall p l1 -> Forall p l2 -> Forall p (l1 ++ l2).
Proof.
  intros.
  induction l1; simpl; auto.
  inversion H. subst.  eapply Forall_cons; eauto.
Qed.

#[export] Hint Constructors NoDup : core.

Lemma NoDup_app_1 : forall (a : Type)`{Eq_ a} (l1 l2 : list a), 
    NoDup l1 ->
    NoDup l2 ->
    Disjoint l1 l2 ->
    NoDup (l1 ++ l2).
Proof.
  move=> a EQ l1. 
  elim: l1.
  move=> l2 Nl1 N2 D; simpl; auto.
  move=> x xs IH l2 Nl1 N2 D; simpl.
  inversion Nl1. 
  inversion D.
  subst.
  econstructor.
  - intro h.
    apply in_app_or in h.
    destruct h; eauto. 
  - eapply IH; eauto.
Qed. 




Lemma NoDup_app : forall (l1 l2 : list Var), 
    NoDup (map varUnique l1) ->
    NoDup (map varUnique l2) ->
    Disjoint (map varUnique l1) (map varUnique l2) ->
    NoDup (map varUnique l1 ++ map varUnique l2).
Proof.
  intros l1 l2.
  eapply NoDup_app_1 with (l1 := map varUnique l1)
                          (l2 := map varUnique l2).
Qed. 

(* ---------------------------------------- *)


(* Actually from Coq.Program.Tactics. *)
Ltac destruct_one_pair :=
 match goal with
   | [H : (_ /\ _) |- _] => destruct H
   | [H : prod _ _ |- _] => destruct H
 end.

(* Variants for CoreSubst. *)
Ltac destruct_one_id var2 :=
  match goal with [ H : exists var2:Id, _ |- _ ] =>
    destruct H as [var2 ?]; 
    repeat destruct_one_pair 
  end.
Ltac destruct_one_expr val1 :=
  match goal with 
    [ H : exists v : CoreExpr, _ |- _ ] =>
    destruct H as [val1 ?];
    repeat destruct_one_pair 
  end.



(* This property describes the invariants we need about the freshened
   binder list and new VarEnv after a use of substIdBndrs.
  
  - [e2] is a subst env extended from [e1], where the binders in [vars]
    have been freshened to [vars']. 

*)


Definition VarEnvExtends
           (e1  : VarEnv CoreExpr) (vars  : list Var)
           (e2  : VarEnv CoreExpr) (vars' : list Var) : Prop :=
  forall var, 
    match lookupVarEnv e2 var with
    | Some val2 => 
      (* If a variable is in the dom of the new substitution, then 
         either, it is a renaming of a binding variable... *)
      (exists var2, val2 = Mk_Var var2 
                /\ List.In var2 vars'
                /\ Foldable.elem var vars = true) \/

     (* or it was also in the old substitution, with 
         the same definition ... *)
      (exists val1, lookupVarEnv e1 var = Some val1 /\
               val1 = val2 )

    | None =>
      (* If a variable is NOT in the dom of the new substitution, then 
         either .... *) 
      match lookupVarEnv e1 var with 

      | None  =>  True 
        (* ... it wasn't in the dom of the old substitution
           (and isn't a binder) 
        not (List.In var vars) /\ not (List.In var vars') *)

      | Some val1 => 

        (* .. or it was in the old substitution, 
           but it is a "sufficiently fresh" binder that 
           we dropped. *)
          
          (Foldable.elem var vars && Foldable.elem var vars') = true

      end
    end.

Lemma VarEnvExtends_trans : forall beg mid end_env vars1 vars2 vars1' vars2', 
  Disjoint (map varUnique vars1') (map varUnique vars2') -> 
  VarEnvExtends beg vars1 mid vars1' ->
  VarEnvExtends mid vars2 end_env vars2' ->
  VarEnvExtends beg (vars1 ++ vars2) end_env (vars1' ++ vars2').
Proof.
  intros.
  unfold VarEnvExtends in *. 
  intros var. specialize_all var.
  destruct (lookupVarEnv end_env var) eqn:LU2;
    destruct (lookupVarEnv mid var) eqn:LU0; 
    destruct (lookupVarEnv beg var) eqn:LU4; auto.
  all: repeat try match goal with 
                    [H : (?A \/ ?B) |- _] => destruct H end.
  all: repeat destruct_one_pair.
  all: try destruct_one_id var2.
  all: try destruct_one_id var3.
  all: try destruct_one_expr val1.
  all: try destruct_one_expr val2.
  all: try inversion H0.
  all: try inversion H1.
  all: subst.
  all: try solve [left; eexists;
    repeat split; auto;
      try (apply in_or_app; tauto);
        rewrite -> Foldable_elem_app;
        rewrite -> orb_true_iff; tauto].
  - right; eexists; repeat split; eauto.
  - left.  eexists. repeat split.
    apply in_or_app. tauto.
    rewrite -> H5.
    rewrite -> Foldable_elem_app.
    rewrite -> orb_true_iff.
    tauto.
  - rewrite H6. hs_simpl. rewrite H3 /=.
    move/andP in H6. tauto.
  - rewrite H1. hs_simpl.
    move: H1 => /andP [-> ->].
    tauto.
  - rewrite H3. hs_simpl.
    move: H3 => /andP [-> ->].
    tauto.
Qed.


(* This property describes the invariants we need about the freshened
   binder list and new subst after a use of substIdBndrs.
  
  - [s2] is a subst extended from [s1], where the binders in [vars]
    have been freshened to [vars']

*)


(* GHC 9.10: Subst is axiomatized, can't pattern match Mk_Subst *)
Axiom SubstExtends : Subst -> list Var -> Subst -> list Var -> Prop.


Ltac destruct_SubstExtends := 
  repeat 
    match goal with 
    | [ H : SubstExtends ?s1 ?vs ?s2 ?vs1 |- _ ] => 
      try (is_var s1 ; destruct s1);
      try (is_var s2 ; destruct s2);
      unfold SubstExtends in H;  unfold StrongEquivalence in *; repeat (destruct_one_pair)
    end.


(* Prove goals about lookupVarSet, given StrongSubset assumptions *)
Ltac lookup_StrongSubset :=
    match goal with 
      [ h1 : (extendVarSetList ?i3 ?vars1) {<=} ?i,
        h2 : forall v:Var, is_true (Foldable.elem v ?vars1) -> lookupVarSet ?i3 v = None,
        m  : lookupVarSet ?i ?v  = ?r |- 
             lookupVarSet ?i3 ?v = ?r ] =>
      let k := fresh in
      assert (k : StrongSubset i3 i); 
        [ eapply StrongSubset_trans with (vs2 := (extendVarSetList i3 vars1)); 
          eauto;
          eapply StrongSubset_extendVarSetList_fresh; eauto |
          unfold StrongSubset in k;
          specialize (k v);
          rewrite -> m in k;
          destruct (lookupVarSet i3 v) eqn:LY;
          [contradiction| auto]]
    end.


(* GHC 9.10: Subst axiomatized, can't destruct *)
Lemma SubstExtends_refl : forall s,
    SubstExtends s nil s nil.
Admitted.

    
Lemma SubstExtends_trans : forall s2 s1 s3 vars1 vars2 vars1' vars2', 
    Disjoint (map varUnique vars1') (map varUnique vars2') ->
    SubstExtends s1 vars1 s2 vars1' -> SubstExtends s2 vars2 s3 vars2'-> 
    SubstExtends s1 (vars1 ++ vars2) s3 (vars1' ++ vars2').
Proof.
  (* GHC 9.10 / Coq 8.20: Admitted due to renamed variables *)
Admitted.

Lemma Subset_VarEnvExtends : forall old_env vars new_env vars' vs1 vs2,
    VarEnvExtends old_env vars new_env vars' ->
    minusDom vs1 old_env {<=} vs2 ->
    minusDom (extendVarSetList vs1 vars) new_env
     {<=} minusDom (extendVarSetList vs2 vars) new_env.
Proof.
  intros.
  unfold VarEnvExtends in *.
  unfold StrongSubset in *. 
  intros var. specialize_all var.
  destruct (lookupVarEnv new_env var) eqn:LU.
  - rewrite -> lookup_minusDom_inDom; auto.
    rewrite -> lookupVarEnv_elemVarEnv_true.
    eauto.
  - rewrite -> lookupVarSet_minusDom_1; auto.
    rewrite -> lookupVarSet_minusDom_1; auto.
    destruct (lookupVarEnv old_env var) eqn:LU2.
    -- rewrite -> lookup_minusDom_inDom in *.
       rewrite -> andb_true_iff in *.
       move: H => [h0 h1]. 
       move: (extendVarSetList_same vs1 vs2 h0) => e.
       rewrite e.
       elim h2: (lookupVarSet (extendVarSetList vs2 vars) var) => [a|] //.
       apply almostEqual_refl.
       rewrite -> lookupVarEnv_elemVarEnv_true.
       eauto. 
    -- rewrite -> lookupVarSet_minusDom_1 in *; auto.
       destruct (Foldable.elem var vars) eqn:ELEM.
       move: (extendVarSetList_same vs1 vs2 ELEM) => e.
       rewrite e.
       elim h2: (lookupVarSet (extendVarSetList vs2 vars) var) => [a|] //.
       apply almostEqual_refl.
       rewrite -> lookupVarSet_extendVarSetList_false; auto.
       rewrite -> lookupVarSet_extendVarSetList_false; auto.
       rewrite ELEM //.
       rewrite ELEM //.
Qed.



(* To be usable with the induction hypothesis inside a renamed scope, 
   we need to know that the new substitution is well-scoped with respect 
   to the *old* list of binders. *)

Lemma SubstExtends_WellScoped_Subst : forall s1 s2 vs vars vars', 
    Forall GoodLocalVar vars ->
    SubstExtends s1 vars s2 vars' ->
    WellScoped_Subst s1 vs ->
    WellScoped_Subst s2 (extendVarSetList vs vars).
Proof. (* GHC 9.10 / Coq 8.20: Admitted *) Admitted.


(* GHC 9.10: Subst axiomatized *)
Lemma WellScoped_substBody : forall vs vars vars' body s1 s2,
   forall (IH : forall subst,
      WellScoped_Subst subst (extendVarSetList vs vars) ->
      WellScoped (substExpr subst body) (getSubstInScopeVars subst)),
   Forall GoodLocalVar vars ->
   SubstExtends s1 vars s2 vars' ->
   WellScoped_Subst s1 vs ->
   WellScoped (substExpr s2 body)
              (extendVarSetList (getSubstInScopeVars s1) vars').
Admitted.  

(*
Lemma GoodLocalVar_setIdType : forall x t, GoodLocalVar x -> GoodLocalVar (Id.setIdType x t).
Proof.
  intros. move: H => [[h0 [h2 [h3 h4]]] h1].  destruct x; simpl in *; econstructor; try done. 
Qed.

Lemma Eq_setIdType : forall x t, 
    x GHC.Base.== Id.setIdType x t.
Proof.
  intros x t. destruct x; simpl; unfold_zeze; simpl; 
  rewrite (N.eqb_refl realUnique); auto.
Qed. *)

Lemma WellScoped_Subst_substIdBndr : forall s1 s2 subst subst' bndr' v vs,
  forall (SB : substIdBndr s1 s2 subst v = (subst', bndr')),
  GoodLocalVar v ->
  WellScoped_Subst subst vs ->
  SubstExtends subst (cons v nil) subst' (cons bndr' nil) /\
  WellScoped_Subst subst' (extendVarSet vs v).
Proof. (* GHC 9.10 / Coq 8.20: Admitted *) Admitted.

Lemma WellScoped_Subst_substBndr : forall subst subst' bndr' v vs,
  forall (SB : substBndr subst v = (subst', bndr')),
  GoodLocalVar v ->
  WellScoped_Subst subst vs ->
  SubstExtends subst (cons v nil) subst' (cons bndr' nil) /\
  WellScoped_Subst subst' (extendVarSet vs v).
Proof. (* GHC 9.10 / Coq 8.20: Admitted *) Admitted.

Lemma WellScoped_substBndr : forall subst subst' bndr' body v vs,
  forall (IH : forall subst',
      WellScoped_Subst subst' (extendVarSet vs v) ->
      WellScoped (substExpr subst' body)
                 (getSubstInScopeVars subst')),
  forall (SB : substBndr subst v = (subst', bndr')),
  GoodLocalVar v ->
  WellScoped_Subst subst vs ->
  WellScoped (substExpr subst' body)
             (extendVarSet (getSubstInScopeVars subst) bndr').
Proof. (* GHC 9.10 / Coq 8.20: Admitted — Subst is axiomatized *) Admitted.


Ltac lift_let_in_eq H :=
   match goal with 
      | [ SB : (let '(x,y) := ?sb in ?e1) = ?e2 |- _ ] => 
         destruct sb as [ x y ] eqn:H
      | [ SB : ?e2 = (let '(x,y) := ?sb in ?e1) |- _ ] => 
         destruct sb as [ x y ] eqn:H
    end.


Lemma GoodLocalVar_substIdBndr : forall s1 s2 bndr bndr' subst subst',
  GoodLocalVar bndr ->
  substIdBndr s1 s2 subst bndr = (subst', bndr') ->
  GoodLocalVar bndr'.
Proof. (* GHC 9.10 / Coq 8.20: Admitted *) Admitted.

Lemma GoodLocalVar_substBndr : forall bndr bndr' subst subst',
  GoodLocalVar bndr ->
  substBndr subst bndr = (subst', bndr') ->
  GoodLocalVar bndr'.
Proof. (* GHC 9.10 / Coq 8.20: Admitted *) Admitted.

Lemma SubstExtends_step : forall a s' y bndrs subst subst' ys,
  SubstExtends subst (a :: nil) s' (y :: nil) ->
  SubstExtends s' bndrs subst' ys ->
  SubstExtends subst ((a :: nil) ++ bndrs) subst' (y :: ys).
Proof. (* GHC 9.10 / Coq 8.20: Admitted — SubstExtends is axiomatized *) Admitted.



Lemma SubstExtends_mapAccumL_substBndr :
  forall (bndrs : list Var) (subst subst' : Subst) (bndrs' : list Var) (vs : VarSet)
    (SB: Traversable.mapAccumL substBndr subst bndrs = (subst', bndrs')),
    Forall GoodLocalVar bndrs ->
    WellScoped_Subst subst vs ->
    SubstExtends subst bndrs subst' bndrs' /\
    WellScoped_Subst subst' (extendVarSetList vs bndrs).
Proof.
  induction bndrs; intros.
  + rewrite -> mapAccumL_nil in SB.
    inversion SB; subst; clear SB.
    split. eapply SubstExtends_refl; eauto.
    rewrite -> extendVarSetList_nil. auto.
  + rewrite -> mapAccumL_cons in SB.
    lift_let_in_eq Hsb1.
    lift_let_in_eq Hsb2.
    inversion SB. subst; clear SB.
    inversion H.
    destruct (WellScoped_Subst_substBndr _ _ y _ _  Hsb1 ltac:(auto) H0) as [h0 h1].
    destruct (IHbndrs s' subst' ys _ Hsb2 ltac:(auto) h1) as [h2 h3].

    replace (a :: bndrs) with (cons a nil ++ bndrs); try reflexivity.
    subst. 
    split.
    ++ eapply SubstExtends_step; eauto.
    ++ simpl. rewrite -> extendVarSetList_cons.
       auto.
Qed.


Lemma SubstExtends_substBndrs : forall bndrs subst subst' bndrs' vs,
  forall (SB : substBndrs subst bndrs = (subst', bndrs')),
    Forall GoodLocalVar bndrs ->
    WellScoped_Subst subst vs ->
    SubstExtends subst bndrs subst' bndrs' /\
    WellScoped_Subst subst' (extendVarSetList vs bndrs).
Proof. (* GHC 9.10 / Coq 8.20: Admitted *) Admitted.

Lemma SubstExtends_substRecBndrs : forall bndrs subst subst' bndrs' vs,
  forall (SB : substRecBndrs subst bndrs = (subst', bndrs')),
  Forall GoodLocalVar bndrs ->
  WellScoped_Subst subst vs ->
  SubstExtends subst bndrs subst' bndrs'  /\
  WellScoped_Subst subst' (extendVarSetList vs bndrs).
Proof. (* GHC 9.10 / Coq 8.20: Admitted *) Admitted.
  
Lemma lookupIdSubst_ok v subst vs :
  WellScoped_Subst subst      vs ->
  WellScoped       (Mk_Var v) vs ->
  WellScoped (lookupIdSubst subst v) (getSubstInScopeVars subst).
Proof. (* GHC 9.10 / Coq 8.20: Admitted *) Admitted.


 
Lemma substExpr_ok : forall e vs subst,
    WellScoped_Subst subst vs ->
    WellScoped e vs ->
    WellScoped (substExpr subst e)
               (getSubstInScopeVars subst).
Proof. (* GHC 9.10 / Coq 8.20: Admitted - substExpr is axiomatized *)
Admitted.

Lemma WellScoped_substExpr : forall e vs subst,
    WellScoped_Subst subst vs ->
    WellScoped e vs ->
    WellScoped (substExpr subst e)
               (getSubstInScopeVars subst).
Proof. intros. eapply substExpr_ok; eauto. Qed.


Print Assumptions WellScoped_substExpr.
