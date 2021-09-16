Require Import HsToCoq.DeferredFix.
Require Import Data.Graph.Inductive.Query.BFS.
Require Import Coq.Lists.List.
Require Import Data.Graph.Inductive.Internal.Queue.
Require Import NicerQueue.
Require Import Equations.Equations.
Require Import Data.Graph.Inductive.Graph.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.SetoidList.
Require Import Omega.
Require Import Wellfounded.

Require Import Path.
Require Import Helper.
Require Import Coq.FSets.FMapFacts.

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.OrderedTypeEx.

Module M := FMapList.Make(N_as_OT).
Module P := WProperties_fun N_as_OT M.
Module F := P.F.

Require Import Coq.Relations.Relation_Operators.
Require Import Lex.

(* Inductive relation*)
Section Ind.


Context {a : Type} {b : Type} { gr : Type -> Type -> Type} {Hgraph : Graph.Graph gr} {Hlaw : Graph.LawfulGraph gr}.

(*Well formed lexicographic measure*)
Definition natNodes := (@Path.natNodes a b gr Hgraph).

Definition natNodes_lt (x y : gr a b) := natNodes x < natNodes y.

Definition natNodes_eq (x y : gr a b) := natNodes x = natNodes y.
Definition list_length_lt {a} (x y : list a) := length x < length y.
Definition queue_length_lt  {a} (x y : Queue a) := list_length_lt (toList _ x) (toList _ y).

Definition bf_measure_list (a: Type) := 
  lex _ _ (natNodes_lt) natNodes_eq ((@list_length_lt a)).


Definition bf_measure_queue (a: Type) :=
  lex _ _ (natNodes_lt) natNodes_eq (@queue_length_lt a).

Lemma well_founded_bf_measure_list : forall a,  well_founded (bf_measure_list a).
Proof.
  intros. eapply WF_lex.
  - apply f_nat_lt_wf.
  - apply f_nat_lt_wf.
  - unfold Transitive. intros. unfold natNodes_eq in *; omega.
  - intros. unfold natNodes_eq in *. unfold natNodes_lt in *. destruct H. destruct H.
    omega.
  - unfold Symmetric. intros. unfold natNodes_eq in *. omega.
Qed. 

Lemma well_founded_bf_measure_queue : forall a,  well_founded (bf_measure_queue a).
Proof.
  intros. eapply WF_lex.
  - apply f_nat_lt_wf.
  - apply f_nat_lt_wf.
  - unfold Transitive. intros. unfold natNodes_eq in *; omega.
  - intros. unfold natNodes_eq in *. unfold natNodes_lt in *. destruct H. destruct H.
    omega.
  - unfold Symmetric. intros. unfold natNodes_eq in *. omega.
Qed. 

(*A few properties of this relation*)
Lemma measure_trans: forall {a} x y z,
  bf_measure_list a x y ->
  bf_measure_list a y z ->
  bf_measure_list a x z.
Proof.
  intros. unfold bf_measure_list in *.
  inversion H; subst.
  - inversion H0; subst.
    + apply lex1. unfold natNodes_lt in *. omega.
    + apply lex1. unfold natNodes_lt in *. unfold natNodes_eq in H4. omega.
  - inversion H0; subst.
    + apply lex1. unfold natNodes_lt in *. unfold natNodes_eq in H1. omega.
    + apply lex2. unfold natNodes_eq in *. omega. unfold list_length_lt in *. omega.
Qed. 

Lemma measure_antisym: forall {a} x y,
  bf_measure_list a x y ->
  ~bf_measure_list a y x.
Proof.
  intros. intro. unfold bf_measure_list in *. 
  inversion H; inversion H0; subst; unfold natNodes_lt in *; unfold natNodes_eq in *.
  - inversion H5; subst. inversion H6; subst. omega.
  - inversion H6; subst. inversion H7; subst. omega.
  - inversion H6; subst. inversion H7; subst. omega.
  - inversion H7; subst. inversion H8; subst.
    unfold list_length_lt in *. omega.
Qed.

Lemma measure_antirefl: forall {a} x,
  ~bf_measure_list a x x.
Proof.
  intros. intro. inversion H; subst; unfold natNodes_lt in *; unfold list_length_lt in *; try(omega).
Qed.


(*We define an equivalent version of BFS that is tail recursive and consists of a series of states
  that step to each other. This way, we can reason about the specific states of the algorithm. A state
  consists of the current graph, the current queue, and the current output*)
Definition state : Type := (gr a b) * (list (Node * Num.Int)) * (list (Node * Num.Int)) .


Definition get_graph (s: state) :=
  match s with
  | (g, _, _) => g
  end.

Definition get_queue (s: state) :=
  match s with
  | (_, q, _) => q
end.

Definition get_dists (s: state) :=
  match s with
  | (_, _, d) => d
  end.

(*How to step from 1 state to another. The inductive definiction makes it easier to use as
  an assumption in proofs*)
Inductive bfs_step : state -> state -> Prop :=
  | bfs_find: forall g d v j vs c g',
      isEmpty g = false ->
      match_ v g = (Some c, g') ->
      bfs_step (g, (v, j) :: vs, d) (g', (vs ++ suci c (Num.op_zp__ j (Num.fromInteger 1))),
        d ++ (v,j) :: nil)
  | bfs_skip: forall g d v j vs g',
      isEmpty g = false ->
      match_ v g = (None, g') ->
      bfs_step (g, (v, j) :: vs, d) (g', vs, d).

Definition start (g : gr a b) (v: Graph.Node) : state := (g, ((v, Num.fromInteger 0) :: nil), nil).

(*A valid state is any state that can be reached from the start state.*)
Inductive valid : state -> (gr a b) -> Node -> Prop :=
  | v_start : forall g v, vIn g v = true -> valid (start g v) g v
  | v_step : forall s s' v g, valid s' g v -> bfs_step s' s -> valid s g v.

(*From Software Foundations*)
Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

Definition bfs_multi (s1 s2 : state):= multi (bfs_step) s1 s2.

Lemma multi_valid: forall s1 s2 g v,
  valid s1 g v ->
  bfs_multi s1 s2 ->
  valid s2 g v.
Proof.
  intros. induction H0. assumption. apply IHmulti. eapply v_step. apply H. assumption.
Qed.

Definition done (s: state) := null (get_queue s) || isEmpty (get_graph s).

(*The executable, tail recursive version of this, which we will prove equivalent to the hs-to-coq version*)
Section Exec.

Lemma match_none_size: forall g v g',
  match_ v g = (None, g') -> natNodes g = natNodes g'.
Proof.
  intros. pose proof (match_remain_none g). erewrite H0. reflexivity. apply H.
Qed.  

Instance need_this_for_equations : WellFounded (bf_measure_list (Node * Num.Int)).
Proof.
  unfold WellFounded. apply well_founded_bf_measure_list.
Defined.

Equations bfs_tail (s: state) : state by wf (get_queue s, get_graph s) (bf_measure_list (Node * Num.Int)) :=
  bfs_tail (g, nil, x) => (g, nil, x);
  bfs_tail (g, (v, j) :: vs, d) => if (isEmpty g) then  (g, (v, j) :: vs, d) else
      match (match_ v g) as y return ((match_ v g = y) -> _) with
      | (Some c, g') => fun H: (match_ v g) = (Some c, g') => 
        bfs_tail (g', (vs ++ suci c (Num.op_zp__ j (Num.fromInteger 1))), d ++ (v,j) :: nil)
      | (None, g') => fun H: (match_ v g) = (None, g') => bfs_tail (g', vs, d)
      end (eq_refl).
Next Obligation.
unfold bf_measure_list. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H.
Defined.
Next Obligation.
unfold bf_measure_list. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply H. unfold list_length_lt.
simpl. omega.
Defined.

Definition expand_bfs_tail := 
fun s : gr a b * list (Node * Num.Int) * list (Node * Num.Int) =>
let (p, l) := s in
(let (g, l0) := p in
 fun l1 : list (Node * Num.Int) =>
 match l0 with
 | nil => fun l2 : list (Node * Num.Int) => (g, nil, l2)
 | p0 :: l2 =>
     fun l3 : list (Node * Num.Int) =>
     (let (n, i) := p0 in
      fun l4 l5 : list (Node * Num.Int) =>
      if isEmpty g
      then (g, (n, i) :: l4, l5)
      else
       (let (m, g') as y return (match_ n g = y -> gr a b * list (Node * Num.Int) * list (Node * Num.Int)) :=
          match_ n g in
        match
          m as m0 return (match_ n g = (m0, g') -> gr a b * list (Node * Num.Int) * list (Node * Num.Int))
        with
        | Some c =>
            fun _ : match_ n g = (Some c, g') =>
            bfs_tail (g', l4 ++ suci c (Num.op_zp__ i (Num.fromInteger 1)), l5 ++ (n, i) :: nil)
        | None => fun _ : match_ n g = (None, g') => bfs_tail (g', l4, l5)
        end) eq_refl) l2 l3
 end l1) l.

Lemma unfold_bfs_tail: forall s,
  bfs_tail s = expand_bfs_tail s.
Proof.
  intros. unfold expand_bfs_tail. apply bfs_tail_elim; intros; reflexivity.
Qed.

(*This is equivalent to repeatedly stepping with the bfs_step inductive relation. We prove this by proving that
  bfs_tail represents a multistep to a done state. So when we start with the start state, we get a valid
  done state. We will later prove that all valid done states are equivalent, so we can prove claims about bfs_tail
  by considering valid done states in general*)

Lemma bfs_tail_multi: forall s,
  bfs_multi s (bfs_tail s).
Proof.
  intros. destruct s as[r d].
  remember (snd r, fst r) as r'. generalize dependent r. revert d. 
  induction (r') using (well_founded_induction (well_founded_bf_measure_list (Node * Num.Int))).
  intros. destruct r' as [q g]. inversion Heqr'; subst. clear Heqr'. destruct r as [g q].
  rewrite unfold_bfs_tail. simpl. destruct q eqn : Q.
  - apply multi_refl.
  - destruct p as [v j]. destruct (isEmpty g) eqn : E.
    + apply multi_refl.
    + destruct (match_ v g) eqn : M.  destruct m eqn : M'.
      *  eapply multi_step. apply bfs_find. assumption. apply M. eapply H. unfold bf_measure_list.
         apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M. simpl. reflexivity.
      * eapply multi_step. apply bfs_skip. assumption. apply M. eapply H. unfold bf_measure_list.
        apply lex2. unfold natNodes_eq. assert (g = g0) by (eapply match_remain_none; apply M).
        subst. eapply match_none_size. simpl.  apply M. 
        unfold list_length_lt. simpl. assert (length l < S(length l)) by omega. apply H0. simpl. 
        assert (g = g0) by (eapply match_remain_none; apply M). subst. reflexivity.
Qed.

Lemma bfs_tail_done: forall s,
  done (bfs_tail s) = true.
Proof.
  intros. unfold done. destruct s as [r d].
  remember (snd r, fst r) as r'. generalize dependent r. revert d. 
  induction (r') using (well_founded_induction (well_founded_bf_measure_list (Node * Num.Int))).
  intros. destruct r'. inversion Heqr'. subst. clear Heqr'.
  destruct r as [g q]. rewrite unfold_bfs_tail. simpl. destruct q eqn : Q.
  - simpl. reflexivity.
  - destruct p. simpl. destruct (isEmpty g) eqn : G. simpl. assumption.
    destruct (match_ n g) eqn : M. destruct m; simpl.
    eapply H. unfold bf_measure_list. apply lex1. unfold natNodes_lt. eapply match_decr_size;
    symmetry; apply M. simpl. reflexivity. assert (g = g0) by (eapply match_remain_none; apply M). subst.
    eapply H. unfold bf_measure_list. apply lex2.
    unfold natNodes_eq. eapply match_none_size. simpl. apply M.  unfold list_length_lt. simpl.
    assert (length l < S(length l)) by omega. apply H0. simpl. reflexivity.
Qed. 

End Exec.

(*Results about multistepping and measure. In particular, we will prove that any two done states
  are equivalent, that any valid state multisteps to a done state, and several other needed results*)
Section Multi.

(*if we step from s to s', s' < s*)
Lemma measure_step: forall s s',
  bfs_step s s' ->
  bf_measure_list (Node * Num.Int) (get_queue s', get_graph s') (get_queue s, get_graph s) .
Proof.
  intros. unfold bf_measure_list. unfold transp. inversion H; subst; simpl in *.
  - apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H1.
  - apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply H1.  unfold list_length_lt.
simpl. omega.
Qed.

(*The same for multistep*)
Lemma measure_multi: forall s s',
  bfs_multi s s' ->
  s = s' \/ bf_measure_list (Node * Num.Int) (get_queue s', get_graph s') (get_queue s, get_graph s) .
Proof.
  intros. induction H.
  - left. reflexivity.
  - destruct IHmulti. subst. right. apply measure_step. assumption.
    right. eapply measure_trans. apply H1. apply measure_step. assumption.
Qed.

(*If s multisteps to s', s and s' are equal exactly when s < s' and s' < s are both false*)
Lemma multistep_eq_measure: forall s s',
  bfs_multi s s' ->
  (s = s') <-> (~bf_measure_list _ (get_queue s', get_graph s') (get_queue s, get_graph s) /\
  ~bf_measure_list (Node * Num.Int) (get_queue s, get_graph s) (get_queue s', get_graph s')). 
Proof.
  intros. split. intros. subst. split; intro;
  pose proof (measure_antirefl (get_queue s', get_graph s')); contradiction. intros.
  destruct H0. apply measure_multi in H. destruct H. subst. reflexivity. contradiction.
Qed. 

Lemma bfs_step_deterministic : forall s1 s2 s,
  bfs_step s s1 -> bfs_step s s2 -> s1 = s2.
Proof.
  intros. inversion H; subst; simpl in *.
  - inversion H0; subst; simpl in *.
    + rewrite H10 in H2. inversion H2; subst. reflexivity.
    + rewrite H10 in H2. inversion H2.
  - inversion H0; subst; simpl in *.
    + rewrite H10 in H2. inversion H2.
    + rewrite H10 in H2. inversion H2; subst. reflexivity.
Qed.

Lemma multi_from_start: forall s s' s'',
  bfs_multi s s'' ->
  bfs_multi s s' ->
  (bfs_multi s' s'' \/ bfs_multi s'' s').
Proof.
  intros. generalize dependent s'. induction H; intros.
  - right. apply H0.
  - inversion H1; subst.
    + left. eapply multi_step. apply H. apply H0.
    + assert (y=y0). eapply bfs_step_deterministic.
      apply H. apply H2. subst. apply IHmulti. apply H3.
Qed.

Lemma valid_begins_with_start: forall s g v,
  valid s g v ->
  bfs_multi (start g v) s.
Proof.
  intros. induction H.
  - constructor.
  - eapply multi_trans. apply IHvalid.  eapply multi_step. apply H0. apply multi_refl.
Qed.

(*For any two valid states, one multisteps to the other*)
Lemma valid_multi: forall s s' g v,
  valid s g v ->
  valid s' g v ->
  bfs_multi s s' \/ bfs_multi s' s.
Proof.
  intros. eapply multi_from_start. apply valid_begins_with_start. apply H0.
  apply valid_begins_with_start. assumption.
Qed.

(*A valid state is not done iff it can step*)
Lemma not_done_step: forall s g v,
  valid s g v ->
  (done s = false <-> exists s', bfs_step s s').
Proof.
  intros. split; intros.
  - destruct s as [p d]. destruct p as [g' q].
    unfold done in H0. simpl in H0.
    rewrite orb_false_iff in H0. destruct H0.
    destruct q. simpl in H0. inversion H0.
    destruct p as [v' d'].
    destruct (match_ v' g') eqn : M. destruct m.
    + exists ((g0, q ++ suci c (Num.op_zp__ d' (Num.fromInteger 1)), d ++ (v', d') :: nil)).
      constructor; assumption.
    + exists (g0, q, d). constructor; assumption.
  - destruct H0. unfold done in *; inversion H0; subst; simpl in *; assumption.
Qed.

(*If a state is done, it cannot step*)
Lemma done_cannot_step: forall s g v,
  valid s g v ->
  done s = true ->
  ~(exists s', bfs_step s s').
Proof.
  intros. intro. pose proof (not_done_step _ _ _ H).
  destruct H2. apply contrapositive in H3. contradiction. 
  rewrite H0. intro. inversion H4.
Qed.

(*A state is done if for every valid state s', s' < s is false*)
Lemma measure_done: forall s g v,
  valid s g v ->
  done s = true <-> 
  (forall s', valid s' g v -> ~bf_measure_list _(get_queue s', get_graph s') (get_queue s, get_graph s)).
Proof.
  intros. split; intros.
  - intro. pose proof (valid_multi _ _ _ _ H H1). destruct H3.
    + inversion H3. subst. pose proof (measure_antirefl (get_queue s', get_graph s')).
      contradiction. subst. pose proof (done_cannot_step _ _ _ H H0).
      apply H6. exists y. assumption.
    + apply measure_multi in H3. destruct H3. subst.
      pose proof (measure_antirefl (get_queue s, get_graph s)).
      contradiction. pose proof (measure_antisym _ _ H2). contradiction.
  - destruct (done s) eqn : D.
    + reflexivity.
    + pose proof (not_done_step _ _ _ H). apply H1 in D.
      destruct D. assert (valid x g v). eapply v_step. apply H. apply H2.
      apply H0 in H3. apply measure_step in H2. contradiction.
Qed.  

(*two valid states are equal if neither is less than the other*)
Lemma measure_unique: forall s g v s',
  valid s g v ->
  valid s' g v ->
  ~bf_measure_list _(get_queue s', get_graph s') (get_queue s, get_graph s) ->
  ~bf_measure_list _(get_queue s, get_graph s) (get_queue s', get_graph s') ->
  s = s'.
Proof.
  intros. pose proof (valid_multi _ _ _ _ H H0). destruct H3.
  - apply measure_multi in H3. destruct H3. assumption. contradiction.
  - apply measure_multi in H3. destruct H3. subst. reflexivity. contradiction.
Qed. 

(*An important lemma: any two done states that are valid are unique. This allows us to use a tail
  recursive function and still prove claims about generic done states*)
Lemma done_unique: forall s g v s',
  valid s g v ->
  valid s' g v ->
  done s = true ->
  done s' = true ->
  s = s'.
Proof.
  intros. assert (forall s', valid s' g v -> ~bf_measure_list _(get_queue s', get_graph s') (get_queue s, get_graph s)).
  eapply measure_done. assumption. assumption.
  assert (forall s'', valid s'' g v -> ~bf_measure_list _(get_queue s'', get_graph s'') (get_queue s', get_graph s')).
  eapply measure_done. assumption. assumption.
  eapply measure_unique. apply H. apply H0. apply H3. apply H0.
  apply H4. apply H.
Qed.

(*This enables us to talk about any prior valid state, with the assurance that we will multistep to the
  current, done state*)
Lemma multi_done: forall s s' g v,
  valid s g v ->
  valid s' g v ->
  done s = false ->
  done s' = true ->
  bfs_multi s s'.
Proof.
  intros. assert (exists s'', bfs_multi s s'' /\ done s'' = true).
  exists (bfs_tail s). split. apply bfs_tail_multi. apply bfs_tail_done.
  destruct H3 as [s'']. destruct H3. assert (valid s'' g v). eapply multi_valid.
  apply H. apply H3. assert (s' = s''). eapply done_unique; try(assumption).
  apply H0. apply H5. subst. assumption.
Qed.

(*A lemma that says that 2 states that step to each other are the closest valid states according to the well founded
  relation*)
Lemma bfs_step_measure_exact: forall s s' g v,
  valid s g v ->
  bfs_step s s' ->
  (forall x, valid x g v -> ~ (bf_measure_list _ (get_queue x, get_graph x) (get_queue s, get_graph s) /\
  bf_measure_list _ (get_queue s', get_graph s') (get_queue x, get_graph x))).
Proof.
  intros. intro. destruct H2.
  assert (valid s' g v). eapply v_step. apply H. assumption.
  pose proof (valid_multi _ _ _ _ H H1). destruct H5.
  inversion H5. subst. pose proof (measure_antirefl (get_queue x, get_graph x)). contradiction.
  subst. assert (y = s'). eapply bfs_step_deterministic. apply H6. assumption. subst.
  eapply measure_multi in H7. destruct H7. subst. 
  pose proof (measure_antirefl (get_queue x, get_graph x)). contradiction.
  pose proof (measure_antisym (get_queue x, get_graph x) (get_queue s', get_graph s')).
  apply H8 in H7. contradiction.
  apply measure_multi in H5. destruct H5. subst.
  pose proof (measure_antirefl (get_queue s, get_graph s)). contradiction.
  pose proof (measure_antisym (get_queue x, get_graph x) (get_queue s, get_graph s)).
  apply H6 in H2. contradiction.
Qed.

(*Why we needed that lemma: if s -> x and s' -> x, then s = s'*)
Lemma valid_determ: forall s g v s' x,
  valid s g v ->
  valid s' g v ->
  bfs_step s x ->
  bfs_step s' x ->
  s = s'.
Proof.
  intros. pose proof (valid_multi _ _ _ _ H H0).
  destruct H3.
  - apply multistep_eq_measure. apply H3.
    apply measure_multi in H3. destruct H3. subst.
    split; intro; pose proof (measure_antirefl (get_queue s', get_graph s')); contradiction.
    assert (S1 := H1). assert (S2 := H2).
    apply measure_step in H1. apply measure_step in H2. split.
    exfalso. pose proof (bfs_step_measure_exact _ _ _ _ H S1).
    specialize (H4 s' H0). apply H4. split; assumption.
    intro.
    pose proof (measure_antisym (get_queue s, get_graph s) (get_queue s', get_graph s')).
    apply H5 in H4. contradiction.
  - symmetry. apply multistep_eq_measure. apply H3.
    apply measure_multi in H3. destruct H3. subst.
    split; intro; pose proof (measure_antirefl (get_queue s, get_graph s)); contradiction.
    assert (S1 := H1). assert (S2 := H2).
    apply measure_step in H1. apply measure_step in H2. split.
    exfalso. pose proof (bfs_step_measure_exact _ _ _ _ H0 S2).
    specialize (H4 s H). apply H4. split; assumption.
    intro.
    pose proof (measure_antisym (get_queue s, get_graph s) (get_queue s', get_graph s')).
    apply H5 in H3. contradiction.
Qed.

(*Every state that is not the start state has a previous state*)
Lemma prior_state: forall s g v,
  valid s g v ->
  s <> (start g v) ->
  (exists s', valid s' g v /\ bfs_step s' s).
Proof.
  intros. inversion H; subst.
  - contradiction.
  - exists s'. split; assumption.
Qed.

(*The start state is not done*)
Lemma done_not_start: forall g v,
  vIn g v = true ->
  done (start g v) = false.
Proof.
  intros. unfold start. unfold done. simpl. destruct (isEmpty g) eqn : E.
  rewrite isEmpty_def in E. rewrite E in H. inversion H. apply v. reflexivity.
Qed.  


End Multi.

(*This section contains various results about some Haskell functions used, inlcuding List.zip,
  repeat (used in place of List.repeat), and suci*)
Section HaskellFunctions.

(*Replicate is trivially sorted*)
Lemma replicate_sorted: forall c n,
  Sorted Z.le (repeat c (Z.to_nat n)). 
Proof.
  intros. 
  induction (Z.to_nat n); simpl; try(constructor).
  - assumption.
  - apply In_InfA. intros. apply repeat_spec in H. subst. omega. 
Qed. 

(*List.filter equivalence with Coq*)
Lemma filter_equiv: forall {a} (l: list a) p,
  List.filter p l = filter p l.
Proof.
  intros. induction l; simpl. reflexivity. rewrite IHl. reflexivity.
Qed.

(*Tuple.snd quivalence with Coq*)
Lemma snd_equiv: @Tuple.snd = @snd.
Proof.
  unfold Tuple.snd. unfold snd. reflexivity.
Qed.

(*Prove that List.length is equivalent (up to Z -> nat conversion) with Coq list length *)
Lemma len_acc_def: forall {a} (l : list a ) n,
  List.lenAcc l n = (n + Z.of_nat (length l))%Z.
Proof.
  intros. revert n. induction l; intros; simpl.
  - omega.
  - rewrite IHl. rewrite Zpos_P_of_succ_nat. omega.
Qed. 

Lemma length_equiv: forall {a} (l: list a),
  length l = Z.to_nat (List.length l).
Proof.
  intros. induction l; simpl.
  - reflexivity.
  - unfold List.length. simpl. unfold List.length in IHl. rewrite len_acc_def. 
    rewrite len_acc_def in IHl. simpl in IHl.
    rewrite Z2Nat.inj_add. simpl. omega. omega. omega.
Qed.

(*List.zip results*)
Lemma zip_in: forall {a} {b} (l1 : list a) (l2: list b),
  (forall x y, In (x,y) (List.zip l1 l2) -> In x l1 /\ In y l2).
Proof.
  intros. generalize dependent l2. induction l1; intros.
  - simpl in H. destruct H.
  - simpl in H. destruct l2. destruct H.
    simpl in H.  destruct H. inversion H; subst.
    split; simpl; left; reflexivity. simpl. apply IHl1 in H. destruct H.
    split; right; assumption. 
Qed. 

Lemma map_snd_zip: forall {a b} (l1: list a) (l2: list b),
  length l1 = length l2 ->
  map snd (List.zip l1 l2) = l2.
Proof.
  intros. generalize dependent l2. induction l1; intros; simpl.
  - simpl in H. destruct l2; try(reflexivity). simpl in H. omega.
  - simpl in H. destruct l2. simpl in H. omega. simpl in H. inversion H.
    simpl. rewrite IHl1. reflexivity. assumption.
Qed.

Lemma map_fst_zip: forall {a b} (l1: list a) (l2: list b),
  length l1 = length l2 ->
  map fst (List.zip l1 l2) = l1.
Proof.
  intros. generalize dependent l2. induction l1; intros. simpl. reflexivity.
  simpl. destruct l2. simpl in H. omega. simpl in *. inversion H. apply IHl1 in H1. rewrite H1. reflexivity.
Qed.

(*Need specialized lemma for zip with replicate*)
Lemma zip_replicate: forall {a} {b} (l : list a) (m : b) x (n: b) ,
  In (x,n) (List.zip l (repeat m (Z.to_nat (List.length l)))) <-> In x l /\ n = m.
Proof.
  intros. rewrite <- length_equiv. induction l; simpl; split; intros.
  - destruct H.
  - destruct_all. destruct H.
  - destruct H. inversion H; subst. split; try(left); reflexivity.
    apply IHl in H. destruct H. subst. split. right. assumption. reflexivity.
  - destruct H. subst. destruct H. inversion H. left. reflexivity.
    right. apply IHl. split; try(assumption); reflexivity.
Qed.

(*Definition about context4l' (a custom function in Data.Graph*)
Lemma context4l'_def: forall (g: gr a b) v i x l o g' y,
  match_ v g = (Some (i, x, l, o), g') ->
  In y (map snd (context4l' (i, x, l, o))) <-> eIn g v y = true.
Proof.
  intros. unfold context4l'. split; intros.
  - rewrite in_map_iff in H0. destruct H0. destruct x0. simpl in *. destruct H0. subst.
    apply in_app_or in H1. destruct H1. apply match_context in H.
    destruct_all. subst. apply H2. rewrite in_map_iff. exists (b0, y). split; auto.
    unfold Base.op_z2218U__ in H0. unfold Base.op_zeze__ in H0. unfold Base.Eq_Char___ in H0.
    unfold Base.op_zeze____  in H0. rewrite filter_equiv in H0. apply filter_In in H0.
    destruct H0. apply match_context in H. destruct_all. subst. 
    simpl in H1. rewrite N.eqb_eq in H1. subst. apply H2. rewrite in_map_iff. exists (b0, x).
    split. reflexivity. assumption.
  - apply match_context in H. destruct_all. subst.
    apply H2 in H0. rewrite in_map_iff in H0. destruct H0. rewrite in_map_iff. exists x0.
    split. apply H. destruct H. solve_in.
Qed.

(*Characterizing suci, which is the function uesd by BFS*)
Lemma suci_def: forall x y n (c: Context a b) v g g',
  match_ v g = (Some c, g') ->
  In (x,y) (suci c n) <-> y = n /\ eIn g v x = true. 
Proof. 
  intros. split. intros. split. unfold suci in H0. apply zip_in in H0. destruct H0. eapply repeat_spec.
  apply H1. 
  unfold suci in H0. apply zip_in in H0. destruct H0. unfold suc' in H0.
  unfold Base.op_z2218U__ in H0. unfold Base.map in H0. rewrite snd_equiv in H0. 
  destruct c. destruct p. destruct p.
  eapply context4l'_def. apply H. apply H0.
  intros. unfold suci. destruct H0. subst.
  epose proof (zip_replicate (suc' c) n x n). apply H0. split.
  unfold suc'. unfold Base.op_z2218U__. rewrite snd_equiv. unfold Base.map.
  destruct c. destruct p. destruct p. rewrite context4l'_def. apply H1. apply H. reflexivity.
Qed.

End HaskellFunctions.

(*We only need to prove correctness for any valid done state, as explained above.*)
Section Correctness.

Definition distance := (@Path.distance a b gr Hgraph).

(*We use a None distance to represent infinity (as in CLRS).*)
Definition lt_distance (o1: option nat) (o2: option nat) :=
  match o1, o2 with
  | _, None => true
  | None, _ => false
  | Some x, Some y => leb x y
  end.

Definition plus_distance (o1: option nat) (n: nat) :=
  match o1 with
  | None => None
  | Some x => Some (x + n)
  end.

(*Lemma 22.1 of CLRS: if (u,v) in E, then v.d <= u.d + 1 (distance from s)*)
Lemma distance_triangle: forall g s u v,
  eIn g u v = true ->
  vIn g s = true ->
  lt_distance (distance g s v) (plus_distance (distance g s u) 1) = true.
Proof.
  intros. destruct (path_dec g s u).
  - destruct e as [l]. apply shortest_path_exists in H1. clear l. destruct H1 as [l]. 
    assert (path' g s v (v ::  l)). { eapply p_multi. apply H1. assumption. }
    destruct (distance g s v) eqn : D.
    + destruct (distance g s u) eqn : D'.
      * simpl. rewrite Nat.leb_le.
        assert (length l = n0). eapply shortest_path_distance. apply D'. assumption. subst.
        apply distance_some in D. destruct_all. subst.
        unfold shortest_path in H3. destruct_all.
        assert (forall n m, n <= m \/ m < n) by (intros; omega).
        specialize (H5 (length x) (length l + 1)). destruct H5. assumption.
        assert (length l + 1 = length (v :: l)). simpl. omega.
        rewrite H6 in H5. apply H4 in H5. contradiction.
      * unfold distance in D'. rewrite distance_none in D'. unfold shortest_path in H1. destruct_all.
        exfalso. apply (D' l). assumption.
    + unfold distance in D. rewrite distance_none in D. unfold shortest_path in H1. destruct_all.
      exfalso. apply (D (v :: l)). assumption.
  - destruct (distance g s u) eqn : D.
    + apply distance_some in D. destruct_all. unfold shortest_path in H1. destruct_all. exfalso.
      apply n. exists x. assumption.
    + simpl. destruct (distance g s v); reflexivity.
Qed.

(*Any vertex or edge in the graph at any point during BFS was in the original graph*)
Lemma graph_subset: forall s v g,
  valid s g v ->
  (forall v, vIn (get_graph s) v = true -> vIn g v = true) /\
  (forall u v, eIn (get_graph s) u v = true -> eIn g u v = true).
Proof.
  intros. induction H; simpl.
  - split; intros; assumption.
  - inversion H0; subst; simpl in *. assert (M:=H2). apply match_remain_some in H2.
    destruct H2. split. intros. rewrite H2 in H4. apply IHvalid. apply H4.
    intros. rewrite H3 in H4. apply IHvalid. apply H4. apply match_remain_none in H2.
    subst. apply IHvalid.
Qed.

(*A vertex that is in the original graph is in the graph in a given state iff
  it is not already finished*)
Lemma graph_iff_not_output: forall s g v v',
  valid s g v ->
  vIn g v' = true ->
  In v' (map fst (get_dists s)) <-> (vIn (get_graph s) v' = false).
Proof.
  intros. induction H; split; intros; simpl in *.
  - destruct H1.
  - rewrite H1 in H0. inversion H0.
  - inversion H1; subst; simpl in *.
    + rewrite map_app in H2. apply in_app_or in H2.
      destruct H2. assert (vIn g0 v' = false). apply IHvalid.
      assumption. assumption. apply match_remain_some in H4.
      destruct H4. specialize (H4 v'). destruct H4. apply contrapositive in H4.
      destruct (vIn g' v'). contradiction. reflexivity. intro. 
      destruct H8. rewrite H8 in H5. inversion H5.
      simpl in H2. destruct H2. subst. apply match_remain_some in H4.
      destruct H4. specialize (H2 v'). destruct H2. apply contrapositive in H2.
      destruct (vIn g' v'). contradiction. reflexivity. intro. destruct H6. contradiction.
      destruct H2.
    + apply match_remain_none in H4. subst. apply IHvalid. assumption. assumption.
  - inversion H1; subst; simpl in *.
    + destruct (N.eq_dec v' v0). subst.
      rewrite map_app. apply in_or_app. right. simpl. left. reflexivity.
      apply match_remain_some in H4. destruct H4. specialize (H4 v').
      destruct H4. apply contrapositive in H6. destruct (vIn g0 v') eqn : V.
      exfalso. apply H6. split. reflexivity. assumption. rewrite map_app.
      apply in_or_app. left. rewrite IHvalid. reflexivity. assumption. 
      destruct (vIn g' v'). inversion H2. auto.
    + apply IHvalid. assumption. apply match_remain_none in H4. subst. assumption.
Qed.

(*Every vertex in the queue is in the graph*)
Lemma queue_in_graph: forall s v g v',
  valid s g v ->
  In v' (map fst (get_queue s)) -> 
  vIn g v' = true.
Proof.
  intros. induction H.
  - unfold start in *. simpl in *. destruct H0. subst. assumption. destruct H0.
  - inversion H1; subst; simpl in *.
    + rewrite map_app in H0. apply in_app_or in H0. destruct H0.
      apply IHvalid. right. assumption. rewrite in_map_iff in H0.
      destruct H0. destruct x. destruct H0; subst. apply (suci_def n i (j + 1)%Z) in H3.
      rewrite H3 in H4. destruct H4. subst. simpl. 
      apply edges_valid in H4. destruct H4.
      pose proof (graph_subset _ _ _ H). destruct H5. apply H5. simpl. assumption.
    + apply IHvalid. right. assumption.
Qed.

(*Each vertex appears at most once in the output*)
Lemma no_dups_output: forall s g v,
  valid s g v ->
  NoDup (map fst (get_dists s)).
Proof.
  intros. induction H; simpl.
  - constructor.
  - inversion H0; subst; simpl in *.
    rewrite map_app. simpl. assert (map fst d ++ v0 :: nil = rev (v0 :: rev ((map fst d)))).
    simpl. rewrite rev_involutive. reflexivity.
    rewrite H3. rewrite NoDup_NoDupA. apply NoDupA_rev. apply eq_equivalence.
    constructor. intro. rewrite <- In_InA_equiv in H4. rewrite <- in_rev in H4.
    assert (vIn g v0 = true). eapply queue_in_graph. apply H. simpl. left. reflexivity. 
    pose proof (graph_iff_not_output _ _ _ _ H H5) as D; simpl in *.
    apply D in H4. 
    assert (vIn g0 v0 = true). apply match_in. exists c. exists g'. assumption.
    rewrite H6 in H4. inversion H4. apply NoDupA_rev. apply eq_equivalence. rewrite <- NoDup_NoDupA.
    assumption. assumption.
Qed.

(*Every distance on the queue is >= 0*)
Lemma dist_geq_0: forall s g v v' d,
  valid s g v ->
  In (v', d) (get_queue s) ->
  (d >= 0)%Z.
Proof.
  intros. generalize dependent v'. generalize dependent d. induction H; intros.
  - unfold start in H0; simpl in *. destruct H0. inversion H0; subst. omega. destruct H0.
  - inversion H0; subst; simpl in *.
    +  apply in_app_or in H1. destruct H1. eapply IHvalid. right. apply H1.
      eapply (suci_def _ _ _ _ _ _ _ H3) in H1. destruct H1. 
       assert ((j >=0)%Z). eapply IHvalid. left. reflexivity. omega.
     + eapply IHvalid. right. apply H1.
Qed. 

(*Likewise for the output*)
Lemma dists_geq_0: forall s g v v' d,
  valid s g v ->
  In (v', d) (get_dists s) ->
  (0 <= d)%Z.
Proof.
  intros. induction H.
  - unfold start in *. simpl in *. destruct H0.
  - inversion H1; subst; simpl in *.
    + apply in_app_or in H0. destruct H0. apply IHvalid; assumption. simpl in H0. destruct H0.
      inversion H0; subst.
      pose proof (dist_geq_0 (g0, (v', d) :: vs, d0) g v v' d H). simpl in H4.
      assert (d >= 0)%Z. apply H4. left. reflexivity. omega. destruct H0.
    + apply IHvalid; assumption.
Qed.

Lemma valid_in: forall s g v,
  valid s g v ->
  vIn g v = true.
Proof.
  intros. induction H. assumption. assumption.
Qed.

(** ** Lemma 22.2 of CLRS **)

(*TODO (or something): The BFS implementation does not count the first vertex, so we have that
  [distance u v] (length of shortest path) = 1 + (computed distance)*)

(*First, the necessary statement for queues: if (v', d) is in the queue, then d(v') <= d + 1*)
Lemma queue_upper_bound: forall s g v v' d,
  valid s g v ->
  In (v', d) (get_queue s) ->
  lt_distance (distance g v v')  (Some ((Z.to_nat d) + 1)) = true.
Proof.
  intros. generalize dependent v'. generalize dependent d. induction H; intros.
  - unfold start in *; simpl in *. destruct H0. inversion H0; subst.
    simpl. assert (distance g v' v' = Some 1). apply distance_refl in H.
    apply distance_of_shortest_path in H. simpl in H. assumption.
    rewrite H1. reflexivity. destruct H0.
  - inversion H0; subst; simpl in *.
    + apply in_app_or in H1. destruct H1.
      * apply IHvalid. right. assumption.
      * apply (suci_def _ _ _ _ _ _ _ H3) in H1. destruct H1. subst.
        pose proof (valid_in (g0, (v0, j) :: vs, d0) g v H). simpl in H1.
        pose proof (graph_subset (g0, (v0, j) :: vs, d0) v g H). simpl in H5.
        destruct H5. apply H6 in H4. 
        pose proof (distance_triangle _ _ _ _ H4 H1).
        assert (lt_distance (distance g v v0) (Some (Z.to_nat j + 1)) = true). apply IHvalid. left.
        reflexivity. destruct (distance g v v0) eqn : ?; simpl in *.
        destruct (distance g v v') eqn : ?. simpl in *. rewrite Nat.leb_le in *.
        assert ((j >= 0)%Z). eapply dist_geq_0. apply H. simpl. left. reflexivity.
        assert (Z.to_nat j + 1 = Z.to_nat (j + 1)). assert (Z.to_nat j + Z.to_nat (1%Z) = Z.to_nat (j + 1)).
        rewrite <- Z2Nat.inj_add. reflexivity. omega. omega. 
        assert (Z.to_nat 1 = 1). unfold Z.to_nat. unfold Pos.to_nat. simpl. reflexivity.
        rewrite H11 in H10. omega. omega. simpl. simpl in H7. inversion H7.
        inversion H8.
    + apply IHvalid. right. assumption.
Qed. 

(*Lemma 22.2 of CLRS*)
Lemma dist_upper_bound: forall s g v v' d,
  valid s g v ->
  In (v', d) (get_dists s) ->
  lt_distance (distance g v v') (Some (Z.to_nat d + 1))  = true.
Proof.
  intros. induction H; simpl.
  - unfold start in H0; simpl in H0. destruct H0.
  - inversion H1; subst; simpl in *.
    + apply in_app_or in H0. destruct H0. specialize (IHvalid H0).
      apply IHvalid. simpl in H0. destruct H0. inversion H0; subst.
      pose proof (queue_upper_bound _ _ _ v' d H). simpl in H4.
      unfold lt_distance in H4. apply H4. left. reflexivity. destruct H0.
    + apply IHvalid. assumption.
Qed.

(** Lemma 22.3 of CLRS **)
(*I believe we only ever use the first part (sortedness of the queue), but the second is necessary for the IH*)
Lemma queue_structure: forall s g v v' d tl,
  valid s g v ->
  get_queue s = (v', d) :: tl ->
  (Sorted Z.le (map snd (get_queue s))) /\ (forall v' d', In (v', d') (get_queue s) -> (d' <= d + 1)%Z).
Proof.
  intros. generalize dependent v'. revert d. revert tl. induction H; intros; simpl.
  - unfold start; simpl in *. inversion H0; subst. split. constructor. constructor. constructor.
    intros. destruct H1. inversion H1. subst. omega. destruct H1.
  - inversion H0; subst; simpl in *.
    + split. rewrite map_app. eapply SortA_app. apply eq_equivalence.
      assert (Sorted Z.le (j :: map snd vs)). { specialize (IHvalid vs j v0).
      apply IHvalid. reflexivity. } inversion H4; subst. assumption.
      unfold suci. rewrite map_snd_zip.  apply replicate_sorted.
      rewrite repeat_length. apply length_equiv.
      intros.
      unfold suci in H5. rewrite map_snd_zip in H5. 
      rewrite <- In_InA_equiv in H5. apply repeat_spec in H5.  subst.
      rewrite <- In_InA_equiv in H4. rewrite in_map_iff in H4.
      destruct H4. destruct H4. destruct x0; subst.
      simpl. specialize (IHvalid vs j v0). destruct IHvalid. reflexivity.
      specialize (H6 n i). apply H6. right. assumption.
      rewrite repeat_length. apply length_equiv.
      intros. apply in_app_or in H4.
      (*d is in vs or suci *)
      destruct vs. simpl in H1. destruct H4. simpl in H4. destruct H4.
      unfold suci in H4. apply zip_in in H4. destruct H4.
      apply repeat_spec in H5. subst.
      assert (In (v', d) (suci c (j+1)%Z)). rewrite H1. solve_in.
      unfold suci in H5. apply zip_in in H5. destruct H5.
      apply repeat_spec in H6. subst. omega.
      (*other case*)
      simpl in H1. inversion H1. subst.
      specialize (IHvalid ((v', d) :: vs) j v0). destruct IHvalid.
      reflexivity. inversion H5. subst.
      inversion H10. subst. 
      destruct H4.
      simpl in H4. destruct H4. inversion H4. subst. omega.
      assert (d' <= j + 1)%Z. eapply H6. right. right. apply H4.
      omega.
      unfold suci in H4. apply zip_in in H4. destruct H4.
      apply repeat_spec in H7. subst. omega.
    + specialize (IHvalid vs j v0). destruct IHvalid. reflexivity.
      split. inversion H4. assumption. intros. rewrite H1 in H6.
      destruct H6. inversion H6; subst. omega.
      inversion H4; subst. inversion H10; subst.
      assert (d' <= j + 1)%Z. eapply H5. right. right. apply H6. omega.
Qed. 

(** Reachability **)

(*First, everything on the queue is reachable fron v*)
Lemma queue_reachable: forall s g v v',
  valid s g v ->
  In v' (map fst (get_queue s)) ->
  exists l, path' g v v' l.
Proof.
  intros. generalize dependent v'. induction H; intros; subst.
  - unfold start in *; simpl in *. destruct H0. subst. exists (v' :: nil). constructor. assumption. destruct H0.
  - inversion H0; subst; simpl in *.
    + rewrite map_app in H1. apply in_app_or in H1. destruct H1.
      apply IHvalid. right. assumption. rewrite in_map_iff in H1.
      destruct H1. destruct x. simpl in H1. destruct H1; subst.
      apply (suci_def _ _ _ _ _  _ _ H3) in H4. destruct H4; subst.
      specialize (IHvalid v0). destruct IHvalid. left. reflexivity. subst.
      exists (v' :: x). econstructor. apply H1. pose proof (graph_subset _ _ _ H).
      destruct H5. apply H6. simpl. assumption.
    + apply IHvalid. right. assumption.
Qed. 

(*Thus, everything in the output is reachable from v*)
Theorem output_is_reachable: forall s g v v',
  valid s g v ->
  In v' (map fst (get_dists s)) ->
  exists l, path' g v v' l.
Proof.
  intros. induction H; subst.
  - unfold start in *; simpl in *. destruct H0.
  - inversion H1; subst; simpl in *.
    + rewrite map_app in H0. apply in_app_or in H0. destruct H0.
      apply IHvalid. assumption. eapply queue_reachable. apply H. simpl.
      simpl in H0. destruct H0; subst. left. reflexivity. destruct H0.
    + apply IHvalid. assumption.
Qed. 

(*Now the harder side: everything that is reachable is in the output*)

(*Everything in the output at one state is there in all future states*)
Lemma output_preserved_strong: forall s v g v' s' (d : Num.Int),
  valid s g v ->
  bfs_multi s s' ->
  In (v' d) (get_dists s) ->
  In (v' d) (get_dists s').
Proof.
  intros. induction H0. assumption. assert (valid y g v). eapply v_step. apply H. assumption.
  specialize (IHmulti H3). clear H3. inversion H0; subst; simpl in *; apply IHmulti; solve_in.
Qed.

Lemma output_preserved: forall s v g v' s',
  valid s g v ->
  bfs_multi s s' ->
  In v' (map fst (get_dists s)) ->
  In v' (map fst (get_dists s')).
Proof.
  intros. rewrite in_map_iff in *. destruct H1. exists x. destruct H1.
  split. assumption. destruct x; simpl. subst. eapply output_preserved_strong.
  apply H. apply H0. assumption.
Qed.

(*A stronger version of [graph_subset]: if a vertex or edge is in the graph at a later point,
  then it was in the graph in an earlier state that steps to the current state *)
Lemma graph_subset': forall s v g s',
  valid s g v ->
  bfs_multi s s' ->
  (forall v, vIn (get_graph s') v = true -> vIn (get_graph s) v = true) /\
  (forall u v, eIn (get_graph s') u v = true -> eIn (get_graph s) u v = true).
Proof.
  intros. induction H0; simpl.
  - split; intros; assumption.
  - assert (valid y g v). eapply v_step. apply H. assumption.
    specialize (IHmulti H2). clear H2. inversion H0; subst; simpl in *.
    assert (M:=H3). apply match_remain_some in H3.
    destruct H3. split. intros. destruct IHmulti. apply H6 in H5.
    rewrite H3 in H5. destruct H5. assumption.
    intros. destruct IHmulti. apply H7 in H5.
    rewrite H4 in H5. destruct H5. assumption. apply match_remain_none in H3. subst. apply IHmulti.
Qed.

(*Everything in the queue at one point that is not in the queue at a future point must be in the output*)
Lemma queue_added_to_output: forall s v g v' s',
  valid s g v ->
  bfs_multi s s' ->
  In v' (map fst (get_queue s)) ->
  ~In v' (map fst (get_queue s')) ->
  In v' (map fst (get_dists s')).
Proof.
  intros. induction H0.
  - contradiction.
  - inversion H0; subst; simpl in *.
    + destruct H1. subst. eapply output_preserved.
      eapply v_step. apply H. apply H0. assumption. simpl. rewrite map_app.
      apply in_or_app. right. simpl. left. reflexivity.
      apply IHmulti. eapply v_step. apply H. assumption.
      rewrite map_app. apply in_or_app. left. apply H1. assumption.
    + destruct H1. subst. rewrite graph_iff_not_output. pose proof (graph_subset' _ _ _ z H).
      destruct H1. eapply multi_step. apply H0. assumption. simpl in *. 
      specialize (H1 v'). apply contrapositive in H1. destruct (vIn (get_graph z) v').
      contradiction. reflexivity. 
      destruct (vIn g0 v') eqn : M. rewrite <- match_in in M.
      destruct M. destruct H7. rewrite H7 in H5. inversion H5. auto. 
      eapply multi_valid. apply H. eapply multi_step. apply H0. assumption.
      eapply queue_in_graph. apply H. simpl. left. reflexivity. 
      apply IHmulti. eapply v_step. apply H. assumption. assumption. assumption.
Qed.
     
(*An important lemma: If a vertex is on the queue at any point, when we multistep to the end, it is in
  the list of distances*)
Lemma queue_ends_in_output: forall s v g s' v',
  valid s g v ->
  bfs_multi s s' ->
  done s' = true ->
  In v' (map fst (get_queue s)) ->
  In v' (map fst (get_dists s')).
Proof.
  intros. unfold done in H1. rewrite orb_true_iff in H1.
  destruct H1. destruct (get_queue s') eqn : E. 
  eapply queue_added_to_output. apply H. assumption. assumption. rewrite E. simpl. auto.
  simpl in H1. inversion H1. rewrite graph_iff_not_output. 
  rewrite isEmpty_def in H1. apply H1. apply v'. 
  eapply multi_valid. apply H. assumption. eapply queue_in_graph. apply H. assumption.
Qed.

(*If a vertex is in the distances at any point, there must be a step when it was added to the distances. The rest
  of the lemma gives a bunch of information about that state and the queue/distances*)
Lemma output_is_added: forall s v g v' d,
  valid s g v ->
  In (v', d) (get_dists s) ->
  (exists s' c g', valid s' g v /\ bfs_multi s' s  /\ (exists l1,
    get_queue s' = l1 ++ suci c (Num.op_zp__ d (Num.fromInteger 1)) /\ (forall s'', valid s'' g v ->
     bfs_step s'' s' ->
    ~In v' (map fst (get_dists s'')) /\ (match_ v' (get_graph s'') = (Some c, g')) /\ 
      get_queue s'' = (v', d) :: l1)) /\ s' <> start g v /\ (exists l2, get_dists s' = l2 ++ (v', d) :: nil) ).
Proof.
  intros. induction H.
  - unfold start in H0. simpl in *. destruct H0.
  - inversion H1; subst; simpl in *.
    + assert (~In v0 (map fst d0)). assert (valid ( (g', vs ++ suci c (j + 1)%Z, d0 ++ (v0, j) :: nil)) g v).
      eapply v_step. apply H. assumption. apply no_dups_output in H4. simpl in H4. rewrite NoDup_NoDupA in H4.
      rewrite map_app in H4. simpl in H4. apply NoDupA_swap in H4. inversion H4; subst.
      intro. rewrite In_InA_equiv in H5. rewrite app_nil_r in H7. contradiction.
      apply eq_equivalence. destruct (N.eq_dec v' v0). subst. apply in_app_or in H0. destruct H0.
      rewrite in_map_iff in H4. exfalso. apply H4. exists (v0, d). split; simpl. reflexivity. assumption.
      simpl in H0. destruct H0. inversion H0; subst. 
      exists (g', vs ++ suci c (d + 1)%Z, d0 ++ (v0, d) :: nil). exists c. exists g'.
      split. eapply v_step. apply H. assumption.
      split. apply multi_refl.
      split. exists vs. split. reflexivity. intros.
      assert (s'' = (g0, (v0, d) :: vs, d0)). eapply valid_determ. apply H5.
      assumption. apply H6. assumption. subst. simpl in *. split. assumption. split.  assumption.
      reflexivity. split.
      unfold start. simpl. intro. inversion H5; subst. destruct d0; inversion H9.
      exists d0. simpl. reflexivity.
      destruct H0. apply in_app_or in H0. destruct H0.
      apply IHvalid in H0. clear IHvalid. destruct H0 as [s']. destruct H0 as [c'].
      destruct H0 as [g'']. destruct_all. exists s'. exists c'. exists g''. split.
      assumption. split. eapply multi_trans. apply H5. apply multi_R. assumption.
      split. exists x. split. assumption. split. apply H9. assumption. assumption. apply H9.
      assumption. assumption. split. apply H7. exists x0. assumption.
      destruct H0. inversion H0; subst.
      contradiction. destruct H0.
    + apply IHvalid in H0. clear IHvalid. destruct H0 as [s']. destruct H0 as [c'].
      destruct H0 as [g'']. destruct_all. exists s'. exists c'. exists g''.
      repeat(split; try(assumption)). eapply multi_trans. apply H4. apply multi_R. assumption.
      exists x. split. assumption. apply H8. exists x0. assumption.
Qed.

(*Last lemma before reachability - an edge is in the graph in a given state exactly when both ot its
  vertices are in the graph*)
Lemma edge_in_state: forall s g v u' v',
  valid s g v ->  
  eIn g u' v' = true ->
  eIn (get_graph s) u' v' = true <-> (vIn (get_graph s) u' = true /\ vIn (get_graph s) v' = true).
Proof.
  intros. induction H.
  - unfold start; simpl. split; intros.
    + apply edges_valid. assumption.
    + assumption.
  - specialize (IHvalid H0). inversion H1; subst; simpl in *.
    + split; intros.
      * apply edges_valid. assumption.
      * destruct H4. apply match_remain_some in H3. destruct H3. apply H3 in H4.
        apply H3 in H5. rewrite H6. split. rewrite IHvalid. destruct_all. split; assumption.
        destruct_all; split; assumption.
    + apply match_remain_none in H3. subst. apply IHvalid.
Qed.

(*First, prove everything reachable is in queue at some point*)
Lemma reachable_in_queue: forall g v v',
  (exists l, path' g v v' l) ->
  (exists s, valid s g v /\ In v' (map fst (get_queue s))).
Proof.
  intros. destruct H as [l]. generalize dependent v'.
  induction l using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
  intros. inversion H0; subst.
  - exists (start g v'). split. constructor. assumption. simpl. left. reflexivity. 
  - rename v'0 into n. 
    assert (exists s : state, valid s g v /\ In n (map fst (get_queue s))). eapply H.
    assert (length l0 < S(length l0)) by omega. simpl. apply H3. assumption.
    destruct H3 as [s]. destruct H3. 
    assert (exists sd, done sd = true /\ bfs_multi s sd). exists (bfs_tail s).
    split. apply bfs_tail_done. apply bfs_tail_multi. destruct H5 as [sd]. destruct H5.
    pose proof (queue_ends_in_output _ _ _ _ _ H3 H6 H5 H4).
    assert (valid sd g v). eapply multi_valid. apply H3. assumption.
    rewrite in_map_iff in H7. destruct H7. destruct x as [n' d]. simpl in H7. destruct H7; subst.
    pose proof (output_is_added _ _ _ _ _ H8 H9). destruct H7 as [sp]. destruct H7 as [c].
    destruct H7 as [g']. destruct H7. destruct H10. destruct H11. destruct H11 as [l1].
    (*need prior state*)
    destruct H12. destruct H13. pose proof (prior_state _ _ _ H7 H12). destruct H14 as [sb]. destruct H14.
    pose proof (edge_in_state _ _ _ _ _ H14 H2). destruct H11 as [A H11].
    specialize (H11 _ H14 H15). destruct H11. destruct H17. destruct (vIn (get_graph sb) v') eqn : M.
    + assert (vIn (get_graph sb) n = true). erewrite <- match_in. exists c. exists g'. assumption.
      rewrite H19 in H16. assert (eIn (get_graph sb) n v' = true). rewrite H16. split; reflexivity.
      exists sp. split; try(assumption). rewrite A.  rewrite map_app. apply in_or_app. right.
      pose proof (suci_def v' (Num.op_zp__ d (Num.fromInteger 1)) (Num.op_zp__ d (Num.fromInteger 1))
      c n (get_graph sb) g' H17). simpl in H21. destruct H21.
      rewrite H20 in H21. rewrite in_map_iff. exists (v', (d+1)%Z). split. reflexivity.
      simpl. apply H22. rewrite H20. split; reflexivity.
    + rewrite <- graph_iff_not_output in M. rewrite in_map_iff in M. destruct M. destruct x0. simpl in H19; destruct H19; subst.
      pose proof (output_is_added _ _ _ _ _ H14 H20). destruct_all.
      pose proof (prior_state _ _ _ H19 H23). destruct H26. exists x5. destruct H26. 
      specialize (H25 _ H26 H27). destruct_all. split. assumption. rewrite H29. simpl.
      left. reflexivity. apply H14. apply edges_valid in H2. destruct H2; assumption.
Qed.

(*Now, everything reachable is in the ouptut*)
Lemma reachable_in_output: forall g v v' s,
  valid s g v ->
  done s = true ->
  (exists l, path' g v v' l) ->
  In v' (map fst (get_dists s)).
Proof.
  intros. eapply reachable_in_queue in H1. destruct H1 as [s']. destruct H1.
  eapply queue_ends_in_output. apply H1. destruct (done s') eqn : D.
  assert (s = s'). eapply done_unique. apply H. apply H1. assumption. assumption.
  subst. apply multi_refl. eapply multi_done. apply H1. apply H. assumption. assumption.
  assumption. assumption.
Qed.
(*
(*The start vertex is in the output*)
Lemma v_in_output: forall s g v,
  valid s g v ->
  s = start g v \/ In v (map fst (get_dists s)).
Proof.
  intros. induction H.
  - left. reflexivity.
  - inversion H0; subst; simpl in *.
    + right. destruct (N.eq_dec v v0). subst.
      rewrite map_app. simpl. solve_in.
      unfold start in IHvalid. simpl in IHvalid.
      rewrite map_app. destruct IHvalid. inversion H3; subst. contradiction.
      solve_in.
    + destruct IHvalid. unfold start in H3. inversion H3. subst.
      assert (vIn g v = false). destruct (vIn g v) eqn : V.
      rewrite <- match_in in V. destruct_all. rewrite H4 in H2. inversion H2. reflexivity.
      assert (vIn g v = true). eapply valid_in. apply H. rewrite H5 in H4. inversion H4.
      right. assumption.
Qed.
*)
(** Proof the BFS finds all reachable vertices and only reachable vertices **)
Theorem output_iff_reachable: forall s g v v',
  valid s g v ->
  done s = true ->
  In v' (map fst (get_dists s)) <-> exists l, path' g v v' l.
Proof.
  intros. split; intros.
  - eapply output_is_reachable. apply H. apply H1.
  - eapply reachable_in_output. apply H. assumption. assumption.
Qed.

(** Correctness of BFS **)

(*Now we will prove that every (v',d) pair in the output has the property that (d'+1) is the distance from v
  to v'. This requires several lemmas first.*)

(*Find distance from state*)
Definition find_dist_list l v :=
  fold_right (fun x acc => if N.eq_dec (fst x) v then Some (Z.to_nat (snd x)) else acc) None l.

Definition find_dist s := find_dist_list (get_dists s).

Lemma find_dist_in: forall s g v v' n,
  valid s g v ->
  find_dist s v' = Some n <-> In (v',(Z.of_nat n)) (get_dists s).
Proof.
  intros. pose proof no_dups_output _ _ _ H. unfold find_dist.
  assert (forall l, NoDup (map fst l) ->
   (forall n, In n (map snd l) -> (0 <= n)%Z) ->
   fold_right (fun (x : N * Z) (acc : option nat) => if N.eq_dec (fst x) v' then Some (Z.to_nat (snd x)) else acc)
  None l = Some n <-> In (v', Z.of_nat n) l). { intros; induction l; split; intros; simpl in *.
  - inversion H3.
  - destruct H3.
  - destruct a0. simpl in *. destruct (N.eq_dec n0 v') eqn : ?. subst. inversion H3; subst.
    left. rewrite Z2Nat.id. reflexivity. apply H2. left. reflexivity. 
    right. apply IHl. inversion H1; assumption. intros. apply H2. right. assumption. assumption.
  - destruct a0; simpl in *. destruct H3. inversion H3; subst. destruct (N.eq_dec v' v').
    rewrite Nat2Z.id. reflexivity. contradiction. destruct (N.eq_dec n0 v'). subst.
    inversion H1. subst. assert (In v' (map fst l)). rewrite in_map_iff. exists (v', Z.of_nat n).
    split; try(reflexivity); assumption. contradiction. rewrite IHl. assumption. inversion H1; assumption.
    intros. apply H2. right. assumption. } apply H1.
    assumption. intros. rewrite in_map_iff in H2. destruct H2.
    destruct x. destruct H2. simpl in H2; subst. eapply dists_geq_0. apply H.  apply H3.
Qed.

Lemma find_dist_not: forall s v,
  find_dist s v = None <-> (forall y, ~In (v, y) (get_dists s)).
Proof.
  intros. unfold find_dist. assert (forall l, 
  fold_right (fun (x : N * Z) (acc : option nat) => if N.eq_dec (fst x) v then Some (Z.to_nat (snd x)) else acc) None
  l = None <-> (forall y : Num.Int, ~ In (v, y) l)). { intros.
  induction l; split; intros; simpl in *.
  - auto.
  - reflexivity.
  - destruct a0. simpl in *. destruct (N.eq_dec n v). inversion H.
    intro. rewrite IHl in H. destruct H0. inversion H0; subst. contradiction.
    apply (H y); assumption.
  - destruct a0. simpl. destruct (N.eq_dec n v). subst. exfalso. apply (H z).
    left. reflexivity. rewrite IHl. intros. intro. apply (H y). right. assumption. }
    apply H.
Qed.

(*The start vertex appears with distance 0 in the output*)
Lemma second_state: forall s g v,
  vIn g v = true ->
  bfs_step (start g v) s ->
  get_dists s = (v, 0%Z) :: nil.
Proof.
  intros. unfold start in H0. inversion H0; subst; simpl. reflexivity.
  rewrite <- match_in in H. destruct H. destruct H. rewrite H in H8. inversion H8.
Qed.

Lemma dists_nil_iff_start: forall s g v,
  valid s g v ->
  get_dists s = nil <-> s = start g v.
Proof.
  intros. induction H.
  - split; intros; try(reflexivity).
  - split; intros.
    + inversion H0; subst; simpl in *.
      * destruct d; inversion H1.
      * subst. unfold start in IHvalid. destruct IHvalid.
        specialize (H1 eq_refl). inversion H1; subst.
        pose proof (valid_in _ _ _ H). rewrite <- match_in in H5.
        destruct_all. rewrite H5 in H3. inversion H3.
    + subst. inversion H0; subst; simpl in *.
      * destruct d; inversion H5.
      * unfold start in IHvalid. destruct IHvalid. 
        specialize (H1 eq_refl). inversion H1; subst.
Qed.

Lemma multi_from_second: forall s g v s',
  valid s g v  ->
  bfs_step (start g v) s' ->
  s = start g v \/ bfs_multi s' s.
Proof.
  intros. induction H.
  - left. reflexivity.
  - specialize (IHvalid H0). destruct IHvalid. subst.
    assert (s = s'). eapply bfs_step_deterministic. apply H1. apply H0. subst.
    right. apply multi_refl. right. eapply multi_trans. apply H2. eapply multi_step.
    apply H1. apply multi_refl.
Qed. 

Lemma start_0_dist: forall s g v,
  valid s g v ->
  (get_dists s) <> nil ->
  In (v, 0%Z) (get_dists s).
Proof.
  intros. assert (exists s', bfs_step (start g v) s').
  assert (vIn g v = true) by (eapply valid_in; apply H).
  pose proof (done_not_start g v H1). rewrite not_done_step in H2.
  apply H2. apply v_start. apply H1. destruct H1 as [s'].
  pose proof (multi_from_second _ _ _ _ H H1). destruct H2. subst.
  rewrite dists_nil_iff_start in H0. contradiction. apply H. 
  eapply output_preserved_strong. eapply v_step. apply v_start.
  apply valid_in in H. apply H. apply H1. assumption.
  erewrite second_state. simpl. left. reflexivity. 
  apply valid_in in H. apply H. apply H1.
Qed.

(*A key characterization of distances: If (v', d) is the first instance of v' on the queue and v' has not
  yet been discovered, when we step, either (v', d) is in the output, or the same condition holds*)
Lemma first_queue_constant: forall s g v v' d' l1 l2 s',
  valid s g v ->
  get_queue s = l1 ++ (v', d') :: l2 ->
  (forall x, In x (map fst l1) -> x <> v') ->
  ~In v' (map fst (get_dists s)) ->
  bfs_step s s' ->
  (In (v', d') (get_dists s') \/ 
  (~In v' (map fst (get_dists s')) /\
  exists l1 l2, get_queue s' = l1 ++ (v', d') :: l2  /\
  (forall x, In x (map fst l1) -> x <> v'))).
Proof.
  intros. inversion H3; subst; simpl in *.
  - destruct (N.eq_dec v0 v'). subst. left.
    destruct l1. simpl in H0. inversion H0. subst. solve_in.
    simpl in H0. inversion H0; subst. 
    specialize (H1 v'). simpl in H1. 
    assert (v' <> v') by (apply H1; left; reflexivity); contradiction.
    destruct l1. simpl in H0. inversion H0; subst. contradiction.
    destruct p. inversion H0; subst. right. split. intro.
    rewrite map_app in H6. apply in_app_or in H6. destruct H6. contradiction.
    simpl in H6. destruct H6; subst. contradiction. destruct H6.
    exists l1. exists (l2 ++ suci c (i + 1)%Z). split. rewrite <- app_assoc.
    simpl. reflexivity. intros. apply H1. simpl. right. assumption.
  - assert (vIn g0 v' = true). destruct (vIn g0 v') eqn : E. reflexivity.
     replace g0 with (get_graph (g0, (v0, j) :: vs, d)) in E by reflexivity.
    rewrite <- graph_iff_not_output in E. simpl in E. contradiction.
    apply H. 
    eapply queue_in_graph. apply H. rewrite H0. simpl.
    rewrite map_app. apply in_or_app. right. simpl. left. reflexivity.
    right. split. assumption. destruct l1. simpl in H0. inversion H0; subst.
    rewrite <- match_in in H6. destruct_all. rewrite H6 in H5. inversion H5.
    inversion H0; subst. exists l1. exists l2. split. reflexivity. intros. apply H1.
    simpl. right. assumption.
Qed.

(*Multistep version of the above*)
Lemma first_queue_contant_multi: forall s g v v' d' l1 l2 s',
  valid s g v ->
  get_queue s = l1 ++ (v', d') :: l2 ->
  (forall x, In x (map fst l1) -> x <> v') ->
  ~In v' (map fst (get_dists s)) ->
  bfs_multi s s' ->
  (In (v', d') (get_dists s') \/ 
  (~In v' (map fst (get_dists s')) /\
  exists l1 l2, get_queue s' = l1 ++ (v', d') :: l2  /\
  (forall x, In x (map fst l1) -> x <> v'))).
Proof.
  intros. generalize dependent l1. revert l2. induction H3; intros.
  - right. split; try(assumption). exists l1. exists l2. split; try(assumption).
  - pose proof (first_queue_constant _ _ _ _ _ _ _ _ H H1 H4 H2 H0). destruct H5.
    left. eapply output_preserved_strong. eapply v_step. apply H. apply H0.
    assumption. apply H5. destruct_all. assert (valid y g v). eapply v_step.
    apply H. assumption. specialize (IHmulti H8 H5 _ _ H6 H7). apply IHmulti.
Qed.

(*Now we know that if (v', d') is the first instance of v' on the queue at some point, v', g') is in
  the distances when we finish (since the other condition cannot happen)*)
Lemma first_queue_in_dists: forall s g v v' d' l1 l2 s',
  valid s g v ->
  valid s' g v ->
  get_queue s = l1 ++ (v', d') :: l2 ->
  (forall x, In x (map fst l1) -> x <> v') ->
  ~In v' (map fst (get_dists s)) ->
  done s' = true ->
  In (v', d') (get_dists s').
Proof.
  intros. destruct (done s) eqn : D.
  - assert (s = s'). eapply done_unique. apply H. 
    assumption. assumption. assumption. subst.
    unfold done in D. rewrite H1 in D. rewrite orb_true_iff in D.
    destruct D. destruct l1; simpl in H5; inversion H5.
    rewrite isEmpty_def in H5. 
    assert (vIn (get_graph s') v' = true). destruct (vIn (get_graph s') v') eqn : V.
    reflexivity. eapply graph_iff_not_output in V. contradiction. apply H.
    eapply queue_in_graph. apply H. rewrite H1. rewrite map_app. simpl. solve_in.
    rewrite H5 in H6. inversion H6. assumption.
  - pose proof (multi_done _ _ _ _ H H0 D H4).
    pose proof (first_queue_contant_multi _ _ _ _ _ _ _ _ H H1 H2 H3 H5). destruct H6. assumption.
    destruct_all. unfold done in H4. rewrite H7 in H4.
    rewrite orb_true_iff in H4. destruct H4. destruct x; simpl in H4; inversion H4.
    rewrite isEmpty_def in H4. destruct (vIn (get_graph s') v') eqn : V.
    rewrite H4 in V. inversion V. eapply graph_iff_not_output in V. 
    contradiction. apply H0. eapply queue_in_graph. apply H. rewrite H1. rewrite map_app; simpl; solve_in.
    assumption.
Qed.

Lemma queue_smaller_than_dists: forall s g v,
  valid s g v ->
  (forall n, In n (map snd (get_queue s)) ->
  (forall m, In m (map snd (get_dists s)) ->
  (m <= n)%Z)).
Proof.
  intros. generalize dependent n. generalize dependent m. induction H; intros. unfold start in *; simpl in *. destruct H1.
  inversion H0; subst; simpl in *.
  - rewrite map_app in *. apply in_app_or in H1. apply in_app_or in H2. destruct H2.
    destruct H1. apply IHvalid.  assumption. right. assumption. simpl in H1.
    destruct H1. subst. pose proof (queue_structure _ _ _ v0 m vs H) .
    assert (get_queue (g0, (v0, m) :: vs, d) = (v0, m) :: vs) by reflexivity. specialize (H1 H5); clear H5.
    destruct H1. simpl in H1. apply Sorted_StronglySorted in H1. inversion H1; subst.
    rewrite Forall_forall in H9. apply H9. assumption. unfold Relations_1.Transitive. intros. omega. 
    destruct H1.  
    rewrite in_map_iff in H2. destruct H2. destruct x. simpl in *. destruct H2. subst.  
    rewrite (suci_def n0 n _ c v0 g0 g' H4) in H5. destruct H5. subst.
    destruct H1. assert ( (m<=j)%Z). apply IHvalid. assumption. left. reflexivity. omega.
    destruct H1. subst. omega. destruct H1.
  - apply IHvalid. assumption. right. assumption.
Qed.

(*Another key property of BFS: the distances are sorted*)
Theorem dists_sorted: forall s g v,
  valid s g v ->
  Sorted Z.le (map snd (get_dists s)).
Proof.
  intros. induction H.
  - simpl. constructor.
  - inversion H0; subst; simpl in *.
    + rewrite map_app. eapply SortA_app. apply eq_equivalence. apply IHvalid.
      simpl. constructor. constructor. constructor. intros.
      simpl in H4. rewrite <- In_InA_equiv in H4. rewrite <- In_InA_equiv in H3. 
      eapply queue_smaller_than_dists. apply H.
      simpl. simpl in H4. destruct H4. subst. left. reflexivity. destruct H4.
      simpl. assumption.
    + assumption.
Qed.

Definition dist_plus_one s v :=
  match find_dist s v with
  | Some n => Some (n + 1)
  | None => None
  end.

(** The big result: Every (v', d) pair that appears in the output is actually the shortest
  distance from v to v'. This also implies reachability, although that was already proved separately
  (and is needed for this proof) **)

Theorem bfs_tail_correct: forall s g v,
  valid s g v ->
  done s = true ->
  (forall v',
  vIn g v' = true ->
  dist_plus_one s v' = distance g v v').
Proof.
  intros. destruct (distance g v v') eqn : D.
  - generalize dependent v'. induction n as [ n IHn ] using (well_founded_induction lt_wf).
    intros. unfold dist_plus_one. destruct (find_dist s v') as [n'|] eqn : D' .
    rewrite find_dist_in in D'.
    pose proof (dist_upper_bound _ _ _ _ _ H D'). rewrite D in H2.
    rewrite Nat2Z.id in H2. simpl in H2.
    rewrite Nat.leb_le in H2. assert (n = n' + 1 \/ n < n' + 1) by omega.
    destruct H3. subst. reflexivity. clear H2.
    (*It cannot be the start node*)
    destruct (N.eq_dec v v'). subst. unfold distance in D. apply distance_some in D. destruct D as [l].
    destruct H2. subst. assert (shortest_path g v' v' (v' ::  nil)) by (apply distance_refl; assumption).
    apply distance_of_shortest_path in H4. simpl in H4. eapply shortest_path_distance in H4.
    rewrite H4. 
    pose proof (start_0_dist _ _ _ H).
    assert (In (v', 0%Z) (get_dists s)). apply H5. intro. rewrite H6 in D'. destruct D'.
    assert (Z.of_nat n' = 0%Z). eapply NoDup_pairs. apply   (no_dups_output _ _ _ H).
    apply D'. assumption. assert (n' = 0) by omega. subst. omega. assumption. 
    (*Get predecessor on shortest path*)
    assert (P := D). unfold distance in P. apply distance_some in P. destruct P as [l].
    destruct_all. assert (S:=H2). unfold shortest_path in H2. destruct_all.
    inversion H2; subst. contradiction.
    rename v'0 into w. simpl in H3.
    assert (vIn g v = true). eapply valid_in. apply H.
    destruct (distance g v w) as [nw|] eqn : DW . unfold distance in DW. assert (E := DW).
    apply distance_some in DW. destruct DW as [lw]. destruct H8.
    assert (nw + 1 = length (v' :: l0)). { (*idea, since lw is sp from v -> w, we know that
    length l0 >= length lw, if greater, then can have shorter path to v, so must be equal, this proves claim*)
    assert (length lw <= length l0). { unfold shortest_path in H8. destruct_all.
    assert (length lw <= length l0 \/ length l0 < length lw) by omega. destruct H11. assumption.
    apply H10 in H11. contradiction. } assert (length lw < length l0 \/ length lw = length l0) by omega.
    destruct H11. assert (path' g v v' (v' :: lw)). eapply p_multi. unfold shortest_path in H8.
    apply H8. assumption. exfalso. apply (H5 (v' :: lw)). simpl. omega. assumption. subst. 
    simpl. rewrite H11. omega. } rewrite <- H10. 
    assert (dist_plus_one s w = Some nw). apply IHn. omega. apply edges_valid in H7. destruct H7. assumption.
    assumption. unfold dist_plus_one in H11. destruct (find_dist s w) eqn : F. 2 : { inversion H11. }
    inversion H11; subst. rewrite find_dist_in in F.
    (*we know that the predecessor has distance 1 less and is thus in the distances correctly. We now
    look at the state at which this vertex is added to the distances*)
    pose proof (output_is_added _ _ _ _ _ H F). destruct H9 as [sw]. destruct H9 as [c].
    destruct H9 as [g']. destruct H9. destruct H12. destruct H14. destruct H15. 
    destruct H16 as [l2]. destruct H14. destruct H14. 
    (*first case, v' is already finished *)
    assert (L: n < n'). { assert (length l0 = length lw). simpl in H10; inversion H10. omega.
    rewrite H18 in H3. rewrite <- H18 in H3. omega. }
    destruct (In_dec N.eq_dec v' (map fst (get_dists sw))).
    rewrite H16 in i. rewrite map_app in i. apply in_app_or in i. destruct i.
    rewrite in_map_iff in H18. destruct H18. destruct x0. simpl in H18. destruct H18; subst.
    pose proof (dists_sorted _ _ _ H9). rewrite H16 in H18. rewrite map_app in H18. 
    simpl in H18. epose proof (sort_app (map snd l2) (Z.of_nat n :: nil) Z.le H18).
    assert (Relations_1.Transitive Z.le). unfold Relations_1.Transitive. intros; omega.
    specialize (H20 H21); clear H21. specialize (H20 i (Z.of_nat n)).
    assert (i <= Z.of_nat n)%Z.  apply H20. rewrite in_map_iff. exists (v', i).
    split. reflexivity. assumption. simpl. left. reflexivity. clear H20.
    pose proof (no_dups_output _ _ _ H). epose proof (NoDup_pairs _ v' i (Z.of_nat n') H20).
    assert (i = Z.of_nat n'). apply H22. eapply output_preserved_strong.
    apply H9. assumption. rewrite H16. solve_in. assumption. subst.
     omega. 
    simpl in H18. destruct H18. subst. exfalso. apply (H5 l0). simpl. omega. assumption. destruct H18.
    (* Now we know that v' has not been finished already. Now we need to see if it was already in
        the queue or not*)
    (*Next case: v' not already done, but it is already on the queue*)
    (*Hmm do we need that - just look at 1st position on the queue, it is <= nw + 1 by sorted, already a contradiction*)
    simpl in H14. assert (In v' (map fst (suci c (Z.of_nat n + 1)%Z))). { assert (vIn (get_graph sw) v' = true). 
    destruct (vIn (get_graph sw) v') eqn : ?. reflexivity. rewrite <- graph_iff_not_output in Heqb0.
    contradiction. apply H9. assumption.
    pose proof suci_def. pose proof (prior_state _ _ _ H9 H15). destruct H20 as [sp]. destruct H20.
    specialize (H17 _ H20 H21). destruct H17. destruct H22. simpl in H14. 
    specialize (H19 v' ((Z.of_nat n + 1)%Z) ((Z.of_nat n + 1)%Z) c w (get_graph sp) g' H22).
    destruct H19. rewrite in_map_iff. exists (v', (Z.of_nat n + 1)%Z). simpl. split. reflexivity.
    apply H24. split. reflexivity. rewrite edge_in_state. (*solve_assume.*) split; try(assumption).
    rewrite <- match_in. exists c. exists g'. assumption. 
    destruct (vIn (get_graph sp) v') eqn : V. reflexivity. rewrite <- graph_iff_not_output in V.
    assert (In v' (map fst (get_dists sw))). eapply output_preserved. apply H20.
    eapply multi_step. apply H21. constructor. assumption. contradiction. apply H20. assumption.
    apply H20. assumption. }
    assert (In v' (map fst (get_queue sw))). rewrite H14. rewrite map_app. solve_in.
    epose proof (@in_split_app_special _ _ N.eq_dec _ _ H19). destruct H20 as [i]. 
    destruct H20 as [l']. destruct H20 as [l'']. clear H19. assert (H19 := H20). clear H20. destruct H19.
    assert (suci c (Z.of_nat n + 1)%Z <> nil). {
    destruct (suci c (Z.of_nat n + 1)%Z) eqn : S'. destruct H18. intro. inversion H21. }
    pose proof (exists_last H21). destruct H22. destruct s0. rewrite e in H14.
    assert (Sorted Z.le (map snd (get_queue sw))). { 
    destruct l'. simpl in H19.
    pose proof (queue_structure _ _ _ _ _ _ H9 H19). apply H22. simpl in H19. destruct p.
    pose proof (queue_structure _ _ _ _ _ _ H9 H19). apply H22. }
    assert (i <= (Z.of_nat  n + 1))%Z. { destruct x1.
    assert (In (n2, i0) (suci c (Z.of_nat n + 1)%Z )) by (rewrite e; solve_in).
    pose proof suci_def. pose proof (prior_state _ _ _ H9 H15). destruct H25 as [sp]. destruct H25.
    specialize (H17 _ H25 H26). destruct H17. destruct H27. 
    specialize (H24 n2 i0 ((Z.of_nat n + 1)%Z) c w (get_graph sp) g' H27).
    rewrite H24 in H23. destruct H23. subst.
    clear H26. clear H25. clear H24. destruct l''. rewrite H14 in H19.
    pose proof ( app_inj_tail  (x ++ x0) l' (n2, (Z.of_nat n + 1)%Z) (v', i)).
    assert (x ++ x0 = l' /\ (n2, (Z.of_nat n + 1)%Z) = (v', i)). apply H23. rewrite <- app_assoc.
    apply H19. clear H23. destruct H24. inversion H24; subst. omega.
    remember (p :: l'') as l'''. assert (l''' <> nil). subst. intro. inversion H23.
    pose proof (exists_last H23). destruct H24. destruct s0. rewrite e0 in H19.
    rewrite H14 in H19. destruct x2.
    pose proof  ( app_inj_tail  (x ++ x0) ( l' ++ (v', i) :: x1) (n2, (Z.of_nat n + 1)%Z) (n3, i0)).
    assert (x ++ x0 = l' ++ (v', i) :: x1 /\ (n2, (Z.of_nat n + 1)%Z) = (n3, i0)). apply H24.
    rewrite <- app_assoc. rewrite H19. rewrite <- app_assoc. simpl. reflexivity. clear H24.
    destruct H25. inversion H25; subst. rewrite app_assoc in H14. rewrite H24 in H14.
    rewrite H14 in H22. rewrite map_app in H22. eapply sort_app in H22.
    apply H22. unfold Relations_1.Transitive. intros. omega. rewrite map_app.
    simpl. solve_in. simpl. left. reflexivity. }
    pose proof (first_queue_in_dists _ _ _ _ _ _ _ _ H9 H H19 H20 n1 H0).
    assert (i = Z.of_nat n'). eapply NoDup_pairs. eapply no_dups_output.
    apply H. apply H24. assumption. subst.
    assert (n' <= n + 1). omega. assert (n' < n + 1 \/ n' = n + 1) by omega.
    destruct H26. omega. subst. reflexivity. apply H.
    (*The hard part is over! The rest of the cases are basically just showing that None cases give contradictions*)
    unfold distance in DW. rewrite distance_none in DW. exfalso.
    apply (DW l0). assumption. apply H. rewrite find_dist_not in D'.
    pose proof (output_iff_reachable _ _ _ v' H H0). assert (In v' (map fst (get_dists s))).
    apply H2. apply distance_some in D. destruct_all. exists x. apply H3.
    rewrite in_map_iff in H3. destruct_all. destruct x; subst. exfalso. apply (D' i).
    simpl; assumption.
  - pose proof (output_iff_reachable _ _ _ v' H H0).
    unfold distance in D. rewrite distance_none in D.
    unfold dist_plus_one. destruct (find_dist s v') eqn : F.
    rewrite find_dist_in in F. assert ((exists l : list Node, path' g v v' l)).
    apply H2. rewrite in_map_iff. exists (v', Z.of_nat n). simpl. solve_assume.
    destruct_all. exfalso. apply (D x). assumption. apply H. reflexivity.
Qed.

End Correctness.

(** ** Equivalence and Correctness of [level] (bfs with distances) **)

Section Level.

Instance need_this_for_equations' : WellFounded (bf_measure_list (Node * Num.Int)).
Proof.
  unfold WellFounded. apply well_founded_bf_measure_list.
Defined.

Equations leveln' (x: (list (Node * Num.Int) * (gr a b))) : list (Node * Num.Int) by wf x (bf_measure_list (Node * Num.Int)) :=
  leveln' (nil, g) := nil;
  leveln' ((v,j) :: vs, g) := if (isEmpty g) then nil else
                                match (match_ v g) as y return ((match_ v g = y) -> _ ) with
                                | (Some c, g') => fun H : (match_ v g) = (Some c, g') => (v,j) :: leveln' ( (vs ++ suci c (Num.op_zp__ j (Num.fromInteger 1))), g')
                                | (None, g') => fun H: (match_ v g) = (None, g') => leveln' (vs, g')
                                 end (eq_refl).
Next Obligation.
unfold bf_measure_list. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H.
Defined.
Next Obligation.
unfold bf_measure_list. apply lex2. symmetry. unfold natNodes_eq. eapply match_none_size. apply H. unfold list_length_lt.
simpl. omega.
Defined.


Definition expand_leveln' := 
fun x : list (Node * Num.Int) * gr a b =>
let (l, g) := x in
match l with
| nil => fun _ : gr a b => nil
| p :: l0 =>
    fun g0 : gr a b =>
    (let (n, i) := p in
     fun (l1 : list (Node * Num.Int)) (g1 : gr a b) =>
     if isEmpty g1
     then nil
     else
      (let (m, g') as y return (match_ n g1 = y -> list (Node * Num.Int)) := match_ n g1 in
       match m as m0 return (match_ n g1 = (m0, g') -> list (Node * Num.Int)) with
       | Some c =>
           fun _ : match_ n g1 = (Some c, g') =>
           (n, i) :: leveln' (l1 ++ suci c (Num.op_zp__ i (Num.fromInteger 1)), g')
       | None => fun _ : match_ n g1 = (None, g') => leveln' (l1, g')
       end) eq_refl) l0 g0
end g.

Lemma unfold_leveln': forall x,
  leveln' x = expand_leveln' x.
Proof.
  intros. unfold expand_leveln'. apply leveln'_elim. reflexivity. reflexivity.
Qed.

Lemma leveln_leveln'_equiv: forall g q,
  leveln' (q, g) = leveln q g.
Proof.
  intros. remember (q, g) as x. generalize dependent q. revert g. 
  induction (x) as [y IH] using (well_founded_induction (well_founded_bf_measure_list (Node * Num.Int))).
  intros. destruct y. inversion Heqx; subst. clear Heqx. unfold leveln.
  rewrite unfold_leveln'. simpl. 
   unfold deferredFix2 in *. unfold curry in *.
  rewrite (deferredFix_eq_on _ (fun x => True) ( (bf_measure_list (_)) )).
  - simpl. destruct q eqn : Q.  
    + reflexivity.
    + simpl. destruct p. 
      destruct (isEmpty g) eqn : GE. reflexivity. 
      destruct (match_ n g) eqn : M. unfold leveln in IH. unfold deferredFix2 in IH. unfold curry in IH. destruct m.
      *  erewrite IH.
        reflexivity. unfold bf_measure_list. apply lex1. unfold natNodes_lt. eapply match_decr_size.
        symmetry. apply M. reflexivity.
      * erewrite IH. reflexivity. unfold bf_measure_list. apply lex2. unfold natNodes_eq.
        symmetry. eapply match_none_size. apply M. unfold list_length_lt. simpl. omega. reflexivity.
  - eapply well_founded_bf_measure_list.
  - unfold recurses_on. intros. unfold uncurry. destruct x. destruct l eqn : ?. reflexivity. 
    destruct (isEmpty g1) eqn : ?. reflexivity. simpl. destruct p. 
    destruct (match_ n g1) eqn : ?. destruct m. rewrite H0. reflexivity. apply I.
    unfold bf_measure_list. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply Heqd.
    rewrite H0. reflexivity. apply I. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size.
    apply Heqd. unfold list_length_lt. simpl. omega.
  - apply I.
Qed. 

Lemma leveln_tail_equiv: forall x l,
  get_dists (bfs_tail (x, l)) = l ++ leveln' (snd x, fst x).
Proof.
  intros x. remember (snd x, fst x) as x'. generalize dependent x.
  induction (x') using (well_founded_induction (well_founded_bf_measure_list (Node * Num.Int))).
  intros. destruct x'; inversion Heqx'; subst; clear Heqx'.
  rewrite unfold_leveln'. rewrite unfold_bfs_tail. simpl.  (* unfold expand_leveln'. *)
  destruct x as [g q]. simpl. destruct q eqn : Q.
  - simpl. rewrite app_nil_r. reflexivity.
  - destruct p as [v j]. destruct (isEmpty g) eqn : G. 
    + simpl. rewrite app_nil_r. reflexivity.
    + destruct (match_ v g) eqn : M. destruct m.
      * remember (g0, l0 ++ suci c (j + 1)%Z) as x. erewrite H. rewrite <- app_assoc. simpl.
        reflexivity. unfold bf_measure_list. simpl. destruct x. apply lex1.
        unfold natNodes_lt. eapply match_decr_size. symmetry. inversion Heqx; subst. apply M.
        destruct x. inversion Heqx; subst. simpl. reflexivity.
      * erewrite H. reflexivity. unfold bf_measure_list.  apply lex2.
        unfold natNodes_eq. symmetry. eapply match_none_size. apply M. unfold list_length_lt. simpl. omega.
        simpl. reflexivity.
Qed. 

(** Correctness of [level] **)


(*The Haskell level function (the actual BFS function) is equivalent to running bfs_tail from the start
  state and getting the distances. Now we get correctness from the previous proven results*)
Theorem level_tail_equiv: forall v g,
  get_dists (bfs_tail (start g v)) = level v g.
Proof.
  intros. unfold level. rewrite <- leveln_leveln'_equiv.
  rewrite leveln_tail_equiv. simpl. reflexivity.
Qed.

Lemma level_invalid: forall v (g: gr a b),
  vIn g v = false ->
  level v g = nil.
Proof.
  intros. unfold level. rewrite <- leveln_leveln'_equiv. simpl. rewrite unfold_leveln'. simpl.
  destruct (isEmpty g). reflexivity. destruct (match_ v g) eqn : M. destruct m.
  - assert (vIn g v = true). rewrite <- match_in. exists c. exists g0. assumption. rewrite H0 in H. inversion H.
  - rewrite unfold_leveln'. simpl. reflexivity.
Qed. 

(*[level], when run from a vertex v (not necessarily in the graph), produces a list of the shortest distances from v to v' for
  each v' that is reachable from v. Note that this also implies that a vertex is in this list iff it is
  reachable from v.*)
Theorem level_finds_shortest_path: forall v g v',
  match (find_dist_list (level v g) v') with
  | Some n => Some (n+1)
  | None => None
  end = distance g v v'.
Proof.
  intros.
  destruct (vIn g v) eqn : H.
  assert (V: valid (bfs_tail (start g v)) g v). eapply multi_valid. apply v_start. assumption.
  eapply bfs_tail_multi. assert (D': done (bfs_tail (start g v)) = true). eapply bfs_tail_done.
  rewrite <- level_tail_equiv.
  destruct (vIn g v') eqn : D.
  - pose proof bfs_tail_correct. unfold dist_plus_one in H0. unfold find_dist in H0.
    specialize (H0 (bfs_tail (start g v)) g v).
    specialize (H0 V D' v' D). rewrite <- H0. reflexivity.
  - replace (find_dist_list (get_dists (bfs_tail (start g v))) v') with (find_dist (bfs_tail (start g v)) v') by
    (unfold find_dist; reflexivity).
    destruct (find_dist (bfs_tail (start g v)) v') eqn : F.
    + rewrite find_dist_in in F. pose proof output_iff_reachable.
      assert (exists l, path' g v v' l). rewrite <- H0. rewrite in_map_iff. exists (v', Z.of_nat n).
      solve_assume. apply F. assumption. assumption. destruct_all. apply path_implies_in_graph in H1.
      destruct_all. rewrite H2 in D. inversion D. apply V.
    + destruct (distance g v v') eqn : DI.
      * apply distance_some in DI. destruct_all. unfold shortest_path in H0.
        destruct_all. apply path_implies_in_graph in H0. destruct_all. rewrite H3 in D. inversion D.
      * reflexivity.
  - assert (A:= H). apply level_invalid in H. rewrite H. simpl. destruct (distance g v v') eqn : D.
    + apply distance_some in D. destruct_all. unfold shortest_path in H0. destruct_all.
      apply path_implies_in_graph in H0. destruct_all. rewrite H0 in A. inversion A.
    + reflexivity.
Qed. 

(*The resulting list is sorted by shortest path distance*)
Theorem level_sorted_by_dist: forall v (g: gr a b),
  Sorted Z.le (map snd (level v g)).
Proof.
  intros. destruct (vIn g v) eqn : ?.  rewrite <- level_tail_equiv.
  eapply dists_sorted. eapply multi_valid. 
  apply v_start. apply Heqb0. apply bfs_tail_multi. rewrite level_invalid. simpl. constructor.
  assumption.
Qed.

Theorem no_dup_level: forall v (g: gr a b),
  NoDup (map fst (level v g)).
Proof.
  intros. destruct (vIn g v) eqn : ?. rewrite <- level_tail_equiv.
  eapply no_dups_output. eapply multi_valid. apply v_start. apply Heqb0. apply bfs_tail_multi.
  rewrite level_invalid. simpl. constructor. assumption.
Qed.
 
End Level.

(** ** Equivalence and Correctness of [bfsnInternal] (just returns vertices) **)

Section Bfsn.

(*TODO: see if there is a better specification. I'm not sure how to make a general specification, since
  the function can be arbitrary: ex: f x => 1 or f x => (number of outgoing edges), and the function depends
  on the context, which we don't really know anything about. But I can prove the general case for when the
  function depends only on the vertex , which includes [bfs].
  Relatedly, not sure what to say for [bfsn], since the list could be anything. The resulting output is not
  really bfs at all, and we really dont know much about the resulting output*)


Instance need_this_for_equations'' : WellFounded (bf_measure_list (Node)).
Proof.
  unfold WellFounded. apply well_founded_bf_measure_list.
Defined.
Section Func.
Context {c: Type}.


Equations bfsnInternal' (x :  (list Node) * (gr a b)) (f: Context a b -> c)  : (list c) by wf x (bf_measure_list Node) :=
  bfsnInternal' (nil, g) f := nil;
  bfsnInternal' ((v :: q'), g) f := if (isEmpty g) then nil else
      match (match_ v g) as y return ((match_ v g = y) -> _) with
                        | (Some c, g') => fun H : (match_ v g) = (Some c, g') => 
                          (f c) :: (bfsnInternal' (q' ++ (suc' c), g') f)
                        | (None, g') => fun H : (match_ v g) = (None, g') => ( bfsnInternal' (q', g') f)
                        end (eq_refl).
Next Obligation.
unfold bf_measure_list. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H.
Defined.
Next Obligation.
unfold bf_measure_list. apply lex2. symmetry. unfold natNodes_eq. eapply match_none_size. apply H. unfold list_length_lt.
simpl. omega.
Defined.

Definition expand_bfsnInternal' := 
fun (x : list Node * gr a b) (f : Context a b -> c) =>
(let (l, g) := x in
 fun f0 : Context a b -> c =>
 match l with
 | nil => fun (_ : gr a b) (_ : Context a b -> c) => nil
 | n :: l0 =>
     fun (g0 : gr a b) (f1 : Context a b -> c) =>
     if isEmpty g0
     then nil
     else
      (let (m, g') as y return (match_ n g0 = y -> list c) := match_ n g0 in
       match m as m0 return (match_ n g0 = (m0, g') -> list c) with
       | Some c0 => fun _ : match_ n g0 = (Some c0, g') => f1 c0 :: bfsnInternal' (l0 ++ suc' c0, g') f1
       | None => fun _ : match_ n g0 = (None, g') => bfsnInternal' (l0, g') f1
       end) eq_refl
 end g f0) f.

Lemma unfold_bfsnInternal' : forall x f, bfsnInternal' x f = expand_bfsnInternal' x f.
Proof.
  intros. unfold expand_bfsnInternal'. apply bfsnInternal'_elim. reflexivity. reflexivity.
Qed.

(*Unfortunately, [bfsnInternal] contains a function parameter, so we need yet another well_founded relation
  to enable unrolling [deferredFix]. This one is made up a compound lexicographic order, where we ignore
  the function argument, so it ends up being effectively equivalent to [bf_measure_queue]*)

Definition bfs_two {C} := (lex _ C (@queue_length_lt Node) (fun x y => length (toList _ x) = length (toList _ y)) (fun x y => False)).

Definition bfs_three {C} := lex _ _ (natNodes_lt) (natNodes_eq)  (@bfs_two C).

Lemma wf_bfs_three: forall C, well_founded (@bfs_three C).
Proof.
  intros. unfold bfs_three. apply WF_lex.
  - apply f_nat_lt_wf.
  - unfold bfs_two. apply WF_lex.
    + apply f_nat_lt_wf.
    + unfold well_founded. intros. apply Acc_intro. intros. destruct H.
    + unfold Transitive. intros. omega.
    + intros. unfold queue_length_lt in *. destruct_all. unfold list_length_lt in *. omega.
    + unfold Symmetric. intros. omega.
  - unfold Transitive. unfold natNodes_eq. intros. omega.
  - intros. unfold natNodes_eq in *. unfold natNodes_lt in *. destruct_all. omega.
  - unfold Symmetric. intros. unfold natNodes_eq in *. omega.
Qed.

Lemma bfsnInternal_equiv: forall q g f,
  bfsnInternal f q g = bfsnInternal' ((toList _ q),g) f.
Proof.
  intros. remember (toList Node q) as l. remember (l, g) as x. 
  generalize dependent l. revert g. revert q.
  induction (x) as [y IH] using (well_founded_induction (well_founded_bf_measure_list _)).
  intros. destruct y. inversion Heqx. subst. clear Heqx. unfold bfsnInternal.
  rewrite unfold_bfsnInternal'. simpl. 
  unfold deferredFix3. unfold curry. unfold deferredFix2. unfold curry.
  rewrite (deferredFix_eq_on _ (fun x => True) ( (bfs_three ) )).
  simpl. destruct (queueGet q) eqn : Q.
  destruct (queueEmpty q) eqn : QE.
  - simpl. rewrite toList_queueEmpty in QE. rewrite QE. reflexivity.
  - simpl. destruct (toList _ q) eqn : L.
    + rewrite <- toList_queueEmpty in L. rewrite L in QE. inversion QE.
    + pose proof (toList_queueGet _ _ _ _ L). rewrite Q in H. destruct H. simpl in *. subst.
      destruct (isEmpty g) eqn : G. reflexivity.
      destruct (match_ n0 g) eqn : M. destruct m.
      * unfold bfsnInternal in IH. unfold deferredFix3 in IH. unfold curry in IH. unfold deferredFix2 in IH.
        unfold curry in IH. erewrite IH. reflexivity. unfold bf_measure_list. apply lex1. 
        unfold natNodes_lt. eapply match_decr_size. symmetry. apply M. reflexivity.
        rewrite toList_queuePutList . reflexivity.
      * unfold bfsnInternal in IH. unfold deferredFix3 in IH. unfold curry in IH. unfold deferredFix2 in IH.
        unfold curry in IH. erewrite IH. reflexivity. apply lex2. unfold natNodes_eq. symmetry. 
        eapply match_none_size. apply M. unfold list_length_lt. simpl. omega. reflexivity.
        reflexivity.
  - apply wf_bfs_three.
  - unfold recurses_on. intros. unfold uncurry. destruct x. destruct p. destruct (queueGet q0) eqn : Q'.
    destruct (queueEmpty q0) eqn : QE'. simpl. reflexivity.
    destruct (isEmpty g1) eqn : G'; try(reflexivity). simpl. destruct (match_ n g1) eqn : M'.
    destruct m. rewrite H0. reflexivity. apply I. unfold bfs_three.
    apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M'. rewrite H0. reflexivity.
    apply I. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M'.
    apply lex1. unfold queue_length_lt. destruct (toList _ q0) eqn : L'.
    rewrite <- toList_queueEmpty in L'. rewrite L' in QE'. inversion QE'.
    pose proof (toList_queueGet _ _ _ _ L'). rewrite Q' in H1. simpl in H1. destruct H1. subst.
    unfold list_length_lt. simpl. omega.
  - apply I.
Qed.

(*Not sure what we can say about the general bfsnInternal function, but we can prove that if the function
  given depends only on the vertices, it is the same as applying that function to each vertex in the output
  of [leveln']*)
Lemma bfsInternal_on_vertex_equiv: forall q q' (g: gr a b) (f: Context a b -> c) (default : a),
  (forall c c', node' c = node' c' -> f c = f c') ->
  map fst q' = q ->
  bfsnInternal' (q, g) f = map (fun (x: Node * Num.Int) => let (v, d) := x in f (nil, v, default, nil)) (leveln' (q', g)).
Proof.
  intros. remember (q, g) as p. generalize dependent q. generalize dependent g. generalize dependent q'.
  induction p using (well_founded_induction (well_founded_bf_measure_list _)). intros.
  rewrite unfold_bfsnInternal'. rewrite unfold_leveln'. simpl. destruct p. inversion Heqp. rewrite H3 in H0. rewrite H4 in H0. clear Heqp. clear H3. clear l. clear H4. clear g0.
  simpl. destruct q eqn : Q.
  - destruct q'. simpl. reflexivity. simpl in H1. inversion H1.
  - destruct q' eqn : Q'. simpl in H1. inversion H1. simpl in H1. inversion H1. subst. destruct p.
    simpl. destruct (isEmpty g) eqn : E. simpl. reflexivity.
    destruct (match_ n g) eqn : M. destruct m.
    + simpl. specialize (H c0 (nil, n, default, nil)). simpl in H. rewrite H. erewrite H0.  reflexivity.
      apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M. reflexivity.
      rewrite map_app. unfold suci. rewrite map_fst_zip. reflexivity. rewrite repeat_length.
      apply length_equiv . destruct c0. destruct p. destruct p. simpl. apply match_context in M.
      destruct_all. subst. reflexivity.
    + erewrite H0. reflexivity. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size.
      apply M. unfold list_length_lt. simpl. omega. reflexivity. reflexivity.
Qed.
End Func.

(** ** Correctness of [bfs] **)
(*This states that running bfs is the same as taking the first element from [level]. Note that this immediately
  implies that bfs contains all reachable vertices and they are sorted by distance*)
(*Need an instance of type [a] for the proof to go through. TODO: see if I can eliminate this assumption*)
Theorem bfs_def: forall v (g: gr a b) (x: a),
  bfs v g = map fst (level v g).
Proof.
  intros. unfold bfs. unfold bfsWith. unfold level. 
  pose proof (@bfsnInternal_equiv Node). rewrite H.
  clear H. rewrite <- leveln_leveln'_equiv.
  pose proof (@bfsInternal_on_vertex_equiv Node (toList Node (queuePut v mkQueue)) 
  ((v, Num.fromInteger 0) :: nil) g node' x). simpl in H. unfold fst. apply H. intros.
  assumption. reflexivity.
Qed. 

End Bfsn.


(** ** Equivalence and Correctness of [bft] (returns whole path) **)
Section Bft.

Instance need_this_for_equations''' : WellFounded (bf_measure_list (Path)).
Proof.
  unfold WellFounded. apply well_founded_bf_measure_list.
Defined.

Equations bf' (x :  (list Path) * (gr a b)) : RootPath.RTree by wf x (bf_measure_list Path) :=
  bf' (nil, g) := nil;
  bf' ((nil :: q'), g) := if (isEmpty g) then nil else GHC.Err.patternFailure;
  bf' (((v :: t) :: q'), g) := let p:= v :: t in  if (isEmpty g) then nil else
      match (match_ v g) as y return ((match_ v g = y) -> _) with
                        | (Some c, g') => fun H : (match_ v g) = (Some c, g') => p :: (bf' ((q' ++ map (fun x => x :: p)  (suc' c)), g'))
                        | (None, g') => fun H : (match_ v g) = (None, g') => ( bf' (q', g'))
                        end (eq_refl).
Next Obligation.
unfold bf_measure_list. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H.
Defined.
Next Obligation.
unfold bf_measure_list. apply lex2. symmetry. unfold natNodes_eq. eapply match_none_size. apply H. unfold list_length_lt.
simpl. omega.
Defined.

Definition expand_bf' := 
fun x : list Path * gr a b =>
let (l, g) := x in
match l with
| nil => fun _ : gr a b => nil
| p :: l0 =>
    fun g0 : gr a b =>
    match p with
    | nil => fun (_ : list Path) (g1 : gr a b) =>  if (isEmpty g) then nil else GHC.Err.patternFailure
    | n :: l1 =>
        fun (l2 : list Path) (g1 : gr a b) =>
        if isEmpty g1
        then nil
        else
         (let (m, g') as y return (match_ n g1 = y -> list (list Node)) := match_ n g1 in
          match m as m0 return (match_ n g1 = (m0, g') -> list (list Node)) with
          | Some c =>
              fun _ : match_ n g1 = (Some c, g') =>
              (n :: l1) :: bf' (l2 ++ map (fun x0 : Node => x0 :: n :: l1) (suc' c), g')
          | None => fun _ : match_ n g1 = (None, g') => bf' (l2, g')
          end) eq_refl
    end l0 g0
end g.

Lemma unfold_bf' : forall x, bf' x = expand_bf' x.
Proof.
  intros. unfold expand_bf'. apply bf'_elim. reflexivity. reflexivity. reflexivity.
Qed.

(*Need assumption that q is nonempty, or else queueGet is undefined (and this is OK, bft is called on nonempty queue*)
Lemma bf_bf'_equiv: forall g q,
  bf' ((toList _ q), g) = bf q g.
Proof.
  intros. remember (toList Path q) as l. remember (l, g) as x. generalize dependent q.
  generalize dependent g. revert l.
  induction (x) as [y IH] using (well_founded_induction (well_founded_bf_measure_list _)).
  intros. destruct y. inversion Heqx; subst. clear Heqx. unfold bf.
  rewrite unfold_bf'. simpl. 
   unfold deferredFix2 in *. unfold curry in *.
  rewrite (deferredFix_eq_on _ (fun x => True) ( (bf_measure_queue (_)) )).
  - simpl.  destruct (toList _ q) eqn : Q'. rewrite <- toList_queueEmpty in Q'. rewrite Q'. simpl.
    reflexivity. assert (queueEmpty q = false). destruct (queueEmpty q) eqn : ?.
    rewrite toList_queueEmpty in Heqb0. rewrite Heqb0 in Q'. inversion Q'.
    reflexivity. rewrite H. simpl. destruct (isEmpty g) eqn : E.
    destruct p. reflexivity. rewrite E. reflexivity. 
    destruct (queueGet q) eqn : G.
    pose proof (toList_queueGet _ _ _ _ Q'). rewrite G in H0. simpl in H0. destruct H0. subst.
    destruct p.
    reflexivity. rewrite E. destruct (match_ n g) eqn : M. destruct m.
    + unfold bf in IH. unfold deferredFix2 in IH. unfold curry in IH. erewrite IH. reflexivity.
      apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M. reflexivity.
      rewrite toList_queuePutList . reflexivity.
    + unfold bf in IH. unfold deferredFix2 in IH. unfold curry in IH. erewrite IH. reflexivity.
      apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M. unfold list_length_lt.
      simpl. omega. reflexivity. reflexivity.
  - apply well_founded_bf_measure_queue.
  - unfold recurses_on. intros. unfold uncurry. destruct x. destruct (queueEmpty q0) eqn : QE. simpl.
    reflexivity. simpl. destruct (isEmpty g1); simpl; try(reflexivity). destruct (queueGet q0) eqn : Q''.
    destruct p; try(reflexivity). destruct (match_ n g1) eqn : M'. destruct m. rewrite H0.
    reflexivity. auto. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M'.
    rewrite H0. reflexivity. auto. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size.
    apply M'. unfold queue_length_lt. destruct (toList _ q0) eqn : L. rewrite <- toList_queueEmpty in L.
    rewrite L in QE. inversion QE.
    pose proof (toList_queueGet _ _ _ _ L). rewrite Q'' in H1; simpl in H1; destruct H1; subst.
    unfold list_length_lt. simpl. omega.
  - auto.
Qed.

(** ** Correctness of [bf] **)
(*We want to prove that each is a shortest path. We need to know that the returned paths are valid and that
  their length equals the result of [distance]*)


(*Valid paths. Because we defined a path as the list between vertex u and v, we simply pull out the last
  vertex from the list, verify that it is v, and the rest should be a path according to our previous definition*)
(*Fixpoint valid_path (g: gr a b) (v u : Node) (l: list Node) : Prop :=
  match l with
  | 
*)
(*
Definition valid_path (g: gr a b) (v u : Node) (l: list Node) : Prop :=
  (u = v /\ l = (v :: nil)) \/ exists l', l = u :: l' ++ (v :: nil) /\ path g v u l'.

Definition head {a} (l: list a) : option a :=
  match l with
  | nil => None
  | x :: l => Some x
  end.

Lemma valid_path_head: forall g u v l,
  valid_path g v u l ->
  head l = Some u.
Proof.
  intros. unfold valid_path in H. destruct H; destruct_all. subst. reflexivity.
  rewrite H. reflexivity.
Qed.

Definition All {A} (f: A -> Prop) (l: list A) :=
  fold_right (fun x acc => f x /\ acc) True l.

Lemma All_app: forall {A} (l1 l2: list A) f,
  All f (l1 ++ l2) <-> All f l1 /\ All f l2.
Proof.
  intros. generalize dependent l2. induction l1; intros; simpl.
  - split; intros. split. auto. assumption. destruct H. assumption.
  - split; intros. split. destruct_all. split. assumption. apply IHl1 in H0. apply H0.
    destruct_all. rewrite IHl1 in H0. apply H0. destruct_all. split. assumption.
    rewrite IHl1. split; assumption.
Qed.

Lemma All_in: forall {A} (l: list A) f,
  All f l <-> (forall x, In x l -> f x).
Proof.
  intros. induction l; intros; split; intros.
  - inversion H0.
  - simpl. auto.
  - simpl in *. destruct H. destruct H0. subst. auto. apply IHl; assumption.
  - simpl. split. apply H. simpl. left. reflexivity. apply IHl. intros. apply H. right. assumption.
Qed.
*)
Definition bf_state : Type := gr a b * list Path * list Path.

Definition bf_queue (s: bf_state) :=
  match s with
  | (_, q, _) => q
  end.

Definition bf_graph (s: bf_state) :=
  match s with
  |(g, _ ,_) => g
  end.

Definition bf_out (s: bf_state) :=
  match s with
  |(_, _, o) => o
  end.

Inductive bf_step : bf_state -> bf_state -> Prop :=
  | bf_find: forall g d v t vs c g',
    isEmpty g = false ->
    match_ v g = (Some c, g') ->
    bf_step (g, (v :: t) :: vs, d) (g', (vs ++ map (fun x => x :: v :: t)  (suc' c)), d ++ ((v :: t) :: nil))
  | bf_skip: forall g d v t vs g',
    isEmpty g = false ->
    match_ v g = (None, g') ->
    bf_step (g, (v :: t) :: vs, d) (g', vs, d).

Definition bf_start (g : gr a b) (v: Graph.Node) : bf_state := (g, ((v :: nil) :: nil), nil).

(*A valid state is any state that can be reached from the start state.*)
Inductive bf_valid : bf_state -> (gr a b) -> Node -> Prop :=
  | v_bf_start : forall g v, vIn g v = true -> bf_valid (bf_start g v) g v
  | v_bf_step : forall s s' v g, bf_valid s' g v -> bf_step s' s -> bf_valid s g v.

(*It is much easier to reason about the valid paths by stepping through the function, since the
  graph changes at every step, and we need to show that the paths are still valid in terms of the original grpah*)
Lemma bf_graph_subset: forall s v g,
  bf_valid s g v ->
  (forall v, vIn (bf_graph s) v = true -> vIn g v = true) /\
  (forall u v, eIn (bf_graph s) u v = true -> eIn g u v = true).
Proof.
  intros. induction H; simpl.
  - split; intros; assumption.
  - inversion H0; subst; simpl in *. assert (M:=H2). apply match_remain_some in H2.
    destruct H2. split. intros. rewrite H2 in H4. apply IHbf_valid. apply H4.
    intros. rewrite H3 in H4. apply IHbf_valid. apply H4. apply match_remain_none in H2.
    subst. apply IHbf_valid.
Qed.

Lemma queue_valid_paths: forall s v g v' l,
  bf_valid s g v ->
  In (v' :: l) (bf_queue s) ->
  path' g v v' (v' :: l).
Proof.
  intros. generalize dependent v'. revert l. induction H; intros.
  - simpl in H0. destruct H0. inversion H0; subst. constructor. assumption. destruct H0.  
  - inversion H0; subst; simpl in *.
    apply in_app_or in H1. destruct H1. apply IHbf_valid. right. assumption.
    rewrite in_map_iff in H1. destruct_all. inversion H1; subst.
    eapply p_multi. apply IHbf_valid. left. reflexivity. unfold suc' in H4.
    unfold Base.op_z2218U__ in H4. unfold Base.map in H4. rewrite snd_equiv in H4.
    destruct c. destruct p. destruct p. rewrite context4l'_def in H4. 
    assert (eIn g0 v0 v' = true). apply H4. eapply bf_graph_subset. apply H.
    simpl. assumption. apply H3. apply IHbf_valid. right. assumption.
Qed.


Lemma output_valid_paths: forall s v g v' l,
  bf_valid s g v ->
  In (v' :: l) (bf_out s) ->
  path' g v v' (v' :: l).
Proof.
  intros. induction H.
  - simpl in H0. destruct H0.
  - inversion H1; subst; simpl in *.
    + apply in_app_or in H0. destruct H0. apply IHbf_valid. assumption.
      pose proof (queue_valid_paths _ _ _ v' l H). apply H4. simpl. left. simpl in H0.
      destruct H0; inversion H0. subst. reflexivity.
    + apply IHbf_valid; assumption.
Qed.

(*Now need to prove equivalence with the translated version**)
Equations bf_tail (s: bf_state) : bf_state by wf (bf_queue s, bf_graph s) (bf_measure_list _) :=
  bf_tail (g, nil, x) => (g, nil, x);
  bf_tail (g, (nil :: q'), x) =>  (g, (nil :: q'), x);
  bf_tail (g, (v :: t) :: vs, d) => if (isEmpty g) then  (g, (v :: t) :: vs, d) else
      match (match_ v g) as y return ((match_ v g = y) -> _) with
      | (Some c, g') => fun H: (match_ v g) = (Some c, g') => 
        bf_tail (g', (vs ++ map (fun x => x :: (v :: t))  (suc' c)), d ++ (v :: t) :: nil)
      | (None, g') => fun H: (match_ v g) = (None, g') => bf_tail (g', vs, d)
      end (eq_refl).
Next Obligation.
unfold bf_measure_list. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H.
Defined.
Next Obligation.
unfold bf_measure_list. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply H. unfold list_length_lt.
simpl. omega.
Defined.

Definition expand_bf_tail := 
fun s : gr a b * list Path * list Path =>
let (p, l) := s in
(let (g, l0) := p in
 fun l1 : list Path =>
 match l0 with
 | nil => fun l2 : list Path => (g, nil, l2)
 | p0 :: l2 =>
     fun l3 : list Path =>
     match p0 with
     | nil => fun l4 l5 : list Path => (g, nil :: l4, l5)
     | n :: l4 =>
         fun l5 l6 : list Path =>
         if isEmpty g
         then (g, (n :: l4) :: l5, l6)
         else
          (let (m, g') as y return (match_ n g = y -> gr a b * list Path * list Path) := match_ n g in
           match m as m0 return (match_ n g = (m0, g') -> gr a b * list Path * list Path) with
           | Some c =>
               fun _ : match_ n g = (Some c, g') =>
               bf_tail (g', l5 ++ map (fun x : Node => x :: n :: l4) (suc' c), l6 ++ (n :: l4) :: nil)
           | None => fun _ : match_ n g = (None, g') => bf_tail (g', l5, l6)
           end) eq_refl
     end l2 l3
 end l1) l.

Lemma unfold_bf_tail: forall s,
  bf_tail s = expand_bf_tail s.
Proof.
  intros. unfold expand_bf_tail. apply bf_tail_elim; intros; reflexivity.
Qed.

Lemma bf_multi_valid: forall s1 s2 g v,
  bf_valid s1 g v ->
  multi (bf_step) s1 s2 ->
  bf_valid s2 g v.
Proof.
  intros. induction H0. assumption. apply IHmulti. eapply v_bf_step. apply H. assumption.
Qed.

Lemma bf_tail_multi: forall s,
  multi (bf_step) s (bf_tail s).
Proof.
  intros. destruct s as[r d].
  remember (snd r, fst r) as r'. generalize dependent r. revert d. 
  induction (r') using (well_founded_induction (well_founded_bf_measure_list (_))).
  intros. destruct r' as [q g]. inversion Heqr'; subst. clear Heqr'. destruct r as [g q].
  rewrite unfold_bf_tail. simpl. destruct q eqn : Q.
  - apply multi_refl.
  - destruct p as [|v j]. apply multi_refl. destruct (isEmpty g) eqn : E.
    + apply multi_refl.
    + destruct (match_ v g) eqn : M.  destruct m eqn : M'.
      *  eapply multi_step. apply bf_find. assumption. apply M. eapply H. unfold bf_measure_list.
         apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M. simpl. reflexivity.
      * eapply multi_step. apply bf_skip. assumption. apply M. eapply H. unfold bf_measure_list.
        apply lex2. unfold natNodes_eq. assert (g = g0) by (eapply match_remain_none; apply M).
        subst. eapply match_none_size. simpl.  apply M. 
        unfold list_length_lt. simpl. assert (length l < S(length l)) by omega. apply H0. simpl. 
        assert (g = g0) by (eapply match_remain_none; apply M). subst. reflexivity.
Qed.

Lemma bf_tail_equiv: forall x l,
  (~In nil (snd x)) ->
  bf_out (bf_tail (x, l)) = l ++ bf' (snd x, fst x).
Proof.
  intros x. remember (snd x, fst x) as x'. generalize dependent x.
  induction (x') using (well_founded_induction (well_founded_bf_measure_list _)).
  intros. destruct x'; inversion Heqx'; subst; clear Heqx'.
  rewrite unfold_bf'. rewrite unfold_bf_tail. simpl.  (* unfold expand_leveln'. *)
  destruct x as [g q]. simpl. destruct q eqn : Q.
  - simpl. rewrite app_nil_r. reflexivity.
  - destruct l0 as [|v j]. simpl in H0. exfalso. apply H0. left. reflexivity. destruct (isEmpty g) eqn : G. 
    + simpl. rewrite app_nil_r. reflexivity.
    + simpl.  destruct (match_ v g) eqn : M. destruct m.
      * erewrite H. rewrite <- app_assoc. simpl. reflexivity. 
        unfold bf_measure_list. simpl. apply lex1.
        unfold natNodes_lt. eapply match_decr_size. symmetry.  apply M. simpl. reflexivity.
        intro. simpl in H1. apply in_app_or in H1. destruct H1. apply H0. right. assumption.
        rewrite in_map_iff in H1. destruct_all. inversion H1.
      * erewrite H. reflexivity. unfold bf_measure_list.  apply lex2.
        unfold natNodes_eq. symmetry. eapply match_none_size. apply M. unfold list_length_lt. simpl. omega.
        simpl. reflexivity. simpl in *. intro. apply H0. right. assumption.
Qed.

Lemma bft_tail_equiv: forall v g,
  bf_out (bf_tail (bf_start g v)) = bft v g.
Proof.
  intros. unfold bft. rewrite <- bf_bf'_equiv. rewrite bf_tail_equiv. simpl. reflexivity.
  intro. simpl in H. destruct H. inversion H. auto.
Qed.

(** ** Correctness of [bf] **)

(*Need this as a helper: If v is not in the graph, this returns nil*)
Lemma bf_invalid_v: forall v (g: gr a b),
  vIn g v = false ->
  bft v g = nil.
Proof.
  intros. unfold bft. rewrite <- bf_bf'_equiv. simpl. rewrite unfold_bf'. simpl.
  destruct (isEmpty g). reflexivity. destruct (match_ v g) eqn : M. destruct m.
  assert (vIn g v = true). eapply match_in. exists c. exists g0. assumption. rewrite H0 in H.
  inversion H. rewrite unfold_bf'. simpl. reflexivity.
Qed. 

(*1. All paths in the output are valid*)
Theorem bft_paths_valid: forall v (g: gr a b) v' l,
  In (v' :: l) (bft v g) ->
  path' g v v' (v' :: l).
Proof.
  intros. destruct (vIn g v) eqn : V. rewrite <- bft_tail_equiv in H. eapply output_valid_paths in H.
  apply H. eapply bf_multi_valid.
  apply v_bf_start. assumption. apply bf_tail_multi. rewrite bf_invalid_v in H. simpl in H. inversion H.
  assumption. 
Qed.


Lemma zip_fst_map: forall {A B} (l: list A) (l' : list B) l'',
   length l = length l' ->
   map (fun x => Some (fst x)) (List.zip l l') = map (fun x => head x) (map (fun x => x :: l'') l). 
Proof. 
  intros. generalize dependent l'. revert l''. induction l. intros.
  simpl. reflexivity. intros.
  simpl. destruct l'. simpl in H. omega. simpl in H. inversion H. eapply IHl in H1.
  simpl. rewrite H1. reflexivity.
Qed. 
  
(*Each path starts/ends with the corresponding vertex from [leveln]*)
(*More specifically, if we find the head of each list from [bf], this gives us Some of the first element 
  of [leveln] (as long as we start with equivalent queues)*)
Lemma bf_vertex_order: forall (g: gr a b) q q',
  map (fun x => Some (fst x)) q = map (fun x => head x) q' ->
  map (fun x => Some (fst x)) (leveln' (q, g)) = map (fun x => head x) (bf' (q', g)).
Proof.
  intros. remember (q, g) as x. generalize dependent q. revert g. revert q'. 
  induction (x) as [y IH] using (well_founded_induction (well_founded_bf_measure_list _)).
  intros. destruct y. inversion Heqx. subst. clear Heqx. rewrite unfold_leveln'.
  rewrite unfold_bf'. simpl. destruct q; simpl. simpl in H.
  destruct q'. simpl. reflexivity. simpl in H. inversion H. destruct p.
  destruct q'. simpl in H. inversion H. simpl in H. inversion H. 
  destruct (isEmpty g) eqn : E. simpl. destruct l. simpl. reflexivity.
  rewrite E. simpl. reflexivity. destruct l. simpl in H1. inversion H1.
  rewrite E. simpl in H1. symmetry in H1. inversion H1; subst. destruct (match_ n g) eqn : M. destruct m.
  - simpl. erewrite IH. reflexivity. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry.
    apply M. 2 : { reflexivity. } rewrite map_app. rewrite map_app. rewrite H2.
    assert (map (fun x : Node * Num.Int => Some (fst x)) (suci c (i + 1)%Z) =
     map (fun x : list Node => head x) (map (fun x0 : Node => x0 :: n :: l) (suc' c))).
    unfold suci. apply zip_fst_map.
     rewrite repeat_length. rewrite length_equiv. reflexivity.
    rewrite H0. reflexivity.
  - erewrite IH. reflexivity. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M.
    unfold list_length_lt. simpl. omega. apply H2. reflexivity.
Qed.

Lemma bft_vertex_order: forall (g: gr a b) v,
  map (fun x => Some (fst x)) (level v g) = map (fun x => head x) (bft v g).
Proof.
  intros. unfold level. unfold bft. rewrite <- leveln_leveln'_equiv.
  rewrite <- bf_bf'_equiv. apply bf_vertex_order. simpl. reflexivity.
Qed. 

(*The length of each path is the value in leveln - 1*)
(*We need the hypothesis from before (about the fst elements) so that we know that the queues actually
  have the same vertices in the same order*)
Lemma bf_length: forall (g: gr a b) q q',
  (~In nil q') ->
  map (fun x => Some (fst x)) q = map (fun x => head x) q' ->
  map snd q = map (fun x => (List.length x - 1)%Z) q' ->
  map snd (leveln' (q, g)) = map (fun x => (List.length x - 1)%Z) (bf' (q', g)).
Proof.
  intros. remember (q, g) as x. generalize dependent q. revert g. generalize dependent q'. 
  induction (x) as [y IH] using (well_founded_induction (well_founded_bf_measure_list _)).
  intros. destruct y. inversion Heqx. subst. clear Heqx. rewrite unfold_leveln'.
  rewrite unfold_bf'. simpl. destruct q; simpl. simpl in H0. destruct q'. reflexivity.
  simpl in H1. inversion H1. destruct q'. inversion H1. simpl in H1. inversion H1.
  destruct p. simpl in *. subst. destruct l. exfalso. apply H. left. reflexivity.
  destruct (isEmpty g) eqn : E. reflexivity.
  destruct (match_ n g) eqn : M. simpl in H0.  inversion H0. symmetry in H3. subst. 
  destruct m.
  - rewrite M. simpl. erewrite IH. reflexivity. apply lex1. unfold natNodes_lt. eapply match_decr_size.
    symmetry. apply M. intro. apply in_app_or in H2. destruct H2. apply H. right. assumption.
    rewrite in_map_iff in H2. destruct_all. inversion H2. 3 : { reflexivity. } rewrite map_app.
    rewrite map_app. unfold suci. rewrite (zip_fst_map _ _ (n :: l)). rewrite H5. reflexivity.
    rewrite repeat_length. apply length_equiv. rewrite map_app. rewrite map_app. rewrite H4.
    assert ( map snd (suci c (List.length (n :: l) - 1 + 1)%Z) = 
    map (fun x : list Node => (List.length x - 1)%Z) (map (fun x0 : Node => x0 :: n :: l) (suc' c))). {
    unfold suci. assert ((List.length (n :: l) - 1 + 1)%Z = (List.length (n :: l))) by omega. rewrite H2. clear H2.
    simpl. rewrite <- length_equiv. assert (forall {A} (l: list A) l' ,
    map snd (List.zip l (repeat (List.length l') (length l))) =
    map (fun x => ((List.length x - 1)%Z)) (map (fun x => x :: l') l)). { intros. generalize dependent l'.
    induction l0; intros. simpl. reflexivity. simpl. rewrite IHl0.
    assert (forall {B} (x : B) l, List.length (x :: l) = (List.length l + 1)%Z). { intros.
    assert (Z.to_nat (List.length (x :: l1)) = Z.to_nat (List.length l1 + 1)). rewrite <- length_equiv.
    rewrite Z2Nat.inj_add. rewrite <- length_equiv.  assert (Z.to_nat 1%Z = 1). unfold Z.to_nat. unfold Pos.to_nat.
    unfold Pos.iter_op. reflexivity. rewrite H2. simpl. omega. unfold List.length. 
    rewrite len_acc_def. simpl. omega. omega. 
    apply Z2Nat.inj. unfold List.length. rewrite len_acc_def. simpl. apply Zle_0_pos .
    assert (0 <= List.length l1)%Z. unfold List.length. rewrite len_acc_def. simpl. omega.
    omega. apply H2. } rewrite H2. assert ((List.length l' + 1 - 1)%Z = List.length l') by omega. rewrite H3.
    reflexivity. } apply H2. } rewrite H2. reflexivity. 
  - rewrite M. erewrite IH. reflexivity. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size.
    apply M. unfold list_length_lt. simpl. omega. intro. apply H. right. assumption.
    apply H5. apply H4. reflexivity.
Qed.

Lemma bft_length: forall (g: gr a b) v,
  map snd (level v g) = map (fun x => (List.length x - 1)%Z) (bft v g).
Proof.
  intros. unfold level. unfold bft. rewrite <- leveln_leveln'_equiv.
  rewrite <- bf_bf'_equiv. apply bf_length. 
  - intro. simpl in H. destruct H. inversion H. auto.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(*The big result: that [bft] finds shortest paths. We use List.zip to preserve order*)
Theorem bft_shortest_paths: forall (g: gr a b) v p d u,
  In (p, (u, d)) (List.zip (bft v g) (level v g)) ->
  shortest_path g v u p /\ length p = Z.to_nat d + 1.
Proof.
  intros. pose proof (bft_length g v).
  pose proof (bft_vertex_order g v). symmetry in H0. symmetry in H1.
  pose proof (in_zip_map (bft v g) (level v g) p (u,d) _ _ H H0).
  pose proof (in_zip_map (bft v g) (level v g) p (u,d) _ _ H H1).
  simpl in H2. simpl in H3. unfold hd_error in H3. destruct p. inversion H3.
  inversion H3; subst. 
  assert ((List.length (u :: p) -1)%Z = Z.of_nat (length p)). {
  unfold List.length at 1. rewrite len_acc_def.
  assert (forall n, (Num.fromInteger 0 + Z.of_nat n)%Z = Z.of_nat n). intros.
  simpl. reflexivity. rewrite H2. clear H2.
  assert (length (u :: p) = (1 + length p)). simpl. reflexivity. rewrite H2. clear H2.
  rewrite Nat2Z.inj_add. assert (Z.of_nat 1 = 1%Z). simpl. reflexivity. rewrite H2.
  assert (forall z1 z2, (z1 + z2 - z1)%Z = z2%Z). intros. omega. rewrite H4. reflexivity. }
  assert (V': valid (bfs_tail (start g v)) g v). destruct (vIn g v) eqn : V.
  eapply multi_valid. apply v_start. apply V. apply bfs_tail_multi. 
  apply bf_invalid_v in V. rewrite V in H. inversion H.
  split.
  - apply zip_in in H. destruct_all. pose proof (level_finds_shortest_path v g u).
    rewrite <- level_tail_equiv in H5. rewrite <- level_tail_equiv in H4. 
      replace (find_dist_list (get_dists (bfs_tail (start g v)))) with
      (find_dist (bfs_tail (start g v))) in H5 by (unfold find_dist_list; reflexivity).
    destruct (find_dist (bfs_tail (start g v)) u) eqn : F.
    + rewrite find_dist_in in F.
      pose proof (no_dup_level v g). rewrite <- level_tail_equiv in H6.
      assert ((List.length (u :: p) -1)%Z = Z.of_nat n).
      eapply NoDup_pairs in H6. apply H6. apply H4. apply F.
      symmetry in H5. apply distance_some in H5. destruct H5 as [l].
      destruct_all.
      eapply shortest_path_of_length. apply H5. apply bft_paths_valid.
      assumption. rewrite H8.
      assert (forall z1 z2 z3, (z1 - z2)%Z = z3%Z -> z1 = (z3 + z2)%Z). intros. omega.
      assert (List.length (u :: p) = (Z.of_nat n + 1)%Z). apply H9. assumption.
      rewrite length_equiv. rewrite H10. rewrite Z2Nat.inj_add. rewrite Nat2Z.id.
      simpl. unfold Pos.to_nat. simpl. reflexivity. omega. omega. apply V'.
    + symmetry in H5. pose proof (output_iff_reachable (bfs_tail (start g v)) g v u).
      unfold distance in H5. assert (exists l, path' g v u l). apply H6.
      assumption. apply bfs_tail_done. rewrite in_map_iff. exists (u, (List.length (u :: p) - 1)%Z).
      simpl. solve_assume. rewrite distance_none in H5. destruct_all. exfalso; apply (H5 x); assumption.
  - rewrite H2. rewrite Nat2Z.id. simpl. omega.
Qed. 

End Bft. 

(** Labelled Paths (lbf) **)
Section Lbft.

Instance need_this_for_equations'''' : WellFounded (bf_measure_list (LPath b)).
Proof.
  unfold WellFounded. apply well_founded_bf_measure_list.
Defined.


Equations lbf' (x :  (list (LPath b)) * (gr a b)) : (RootPath.LRTree b) by wf x (bf_measure_list (LPath b)) :=
  lbf' (nil, g) := nil;
  lbf' ((LP nil :: q'), g) := if (isEmpty g) then nil else GHC.Err.patternFailure;
  lbf' ((LP ((v, l) :: t) :: q'), g) := let p:= (v, l) :: t in  if (isEmpty g) then nil else
      match (match_ v g) as y return ((match_ v g = y) -> _) with
                        | (Some c, g') => fun H : (match_ v g) = (Some c, g') => LP p :: (lbf' ((q' ++ map (fun v' => LP (v' :: p))  (lsuc' c)), g'))
                        | (None, g') => fun H : (match_ v g) = (None, g') => (lbf' (q', g'))
                        end (eq_refl).
Next Obligation.
unfold bf_measure_list. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H.
Defined.
Next Obligation.
unfold bf_measure_list. apply lex2. symmetry. unfold natNodes_eq. eapply match_none_size. apply H. unfold list_length_lt.
simpl. omega.
Defined.

Definition expand_lbf' :=
fun x : list (LPath b) * gr a b =>
let (l, g) := x in
match l with
| nil => fun _ : gr a b => nil
| l0 :: l1 =>
    fun g0 : gr a b =>
    match l0 with
    | LP unLPath =>
        fun (l2 : list (LPath b)) (g1 : gr a b) =>
        match unLPath with
        | nil => fun (_ : list (LPath b)) (g2 : gr a b) => if isEmpty g2 then nil else GHC.Err.patternFailure
        | l3 :: l4 =>
            fun (l5 : list (LPath b)) (g2 : gr a b) =>
            (let (n, b0) := l3 in
             fun (l6 : list (LNode b)) (l7 : list (LPath b)) (g3 : gr a b) =>
             if isEmpty g3
             then nil
             else
              (let (m, g') as y return (match_ n g3 = y -> list (LPath b)) := match_ n g3 in
               match m as m0 return (match_ n g3 = (m0, g') -> list (LPath b)) with
               | Some c =>
                   fun _ : match_ n g3 = (Some c, g') =>
                   LP ((n, b0) :: l6)
                   :: lbf' (l7 ++ map (fun v' : Node * b => LP (v' :: (n, b0) :: l6)) (lsuc' c), g')
               | None => fun _ : match_ n g3 = (None, g') => lbf' (l7, g')
               end) eq_refl) l4 l5 g2
        end l2 g1
    end l1 g0
end g. 


Lemma unfold_lbf' : forall x, lbf' x = expand_lbf' x.
Proof.
  intros. unfold expand_lbf'. apply lbf'_elim. reflexivity. reflexivity. reflexivity.
Qed.

(*Need assumption that q is nonempty, or else queueGet is undefined (and this is OK, bft is called on nonempty queue*)
Lemma lbf_lbf'_equiv: forall g q,
  lbf' ((toList _ q), g) = lbf q g.
Proof.
  intros. remember (toList _ q) as l. remember (l, g) as x. generalize dependent q.
  generalize dependent g. revert l.
  induction (x) as [y IH] using (well_founded_induction (well_founded_bf_measure_list _)).
  intros. destruct y. inversion Heqx; subst. clear Heqx. unfold lbf.
  rewrite unfold_lbf'. simpl. 
   unfold deferredFix2 in *. unfold curry in *.
  rewrite (deferredFix_eq_on _ (fun x => True) ( (bf_measure_queue (_)) )).
  - simpl.  destruct (toList _ q) eqn : Q'. rewrite <- toList_queueEmpty in Q'. rewrite Q'. simpl.
    reflexivity. assert (queueEmpty q = false). destruct (queueEmpty q) eqn : ?.
    rewrite toList_queueEmpty in Heqb0. rewrite Heqb0 in Q'. inversion Q'.
    reflexivity. rewrite H. simpl. destruct (isEmpty g) eqn : E.
    destruct l. destruct unLPath. rewrite E. reflexivity. destruct l. rewrite E. reflexivity. 
    destruct (queueGet q) eqn : G.
    pose proof (toList_queueGet _ _ _ _ Q'). rewrite G in H0. simpl in H0. destruct H0. subst.
    destruct l. destruct unLPath. rewrite E. reflexivity. destruct l. rewrite E.
    destruct (match_ n g) eqn : M. destruct m.
    + unfold lbf in IH. unfold deferredFix2 in IH. unfold curry in IH. erewrite IH. reflexivity.
      apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M. reflexivity.
      rewrite toList_queuePutList . reflexivity.
    + unfold lbf in IH. unfold deferredFix2 in IH. unfold curry in IH. erewrite IH. reflexivity.
      apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M. unfold list_length_lt.
      simpl. omega. reflexivity. reflexivity.
  - apply well_founded_bf_measure_queue.
  - unfold recurses_on. intros. unfold uncurry. destruct x. destruct (queueEmpty q0) eqn : QE. simpl.
    reflexivity. simpl. destruct (isEmpty g1); simpl; try(reflexivity). destruct (queueGet q0) eqn : Q''.
    destruct l; try(reflexivity). destruct unLPath; try reflexivity. destruct l.
    destruct (match_ n g1) eqn : M'. destruct m. rewrite H0.
    reflexivity. auto. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M'.
    rewrite H0. reflexivity. auto. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size.
    apply M'. unfold queue_length_lt. destruct (toList _ q0) eqn : L. rewrite <- toList_queueEmpty in L.
    rewrite L in QE. inversion QE.
    pose proof (toList_queueGet _ _ _ _ L). rewrite Q'' in H1; simpl in H1; destruct H1; subst.
    unfold list_length_lt. simpl. omega.
  - auto.
Qed.

(** ** Correctness of [lbf] **)

(*The correctness property is simple: [lb] is the same as [bf] when we remove the labels*)

Definition unlabel_path (l : LPath b) : Path := 
  match l with
  | LP l' => map fst l'
  end.

Definition unlabel_tree (l : list (LPath b)) : list (Path) :=
  map unlabel_path l.

Lemma unlabel_app: forall l1 l2, unlabel_tree (l1 ++ l2) = unlabel_tree l1 ++ unlabel_tree l2.
Proof.
  intros. unfold unlabel_tree. rewrite map_app. reflexivity.
Qed. 

Lemma lbf_unlabel: forall g q q',
  ~In nil q' ->
  unlabel_tree q = q' ->
  unlabel_tree (lbf' (q, g)) = bf' (q', g).
Proof.
  intros. remember (q, g) as x. generalize dependent q. generalize dependent q'. revert g.
  induction (x) as [y IH] using (well_founded_induction (well_founded_bf_measure_list _)).
  intros. destruct y. inversion Heqx. subst. clear Heqx. rewrite unfold_lbf'.
  rewrite unfold_bf'. simpl. destruct q. simpl. reflexivity.
  simpl. destruct l. simpl. destruct unLPath. simpl. simpl in H. exfalso. apply H.
  left. reflexivity. destruct l. simpl. destruct (isEmpty g) eqn : E. reflexivity.
  destruct (match_ n g) eqn : M. destruct m.
  - simpl. erewrite IH. reflexivity. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry.
    apply M. intro. simpl in H. apply in_app_or in H0. destruct H0.
    apply H. right. assumption. rewrite in_map_iff in H0. destruct_all. inversion H0.
    2: { reflexivity. } simpl. rewrite unlabel_app. 
    assert (unlabel_tree (map (fun v' : Node * b => LP (v' :: (n, b0) :: unLPath)) (lsuc' c)) = 
    map (fun x0 : Node => x0 :: n :: map fst unLPath) (suc' c)). unfold unlabel_tree.
    rewrite map_map. simpl. unfold lsuc'. unfold suc'. unfold Base.op_z2218U__.
    unfold Base.map. unfold Graph.flip2. unfold Tuple.snd. induction (context4l' c).
    simpl. reflexivity. simpl. rewrite IHa0. destruct a0. simpl. reflexivity. rewrite H0. reflexivity.
  - erewrite IH. reflexivity. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size.
    apply M. unfold list_length_lt. simpl. omega. intro. apply H. simpl. right. assumption.
    reflexivity. reflexivity.
Qed.

(*For some reason, if the vertex v has no edges, [lbft] returns a list of nil instead of nil, so
  the property we want only holds if v has at least one outgoing edge*)

Lemma out_fst: forall (g: gr a b) v n m b l,
  out g v = (n, m, b) :: l -> v = n.
Proof.
  intros. unfold out in H. unfold Base.map in H. 
  destruct (context4l g v). simpl in H. inversion H. simpl in H. destruct p. inversion H. subst.
  reflexivity.
Qed.

Theorem lbft_label: forall (g: gr a b) v,
  out g v <> nil ->
  unlabel_tree (lbft v g) = bft v g.
Proof.
  intros. unfold lbft. unfold bft. destruct (out g v) eqn : O. contradiction. destruct l.
  destruct p. rewrite <- lbf_lbf'_equiv. rewrite <- bf_bf'_equiv. apply lbf_unlabel.
  intro. simpl in H0. destruct H0. inversion H0. auto. simpl. apply out_fst in O. subst. reflexivity.
Qed. 

End Lbft.

(** Correctness of [bfen] (BFS with predecessors **)
Section Bfen.

Instance need_this_for_equations''''' : WellFounded (bf_measure_list (Node * Node)).
Proof.
  unfold WellFounded. apply well_founded_bf_measure_list.
Defined.

Equations bfenInternal' (x: (list (Node * Node) * (gr a b))) : list (Node * Node) by wf x (bf_measure_list (Node * Node)) :=
  bfenInternal' (nil, g) := nil;
  bfenInternal' ((u,v) :: vs, g) := if (isEmpty g) then nil else
                                match (match_ v g) as y return ((match_ v g = y) -> _ ) with
                                | (Some c, g') => fun H : (match_ v g) = (Some c, g') => (u,v) :: bfenInternal' (vs ++ (outU c), g')
                                | (None, g') => fun H: (match_ v g) = (None, g') => bfenInternal' (vs, g')
                                 end (eq_refl).
Next Obligation.
unfold bf_measure_list. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H.
Defined.
Next Obligation.
unfold bf_measure_list. apply lex2. symmetry. unfold natNodes_eq. eapply match_none_size. apply H. unfold list_length_lt.
simpl. omega.
Defined.

Definition expand_bfenInternal' := 
fun x : list (Node * Node) * gr a b =>
let (l, g) := x in
match l with
| nil => fun _ : gr a b => nil
| p :: l0 =>
    fun g0 : gr a b =>
    (let (n, n0) := p in
     fun (l1 : list (Node * Node)) (g1 : gr a b) =>
     if isEmpty g1
     then nil
     else
      (let (m, g') as y return (match_ n0 g1 = y -> list (Node * Node)) := match_ n0 g1 in
       match m as m0 return (match_ n0 g1 = (m0, g') -> list (Node * Node)) with
       | Some c => fun _ : match_ n0 g1 = (Some c, g') => (n, n0) :: bfenInternal' (l1 ++ outU c, g')
       | None => fun _ : match_ n0 g1 = (None, g') => bfenInternal' (l1, g')
       end) eq_refl) l0 g0
end g.

Lemma unfold_bfenInternal': forall x,
  bfenInternal' x = expand_bfenInternal' x.
Proof.
  intros. unfold expand_bfenInternal'. apply bfenInternal'_elim. reflexivity. reflexivity.
Qed.

Lemma bfenInternal_bfenInternal'_equiv: forall g q,
  bfenInternal' (toList _ q, g) = bfenInternal q g.
Proof.
  intros. remember (q, g) as x. generalize dependent q. revert g. 
  induction (x) as [y IH] using (well_founded_induction (well_founded_bf_measure_queue _)).
  intros. destruct y. inversion Heqx; subst. clear Heqx. unfold bfenInternal.
  rewrite unfold_bfenInternal'. simpl. 
   unfold deferredFix2 in *. unfold curry in *.
  rewrite (deferredFix_eq_on _ (fun x => True) ( (bf_measure_queue (_)) )).
  - simpl. destruct (toList _ q) eqn : Q. rewrite <- toList_queueEmpty in Q. rewrite Q. simpl.
    destruct (queueGet q) eqn : G. rewrite G. destruct p. reflexivity. destruct p.
    destruct (queueGet q) eqn : QG. rewrite QG. pose proof (toList_queueGet _ _ _ _ Q).
    rewrite QG in H. simpl in H. destruct H. subst.
    destruct (queueEmpty q) eqn : E. rewrite toList_queueEmpty in E. rewrite E in Q. inversion Q.
    rewrite E. clear E. destruct (isEmpty g) eqn : E. simpl. reflexivity.
    simpl. destruct (match_ n0 g) eqn : M. destruct m.
    + unfold bfenInternal in IH. unfold deferredFix2 in IH. unfold curry in IH. erewrite <- IH.
      rewrite toList_queuePutList. reflexivity. 2: { reflexivity. } apply lex1.
      unfold natNodes_lt. eapply match_decr_size. symmetry. apply M.
    + unfold bfenInternal in IH. unfold deferredFix2 in IH. unfold curry in IH. erewrite IH. reflexivity.
      2: { reflexivity. } apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M.
      unfold queue_length_lt. rewrite Q. unfold list_length_lt. simpl. omega.
  - apply well_founded_bf_measure_queue.
  - unfold recurses_on. intros. unfold uncurry. destruct x. destruct (queueGet q0) eqn : Q.
    destruct e. destruct (queueEmpty q0) eqn : E. simpl. reflexivity. destruct (isEmpty g1) eqn : G.
    simpl. reflexivity. simpl. destruct (match_ n0 g1) eqn : M'. destruct m.
    rewrite H0. reflexivity. auto. apply lex1. unfold natNodes_lt. eapply match_decr_size.
    symmetry. apply M'. apply H0. auto. apply lex2. unfold natNodes_eq. symmetry.
    eapply match_none_size. apply M'. unfold queue_length_lt. unfold list_length_lt.
    destruct (toList _ q0) eqn : L. rewrite <- toList_queueEmpty in L. rewrite L in E. inversion E.
    pose proof (toList_queueGet _ _ _ _ L). rewrite Q in H1. simpl in H1. destruct H1. destruct e. inversion H1; subst. simpl. omega.
  - auto.
Qed.

Definition first_two (l: list Node) : option (Node * Node) :=
  match l with
  | x :: y :: t => Some (y,x)
  | _ => None
  end.

(*Maybe - prove this claim for suitably long queues, manually go through 1 iteration in other, prove that
  if we take 1st off of bf' then get (v,v) cons that*)

Lemma bfenInternal_pred: forall g q q',
  (forall x, In x q -> first_two x <> None) ->
  map first_two q = map Some q' ->
  map first_two (bf' (q, g)) = map Some (bfenInternal' (q', g)).
Proof.
  intros. remember (q, g) as x. generalize dependent q. revert q'. revert g. 
  induction (x) as [y IH] using (well_founded_induction (well_founded_bf_measure_list _)).
  intros. destruct y. inversion Heqx. subst. clear Heqx.
  rewrite unfold_bfenInternal'. rewrite unfold_bf'. simpl. destruct q; destruct q'.
  reflexivity. simpl in H0. inversion H0. simpl in H0. inversion H0. simpl in H0. inversion H0.
  destruct l. inversion H2. simpl in H2. destruct l. inversion H2. simpl in H2. inversion H2.
  destruct p. inversion H4; subst. clear H4. 
  destruct (isEmpty g) eqn : E. reflexivity. destruct (match_ n2 g) eqn : M.
  destruct m.
  - simpl. erewrite IH. reflexivity. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M.
    3: { reflexivity. } intros. intro. apply in_app_or in H1. destruct H1.
    apply (H x). right. assumption. assumption. apply in_map_iff in H1. destruct H1. destruct H1. subst.
    simpl in H4. inversion H4. rewrite map_app. rewrite map_app.
    rewrite H3. unfold outU. unfold out'. unfold suc'. destruct c.
    destruct p. destruct p. unfold Base.map. unfold Base.op_z2218U__.
    rewrite snd_equiv. rewrite map_map. rewrite map_map. rewrite map_map. rewrite map_map.
    simpl. rewrite filter_equiv. unfold Base.op_z2218U__ . rewrite snd_equiv.
    assert (map (fun x : b * Node => Some (n2, snd x)) (a0 ++ filter (fun x : b * Node => Base.op_zeze__ (snd x) n) a2) =
    map (fun x : b * Node => Some (toEdge (let '(l0, w) := x in (n, w, l0))))
  (a0 ++ filter (fun x : b * Node => Base.op_zeze__ (snd x) n) a2)).
    induction (a0 ++ filter (fun x : b * Node => Base.op_zeze__ (snd x) n) a2); simpl.
    reflexivity. rewrite IHl0. destruct a3. simpl. eapply match_context in M. destruct M. subst. reflexivity.
    rewrite H1. reflexivity.
  - erewrite IH. reflexivity. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M.
    unfold list_length_lt. simpl. omega. 3: { reflexivity. } intros. apply H. right. assumption.
    assumption.
Qed.

(*The first element in the list is (v,v), but the rest are the first two elements in the path
  returned by [bft]*)
Theorem bfe_pred: forall v (g: gr a b) h t,
  vIn g v = true ->
  bft v g = h :: t ->
  map Some (bfe v g) = Some (v,v) :: map first_two t.
Proof.
  intros. unfold bfe. unfold bft in H0. unfold bfen.
  rewrite <- bf_bf'_equiv in H0. rewrite <- bfenInternal_bfenInternal'_equiv.
  simpl. rewrite unfold_bfenInternal'. rewrite unfold_bf' in H0. simpl in *.
  destruct (isEmpty g) eqn : E. inversion H0. destruct (match_ v g) eqn : M.
  destruct m.
  - simpl in *. inversion H0; subst. erewrite bfenInternal_pred. reflexivity.
    intros. rewrite in_map_iff in H1. destruct_all. intro. subst. simpl in H3. inversion H3.
    unfold suc'. unfold outU. unfold out'. destruct c. destruct p. destruct p.
    unfold Base.map. rewrite snd_equiv. rewrite map_map. rewrite map_map. rewrite map_map.
    unfold Base.op_z2218U__ . eapply match_context in M. destruct M. subst.
    induction (context4l' (a2, n, a1, a0)). simpl. reflexivity. simpl. rewrite IHa3. simpl.
    destruct a3. simpl. reflexivity.
  - epose proof (match_in g v). destruct H1. apply H2 in H. destruct_all. rewrite M in H.  inversion H.
Qed.

End Bfen.

End Ind. 
