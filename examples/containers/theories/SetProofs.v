Require Import GHC.Base.
Require Import HsToCoq.DeferredFix.
Require Import Data.Semigroup.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.
Require Proofs.Data.Foldable.
Require Import Data.Set.Internal.
Import GHC.Num.Notations.
Require Import OrdTactic.
Require Import Psatz.
Require Import CustomTactics.
Require Import SortedUtil.
Require Import Coq.Classes.Morphisms. (* For [Proper] *)
Set Bullet Behavior "Strict Subproofs".

(** This file contains our specifications and proofs for [Data.Set]. The file
consists of the following four parts:

1. definitions, lemmas, and tactics for bounds ([Bound], [Bounded], etc.) and
well-formedness ([Desc], [WF], etc.) of sets, (this part is from the beginning
of the file until the lemma [Desc_WF'])

2. theorems (including lemmas) of many operations of [Data.Set], (this part is
from the theorem [null_spec] until the theorem [mapMonotonic_Desc])

3. proofs that [Data.Set] satisfies certain type class properties, (this part
can be found in section [TypeClassLaws])

4, proofs that [Data.Set] satisfies Coq's [FSetInterface]. (this part can be
found in module [SetFSet]).  *)


(** ** Tactics for pointer equality *)

Ltac destruct_ptrEq := lazymatch goal with
  | |- context [if PtrEquality.ptrEq ?x ?y && PtrEquality.ptrEq ?x2 ?y2 then _ else _]
  => let Hpe := fresh "Hpe" in
     let Hpe1 := fresh "Hpe1" in
     let Hpe2 := fresh "Hpe2" in
     destruct (PtrEquality.ptrEq x y && PtrEquality.ptrEq x2 y2) eqn:Hpe;
     [ rewrite andb_true_iff in Hpe;
       destruct Hpe as [Hpe1 Hpe2];
       apply PtrEquality.ptrEq_eq in Hpe1;
       apply PtrEquality.ptrEq_eq in Hpe2;
       subst
     | clear Hpe]
  | |- context [if PtrEquality.ptrEq ?x ?y then _ else _]
  => let Hpe := fresh "Hpe" in
     destruct (PtrEquality.ptrEq x y) eqn:Hpe;
     [ apply PtrEquality.ptrEq_eq in Hpe; subst
     | clear Hpe]
end.

Section WF.
Context {e : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(** ** Utilities for working with [Ord] *)

Lemma compare_Eq : forall (x y : e),
  compare x y = Eq <-> x == y = true.
Proof. order e. Qed.
Lemma compare_Lt : forall (x y : e),
  compare x y = Lt <-> x < y = true.
Proof. order e. Qed.
Lemma compare_Gt : forall (x y : e),
  compare x y = Gt <-> x > y = true.
Proof. order e. Qed.

Lemma lt_eq_r : forall x y z,
  x < y = true ->
  z == y = true ->
  x < z = true.
Proof. order e. Qed.

Lemma lt_eq_l : forall x y z,
  x < y = true ->
  z == x = true ->
  z < y = true.
Proof. order e. Qed.

Lemma lt_not_eq : forall (x y : e),
  x < y = true -> x == y = false.
Proof. order e. Qed.

Lemma gt_not_eq : forall (x y : e),
 x > y = true -> x == y = false.
Proof. order e. Qed.


Lemma lt_gt : forall (x y : e), (x > y) = (y < x).
Proof. order e. Qed.

Lemma lt_trans : forall (x y z : e),
  x < y = true -> y < z = true -> x < z = true.
Proof. order e. Qed.

(** * Well-formedness *)

(* Bounds may be absent (infinity) *)
Definition bound := (option e)%type.

(** A suitable comparision operator for bounds.
   If someone feels like it, then you may introduce nice notation. *)
Definition isLB : bound -> e -> bool :=
  fun lb e => match lb with
    | Some lb => lb < e
    | None => true
  end.

Definition isUB : bound -> e -> bool :=
  fun ub e => match ub with
    | Some ub => e < ub
    | None => true
  end.

Ltac order_Bounds :=
  intros;
  simpl isUB in *;
  simpl isLB in *;
  repeat (congruence || lazymatch goal with
    | H : isUB ?ub _ = false |- _ => destruct ub; simpl isUB in *
    | |-  isUB ?ub _ = _          => destruct ub; simpl isUB in *
    | H : isLB ?lb _ = false |- _ => destruct lb; simpl isLB in *
    | |-  isLB ?lb _ = _          => destruct lb; simpl isLB in *
   end);
   order e.

Lemma isLB_lt:
  forall lb x y,
  isLB lb x = true->
  x < y = true ->
  isLB lb y = true.
Proof. order_Bounds. Qed.

Lemma isUB_lt:
  forall ub x y,
  isUB ub x = true->
  y < x = true ->
  isUB ub y = true.
Proof. order_Bounds. Qed.

(** This is just like size, but with a type signature that does not confuse [lia] *)
Definition size (s : Set_ e) : Z :=
  match s with | Bin sz _ _ _ => sz
               | Tip => 0 end.

Lemma size_size: Internal.size = size.
Proof. reflexivity. Qed.

(** The balancing property of a binary node *)
Definition balance_prop sz1 sz2 :=
  (sz1 + sz2 <= 1 \/ sz1 <= delta * sz2 /\ sz2 <= delta * sz1)%Z.

(** One precondition for [balanceL]: The left tree has been inserted to (but not by too much).
    This is mechanically derived from the context in the call to [balanceL] in [link], and
    unfortunately not very educational.
 *)
Definition balance_prop_inserted sz1 sz2 :=
  (delta * sz1 <= delta*delta*sz2 + delta*sz2 + sz2 /\ sz2 <= sz1)%Z.

(* NB: this does not work:
Definition balance_prop_inserted sz1 sz2 := balance_prop sz1 sz2.
*)

Fixpoint sem (s : Set_ e) (i : e) : bool :=
  match s with | Bin _ x s1 s2 => sem s1 i || (i == x) || sem s2 i
               | Tip => false end.

Lemma sem_resp_eq : forall s i j,
  i == j = true -> sem s i = sem s j.
Proof.
  intros.
  induction s.
  * simpl.
    rewrite IHs1, IHs2.
    replace (j == a) with (i == a) by order e.
    reflexivity.
  * reflexivity.
Qed.

(** This inductive predicate describes when sets are well-formed within
  (exclusive) bounds.
*)

Inductive Bounded : Set_ e -> bound -> bound -> Prop :=
  | BoundedTip : forall lb ub,
    Bounded Tip lb ub
  | BoundedBin :
    forall lb ub,
    forall s1,
    forall s2,
    forall x sz,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true ->
    sz = (1 + size s1 + size s2)%Z ->
    balance_prop (size s1) (size s2) ->
    Bounded (Bin sz x s1 s2) lb ub.

(** ** Lemmas related to well-formedness *)


(** There are no values outside the bounds *)
Lemma sem_outside_below:
  forall {s lb ub i},
  Bounded s lb ub ->
  isLB lb i = false ->
  sem s i = false.
Proof.
  intros ???? HD ?.
  induction HD; intros; subst; simpl in *; intuition.
  rewrite H2.
  rewrite IHHD2 by order_Bounds.
  rewrite orb_false_l. rewrite orb_false_r. order_Bounds.
Qed.

Lemma sem_outside_above:
  forall {s lb ub i},
  Bounded s lb ub ->
  isUB ub i = false ->
  sem s i = false.
Proof.
  intros ???? HD ?.
  induction HD; intros; subst; simpl in *; intuition.
  rewrite H2.
  rewrite IHHD1 by order_Bounds.
  rewrite orb_false_l. rewrite orb_false_r. order_Bounds.
Qed.

Lemma sem_inside:
  forall {s lb ub i},
  Bounded s lb ub ->
  sem s i = true ->
  isLB lb i = true /\ isUB ub i = true.
Proof.
  intros ???? HD ?.
  induction HD; intros; subst; simpl in *; rewrite ?orb_true_iff in *; intuition;
  order_Bounds.
Qed.


(* We use this as a rewrite rule because
   [simpl (size (Bin _ _ _ _ ))]
   simplifies the [ 1 + _ ] which is annoying. *)
Lemma size_Bin: forall sz x (s1 s2 : Set_ e),
  size (Bin sz x s1 s2) = sz.
Proof. intros. reflexivity. Qed.

Lemma size_nonneg:
  forall {s lb ub},
  Bounded s lb ub -> (0 <= size s)%Z.
Proof.
  intros ??? HD.
  induction HD.
  * simpl. lia.
  * simpl. lia.
Qed.

Ltac postive_sizes :=
  repeat match goal with [ H : Bounded ?s _ _ |- _ ] => pose_new (size_nonneg H) end.

Lemma size_0_iff_tip:
  forall {s lb ub},
  Bounded s lb ub -> (size s = 0)%Z <-> s = Tip.
Proof.
  induction 1.
  * intuition.
  * postive_sizes;
    rewrite ?size_Bin in *.
    intuition try (congruence || lia).
Qed.

(** The main point of the balancing condition: Logarithmic height *)

Fixpoint height (s : Set_ e) : Z := match s with
  | Tip => 0%Z
  | Bin _ _ s1 s2 => (1 + max (height s1) (height s2))%Z
  end.

Lemma height_nonneg:
  forall s, (0 <= height s)%Z.
Proof. induction s; cbn -[Z.add]; lia. Qed.

Ltac postive_heights :=
  repeat match goal with [ s : Set_ e |- _ ] => pose_new (height_nonneg s) end.

Lemma size_height_1:
  forall {s lb ub},
  Bounded s lb ub -> (size s = 1)%Z -> height s = 1%Z.
Proof.
  intros.
  destruct H.
  + inversion H0.
  + destruct H, H1; cbn -[Z.add] in *; postive_sizes; try lia; try reflexivity.
Qed.

Lemma Bounded_size_bound : forall s lb ub,
  Bounded s lb ub -> (4^(height s - 1) <= size s*3^(height s - 1))%Z.
Proof.
  intros ??? HB. induction HB.
  * simpl. reflexivity.
  * cbn -[Z.add].
    postive_sizes.
    postive_heights.
    + unfold balance_prop, delta, fromInteger, Num_Integer__ in H2.
      apply Z.max_case_strong; intro Hle.
      - destruct (Z.leb_spec (size s1 + size s2) 1).
         ** assert (size s1 = 0 \/ size s1 = 1)%Z as Hsmall by lia.
            destruct Hsmall.
            ++ rewrite (size_0_iff_tip HB1) in *. subst. cbn -[N.add Z.add Z.mul] in *.
               simpl Z.sub.
               lia.
            ++ assert (size s2 = 0)%Z by lia.
               rewrite (size_0_iff_tip HB2) in *. subst. cbn -[N.add Z.add Z.mul] in *.
               replace (height s1) with 1%Z in *
                 by (symmetry; eapply size_height_1; eassumption).
               simpl Z.sub.
               lia.
         ** destruct H2; only 1: lia.
            assert (height s1 <> 0%Z)
              by (destruct s1; cbn -[Z.add]; postive_heights; simpl size in *; try lia).
            replace (((1 + height s1) - 1))%Z with (Z.succ (height s1 - 1)) by lia.
            rewrite !Z.pow_succ_r by lia.
            etransitivity; only 1: (apply Z.mul_le_mono_nonneg_l; [lia | eassumption]).
            rewrite !Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; only 1: (apply Z.pow_nonneg; lia).
            lia.
      - destruct (Z.leb_spec (size s1 + size s2) 1).
         ** assert (size s2 = 0 \/ size s2 = 1)%Z as Hsmall by lia.
            destruct Hsmall.
            ++ rewrite (size_0_iff_tip HB2) in *. subst. cbn -[N.add Z.add Z.mul] in *.
               simpl Z.sub.
               lia.
            ++ assert (size s1 = 0)%Z by lia.
               rewrite (size_0_iff_tip HB1) in *. subst. cbn -[N.add Z.add Z.mul] in *.
               replace (height s2) with 1%Z in *
                 by (symmetry; eapply size_height_1; eassumption).
               simpl Z.sub.
               lia.
         ** destruct H2; only 1: lia.
            assert (height s1 <> 0%Z)
              by (destruct s1; cbn -[Z.add]; postive_heights; simpl size in *; try lia).
            replace (((1 + height s2) - 1))%Z with (Z.succ (height s2 - 1)) by lia.
            rewrite !Z.pow_succ_r by lia.
            etransitivity; only 1: (apply Z.mul_le_mono_nonneg_l; [lia | eassumption]).
            rewrite !Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; only 1: (apply Z.pow_nonneg; lia).
            lia.
Qed.

Lemma Z_log2_pow2:
  forall y,
  (0 <= y)%Z ->
  (Z.log2 (y ^ 2) <= 2 * Z.log2 y + 1)%Z.
Proof.
  intros.
  replace (y ^ 2)%Z with (y * y)%Z by lia.
  etransitivity; only 1: (apply Z.log2_mul_above; assumption).
  lia.
Qed.

Lemma Z_log2_pow3:
  forall y,
  (0 <= y)%Z ->
  (Z.log2 (y ^ 3) <= 3 * Z.log2 y + 2)%Z.
Proof.
  intros.
  replace (y ^ 3)%Z with (y^2 * y)%Z by lia.
  assert (0 <= y^2)%Z by (apply Z.pow_nonneg; assumption).
  etransitivity; only 1: (apply Z.log2_mul_above; assumption).
  enough ((Z.log2 (y^2) <= 2 * Z.log2 y + 1)%Z) by lia.
  apply Z_log2_pow2.
  assumption.
Qed.

(* Frustratingly, concluding this lemma from the one above took more time
   than proving that. *)
Lemma Bounded_logarithmic_height : forall s lb ub,
  Bounded s lb ub -> (height s <= 3 * Z.log2 (size s) + 3)%Z.
Proof.
  intros ??? HB.
  pose proof (Bounded_size_bound s lb ub HB).
  postive_heights.
  postive_sizes.
  assert (size s = 0 \/ 0 < size s)%Z by lia. destruct H2.
  * apply (size_0_iff_tip HB) in H2.
    subst. simpl. intro Htmp. inversion Htmp.
  * clear H1.
    enough (height s - 1 <= 3 * Z.log2 (size s) + 2)%Z by lia.
    assert (0 < height s)%Z by (induction HB; cbn -[Z.add] in *; postive_heights; try lia).
    assert (0 <= height s - 1)%Z by lia.
    generalize  dependent (height s - 1)%Z; intros h ??.
    generalize dependent (size s); intros sz ??.
    clear dependent s. clear lb ub. clear dependent e.
    assert (0 < 3 ^ h)%Z by (apply Z.pow_pos_nonneg; lia).
    assert (0 < 4 ^ h)%Z by (apply Z.pow_pos_nonneg; lia).
    assert (0 < sz ^ 3)%Z by (apply Z.pow_pos_nonneg; lia).

    etransitivity; only 2: (apply Z_log2_pow3; lia).
    apply Z.log2_le_pow2; only 1: assumption.

    eapply Zmult_lt_0_le_reg_r. apply H0.
    eapply Zmult_lt_0_le_reg_r. apply H0.
    eapply Zmult_lt_0_le_reg_r. apply H0.
    rewrite <- !Z.pow_mul_l.
    simpl (2 * 3 * 3 * 3)%Z.
    etransitivity. apply Z.pow_le_mono_l with (b := (4^3)%Z). lia.
    rewrite <- Z.pow_mul_r by lia.
    rewrite Z.mul_comm.
    rewrite -> Z.pow_mul_r by lia.
    etransitivity. apply Z.pow_le_mono_l. split. lia. eapply H.
    lia.
Qed.

Lemma Bounded_change_ub:
  forall s lb ub ub',
  Bounded s lb (Some ub) ->
  ub <= ub' = true ->
  Bounded s lb (Some ub').
Proof.
  intros ???? HD Heq.
  remember (Some ub) as ubo.
  induction HD; subst.
  * apply BoundedTip; auto.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    simpl in *.
    order_Bounds.
Qed.

Lemma Bounded_change_lb:
  forall s lb lb' ub,
  Bounded s (Some lb) ub ->
  lb' <= lb = true ->
  Bounded s (Some lb') ub.
Proof.
  intros ???? HD Heq.
  remember (Some lb) as lbo.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    order_Bounds.
Qed.

(* Bounded_change_ub and Bounded_relax_ub could be united with
   a isNonStrictUB predicate *)
Lemma Bounded_relax_ub:
  forall s lb ub ub',
  Bounded s lb (Some ub) ->
  isUB ub' ub = true ->
  Bounded s lb ub'.
Proof.
  intros ???? HD Heq.
  remember (Some ub) as ubo.
  induction HD; subst.
  * apply BoundedTip; auto.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    simpl in *.
    order_Bounds.
Qed.

Lemma Bounded_relax_lb:
  forall s lb lb' ub,
  Bounded s (Some lb) ub ->
  isLB lb' lb = true ->
  Bounded s lb' ub.
Proof.
  intros ???? HD Heq.
  remember (Some lb) as lbo.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    order_Bounds.
Qed.

Lemma Bounded_relax_ub_None:
  forall s lb ub,
  Bounded s lb ub ->
  Bounded s lb None.
Proof.
  intros ??? HD.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * eapply BoundedBin; try eassumption; try reflexivity.
Qed.

Lemma Bounded_relax_lb_None:
  forall s lb ub,
  Bounded s lb ub ->
  Bounded s None ub.
Proof.
  intros ??? HD.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * eapply BoundedBin; try eassumption; try reflexivity.
Qed.

(** ** Tactics for Boundedness etc. *)

(** Learns bounds of values found in some set in the context *)
Ltac inside_bounds :=
  repeat lazymatch goal with
    | H : Bounded ?s _ _, H2 : sem ?s ?i = true |- _ =>
       apply (sem_inside H) in H2; destruct H2
  end.

(** Solve [isLB] and [isUB] goals.  *)
Ltac solve_Bounds := first
  [ eassumption
  | solve [inside_bounds; order_Bounds]
  | idtac "solve_Bounds gave up"
  ].

(* Solve equations of the form
     forall i, f i = f0 i || f1 i
   possibly using equations from the context.
   Fails if it does not start with [forall i,], but may leave a partially solve goal.
    *)
Ltac f_solver_simple  :=
  let i := fresh "i" in
  intro i;
  try reflexivity; (* for when we have an existential variable *)
  repeat multimatch goal with [ H : (forall i, _) |- _] => specialize (H i) end;
  repeat match goal with [ H : ?f = _ |- context [?f i] ] => rewrite H in *; clear H end;
  simpl sem in *; rewrite ?orb_assoc, ?orb_false_r, ?orb_false_l;
  try reflexivity.


(** This auxillary tactic destructs one boolean atom in the argument *)

Ltac split_bool_go expr :=
  lazymatch expr with
    | true       => fail
    | false      => fail
    | Some _     => fail
    | None       => fail
    | match ?x with _ => _ end => split_bool_go x || (simpl x; cbv match)
    | negb ?x    => split_bool_go x
    | ?x && ?y   => split_bool_go x || split_bool_go y
    | ?x || ?y   => split_bool_go x || split_bool_go y
    | xorb ?x ?y => split_bool_go x || split_bool_go y
    | ?bexpr     => destruct bexpr eqn:?
  end.

(** This auxillary tactic destructs one boolean or option atom in the goal *)

Ltac split_bool :=
  match goal with
    | |- ?lhs = ?rhs        => split_bool_go lhs || split_bool_go rhs
    (* A bit ad-hoc, could be improved: *)
    | H : ?x || ?y = true  |- _ => split_bool_go x
    | H : ?x || ?y = false |- _ => split_bool_go x
    | H : ?x && ?y = true  |- _ => split_bool_go x
    | H : ?x && ?y = false |- _ => split_bool_go x
  end.


Ltac f_solver_cleanup :=
  simpl negb in *;
  rewrite ?andb_true_r, ?andb_true_l, ?andb_false_r, ?andb_false_l,
          ?orb_true_r, ?orb_true_l, ?orb_false_r, ?orb_false_l,
          ?orb_assoc, ?and_assoc in *;
  try congruence;
  repeat lazymatch goal with
    |  H1 : true = true |- _ => clear H1
    |  H1 : true = _    |- _ => symmetry in H1
    |  H1 : false = false |- _ => clear H1
    |  H1 : false = _    |- _ => symmetry in H1
  end;
  try solve [exfalso; inside_bounds; order_Bounds];
  try reflexivity;
  try lazymatch goal with
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = true, H3 : sem ?s ?j = false |- _
      => exfalso; rewrite (sem_resp_eq s i j H1) in H2; congruence
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = false, H3 : sem ?s ?j = true |- _
      => exfalso; rewrite (sem_resp_eq s i j H1) in H2; congruence
    |  HProper : Proper ((fun i j : e => i == j = true) ==> eq) ?P,
       H1 : (?i == ?j) = true , H2 : ?P ?i = true, H3 : ?P ?j = false |- _
      => exfalso; rewrite (HProper _ _ H1) in H2; congruence
    |  HProper : Proper ((fun i j : e => i == j = true) ==> eq) ?P,
       H1 : (?i == ?j) = true , H2 : ?P ?i = false, H3 : ?P ?j = true |- _
      => exfalso; rewrite (HProper _ _ H1) in H2; congruence
  end.

Ltac f_solver_step := first
  [ split_bool
  | lazymatch goal with H : context [if ?x == ?y then _ else _] |- _
      => destruct (x == y) eqn:?
    end
  | exfalso
  ].

Ltac f_solver := f_solver_simple; repeat (f_solver_cleanup; f_solver_step).

(** A variant of [lia] that unfolds a few specific things and knows that
   the size of a well-formed tree is positive. *)
Ltac lia_sizes :=
  postive_sizes;
  unfold balance_prop_inserted, balance_prop, delta, ratio in *;
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__,
                      Num_Integer__, Ord_Integer___,
                      op_zg____, op_zl____ in *;
  rewrite ?size_size in *;
  rewrite ?size_Bin in *; simpl (size Tip) in *;
  lia.

(** A tactic to solve questions about size. *)
Ltac solve_size := first
  [ assumption
  | reflexivity
  | lia_sizes
  | idtac "solve_size gave up"
  ].

(** Solve goals of Bounded. Should be back-tracking free, I think. *)
Ltac solve_Bounded := eassumption || lazymatch goal with
  | [ |- Bounded Tip _ _ ]
    => apply BoundedTip
  | [ H : Bounded ?s ?lb (Some ?ub) |- Bounded ?s ?lb (Some ?ub') ]
    => apply (Bounded_change_ub _ _ _ _ H); solve_Bounds
  | [ H : Bounded ?s (Some ?lb) ?ub  |- Bounded ?s (Some ?lb') ?ub ]
    => apply (Bounded_change_lb _ _ _ _ H); solve_Bounds
  | [ H : Bounded ?s ?lb (Some ?ub) |- Bounded ?s ?lb ?ub' ]
    => apply (Bounded_relax_ub _ _ _ _ H); solve_Bounds
  | [ H : Bounded ?s (Some ?lb) ?ub  |- Bounded ?s ?lb' ?ub ]
    => apply (Bounded_relax_lb _ _ _ _ H); solve_Bounds
  | [ |- Bounded (Bin _ _ _ _) _ _ ]
    => apply BoundedBin;
        [ solve_Bounded
        | solve_Bounded
        | solve_Bounds
        | solve_Bounds
        | solve_size
        | solve_size
        ]
  | |- ?H => fail "solve_Bounded gave up on" H
  end.

(** We now have special tactics for the three kinds of preconditions most
    our lemmas below have. So we can write a tactic that correctly chooses the
    right tactic.
    Why not simply use [first [solve_Bounded|solve_Bounds|solve_size]]?
    Because that would involve backtracking which hides error messages from us,
    and is possibly too slow.
  *)

Ltac solve_Precondition := lazymatch goal with
  | |- Bounded _ _ _          => solve_Bounded
  | |- isLB _ _ = true        => solve_Bounds
  | |- isUB _ _ = true        => solve_Bounds
  | |- context [set_size]     => simpl; lia    (* in well-founded recursion *)
  | |- @eq _ ?x ?x            => reflexivity
  | |- @eq Z _ _              => solve_size
  | |- context [balance_prop] => solve_size
  | |- ?H                     => fail "solve_Precondition does not recognize this goal: " H
  end.

(** For every set in the context, try to see if [lia] knows it is empty. *)
Ltac find_Tip :=
  match goal with [ H : Bounded ?s _ _ |- _ ] =>
    assert_new (size s = 0)%Z lia_sizes;
    rewrite (size_0_iff_tip H) in *;
    subst s;
    inversion H;
    clear H;
    subst
  end.


(** ** A setup for complete specification *)

(** A proposition of the form [Desc s lb ub sz f] tells us
  everything we need to know about [s].

  Therefore, it is phrased as an induction lemma which replaces
  the concrete Set (e.g. [insert y s]) with a fresh variable [s'],
  and adds all interesting bits about it to the context.

  To prove a [Desc] statement, use [apply showDesc].

  To use a [Desc] statement, use [applyDesc HD] or [apply foo_Desc].
  *)

Definition Desc s lb ub sz f : Prop :=
  forall (P : Set_ e -> Prop),
  (forall s,
    Bounded s lb ub ->
    size s = sz ->
    (forall i, sem s i = f i) ->
    P s) ->
  P s.

Inductive HIDE (P : Prop) := unhide : P -> HIDE P.
Lemma hide : forall {P : Prop},  HIDE P -> P. Proof. intros. inversion H. assumption. Qed.

Ltac applyDesc lem :=
  apply hide;
  eapply lem;
  [ solve_Precondition ..
  | let s := fresh "s" in
    let HB := fresh "HB" in
    let Hsz := fresh "Hsz" in
    let Hsem := fresh "Hsem" in
    intros s HB Hsz Hsem;
    apply unhide;
    try replace (size s) in *;
    try replace (sem s) in *;
    try assumption
  ].

Lemma showDesc :
  forall s lb ub sz f,
  Bounded s lb ub /\ size s = sz /\ (forall i, sem s i = f i) ->
  Desc s lb ub sz f.
Proof.
  intros. intros P HP.
  apply HP; try intuition.
Qed.

Lemma Desc_change_f:
  forall s lb ub sz f f',
  (forall i, f' i = f i) ->
  Desc s lb ub sz f' <-> Desc s lb ub sz f.
Proof.
  intros.
  split; intro HD; applyDesc HD;
  (apply showDesc; split; [solve_Bounded | split; [solve_size | simpl sem; try solve [f_solver]]]);
  intuition.
Qed.

(** A variant that does not indicate anything about [size]. *)

Definition Desc' s lb ub f : Prop :=
  forall (P : Set_ e -> Prop),
  (forall s,
    Bounded s lb ub ->
    True ->             (* So that we can still use [applyDesc] here *)
    (forall i, sem s i = f i) ->
    P s) ->
  P s.

Lemma showDesc' :
  forall s lb ub f,
  Bounded s lb ub /\ (forall i, sem s i = f i) ->
  Desc' s lb ub f.
Proof.
  intros. intros P HP.
  apply HP; intuition.
Qed.

Ltac solve_Desc :=
 lazymatch goal with
 | |- (Desc _ _ _ _ _)
 => apply showDesc; split; [solve_Bounded | split; [solve_size | simpl sem; try solve [f_solver]]]
 | |- (Desc' _ _ _ _)
 => apply showDesc'; split; [solve_Bounded | simpl sem; try solve [f_solver]]
 | |- ?P
 => fail "solve_Desc: Goal not a Desc or Desc' proposition: " P
 end.

(** ** The actual [WF] predicate *)

(** And any set that has a bounds is well-formed *)
Definition WF (s : Set_ e) : Prop := Bounded s None None.

Lemma Desc_WF:
  forall s sz f,
  Desc s None None sz f -> WF s.
Proof.
  intros ??? HD.
  unfold WF.
  (* Unfortunately, [apply HD] does not work unless we have [size s] and [sem s]
     in the context. *)
  assert (Bounded s None None /\ size s = size s /\ sem s = sem s) by (apply HD; auto).
  intuition.
Qed.


Lemma Desc_WF':
  forall s sz f lb ub,
  Desc s lb ub sz f -> WF s.
Proof.
  intros s sz f lb ub HD.
  unfold WF.
  (* Unfortunately, [apply HD] does not work unless we have [size s] and [sem s]
     in the context. *)
  assert (Bounded s lb ub /\ size s = size s /\ sem s = sem s) by (apply HD; auto).
  intuition.
  destruct ub; destruct lb.
  - eapply Bounded_relax_lb; eauto;
      eapply Bounded_relax_ub; eauto.
  - eapply Bounded_relax_ub; eauto.
  - eapply Bounded_relax_lb; eauto.
  - auto.
Qed.


Require Import Coq.Program.Tactics.

Open Scope Z_scope.

(** ** Verification of [empty] *)

Lemma empty_Desc:
  forall lb ub,
  Desc empty lb ub 0 (fun _ => false).
Proof. intros. unfold empty. solve_Desc. Qed.

Lemma empty_WF: WF empty.
Proof. intros. unfold empty. eapply Desc_WF. apply empty_Desc. Qed.


(** ** Verification of [null] *)

Lemma null_spec:
  forall s, WF s -> null s = true <-> s = Tip.
Proof. intros. unfold null. inversion H; simpl; intuition (congruence || lia_sizes). Qed.


(** ** Verification of [singleton] *)

Lemma singleton_Desc:
  forall x lb ub,
  isLB lb x = true ->
  isUB ub x = true ->
  Desc (singleton x) lb ub 1 (fun i => i == x).
Proof.
  intros.

  unfold singleton.
  unfold fromInteger, Num_Integer__.
  solve_Desc.
Qed.


Lemma singleton_WF:
  forall y, WF (singleton y).
Proof. intros. eapply Desc_WF. eapply singleton_Desc; reflexivity. Qed.

(** ** Verifying the various balancing operations *)

(** *** Verification of [balanceL] *)

Lemma balanceL_Desc:
    forall x s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub  ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) \/
    balance_prop_inserted (size s1 - 1) (size s2) /\ (1 <= size s1)%Z \/
    balance_prop (size s1) (size s2 + 1) ->
    Desc (balanceL x s1 s2) lb ub (1 + size s1 + size s2) (fun i => sem s1 i || (i == x) || sem s2 i).
Proof.
  intros.

  unfold balanceL.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try solve [solve_Desc].
Qed.

Lemma balanceL_noop :
    forall x s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) ->
    balanceL x s1 s2 = Bin (1 + size s1 + size s2) x s1 s2.
Proof.
  intros.

  unfold balanceL.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try reflexivity.
Qed.

(** *** Verification of [balanceR] *)

Lemma balanceR_Desc:
    forall x s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) \/
    balance_prop_inserted (size s2 - 1) (size s1) /\ (1 <= size s2)%Z  \/
    balance_prop (size s1 + 1) (size s2) ->
    Desc (balanceR x s1 s2) lb ub (1 + size s1 + size s2) (fun i => sem s1 i || (i == x) || sem s2 i).
Proof.
  intros.

  unfold balanceR.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try solve [solve_Desc].
Qed.

Lemma balanceR_noop :
    forall x s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) ->
    balanceR x s1 s2 = Bin (1 + size s1 + size s2) x s1 s2.
Proof.
  intros.

  unfold balanceR.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try reflexivity.
Qed.


(** *** Verification of [insertMax] *)

Lemma insertMax_Desc:
    forall x s1 lb ub,
    Bounded s1 lb (Some x) ->
    isLB lb x = true ->
    isUB ub x = true->
    Desc (insertMax x s1) lb ub (1 + size s1) (fun i => sem s1 i || (i == x)).
Proof.
  intros.

  remember (Some x) as ub'. revert dependent x.
  induction H; intros; subst; cbn - [Z.add].
  * applyDesc singleton_Desc.
    solve_Desc.
  * clear IHBounded1.
    applyDesc IHBounded2.
    applyDesc balanceR_Desc.
    solve_Desc.
Qed.

(** *** Verification of [insertMin] *)

Lemma insertMin_Desc:
    forall x s2 lb ub,
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    Desc (insertMin x s2) lb ub (1 + size s2) (fun i => (i == x) || sem s2 i).
Proof.
  intros.
  remember (Some x) as ub'. revert dependent x.
  induction H; intros; subst; cbn - [Z.add].
  * applyDesc singleton_Desc.
    solve_Desc.
  * clear IHBounded2.
    applyDesc IHBounded1.
    applyDesc balanceL_Desc.
    solve_Desc.
Qed.

(** *** Verification of [link] *)

Lemma link_eq (x : e) (s1: Set_ e)  (s2: Set_ e) :
  link x s1 s2 =
       match s1, s2 with
          | Tip , r => insertMin x r
          | l , Tip => insertMax x l
          | (Bin sizeL y ly ry as l) , (Bin sizeR z lz rz as r) =>
            if Sumbool.sumbool_of_bool ((delta GHC.Num.* sizeL) GHC.Base.< sizeR)
            then balanceL z (link x l lz) rz
            else if Sumbool.sumbool_of_bool  ((delta GHC.Num.* sizeR) GHC.Base.< sizeL)
                 then balanceR y ly (link x ry r)
                 else bin x l r
        end.
Proof.
  unfold link at 1, link_func at 1.
  destruct s1; only 2: reflexivity.
  destruct s2; only 2: reflexivity.
  lazymatch goal with
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs =>
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.

(* [program_simpl] calls [simpl], which is very confusing due to [1 + _]. So
ask [Next Obligation] to use this only when it solves the goal completely. *)
Local Obligation Tactic := try solve [program_simpl].

Program Fixpoint link_Desc (x : e) (s1: Set_ e)  (s2: Set_ e)
  {measure (set_size s1 + set_size s2)} :
    forall lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub  ->
    isLB lb x = true ->
    isUB ub x = true->
    Desc (link x s1 s2) lb ub (1 + size s1 + size s2) (fun i => sem s1 i || (i == x) || sem s2 i)
    := _.
Next Obligation.
  intros.
  rewrite link_eq.
  inversion H; subst; clear H;
  inversion H0; subst; clear H0.
  * simpl insertMin.
    applyDesc singleton_Desc.
    solve_Desc.
  * applyDesc insertMin_Desc.
    solve_Desc.
  * applyDesc insertMax_Desc.
    solve_Desc.
  * destruct (Sumbool.sumbool_of_bool _);
    only 2: destruct (Sumbool.sumbool_of_bool _);
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
    - applyDesc link_Desc.
      applyDesc balanceL_Desc.
      solve_Desc.
    - applyDesc link_Desc.
      applyDesc balanceR_Desc.
      solve_Desc.
    - clear link_Desc.
      unfold bin.
      solve_Desc.
Qed.

(** ** Verification of [member] *)

Lemma member_spec:
 forall {s lb ub i}, Bounded s lb ub -> member i s = sem s i.
Proof.
  intros ???? HB.
  induction HB.
  * simpl. reflexivity.
  * subst; simpl.
    destruct (compare i x) eqn:?.
    + replace (i == x) with true by order_Bounds.
      rewrite orb_true_r.
      reflexivity.
    + replace (i == x) with false by order_Bounds.
      rewrite IHHB1.
      rewrite (sem_outside_below HB2) by order_Bounds.
      rewrite !orb_false_r.
      reflexivity.
    + replace (i == x) with false by order_Bounds.
      rewrite IHHB2.
      rewrite (sem_outside_above HB1) by order_Bounds.
      rewrite orb_false_l.
      reflexivity.
Qed.

(** ** Verification of [notMember] *)

Lemma notMember_spec:
 forall {s lb ub i}, Bounded s lb ub -> notMember i s = negb (sem s i).
Proof.
  intros ???? HB.
  unfold notMember, op_zd__.
  erewrite member_spec by eassumption.
  reflexivity.
Qed.


(** ** Verification of [insert] *)

(* The [orig] passing and the local fixpoint in insert is plain ugly, so let’s to this instead *)

Fixpoint insert' (x : e) (s : Set_ e ) : Set_ e :=
  match s with
    | Tip => singleton x
    | Bin sz y l r => match compare x y with
      | Lt =>
        let l' := insert' x l in
        if PtrEquality.ptrEq l' l then s else balanceL y l' r
      | Gt =>
        let r' := insert' x r in
        if PtrEquality.ptrEq r' r then s else balanceR y l r'
      | Eq =>
        if PtrEquality.ptrEq x y then s else Bin sz x l r
     end
  end.

Lemma insert_insert' : forall x s, insert x s = insert' x s.
Proof.
  intros.
  unfold insert.
  induction s; simpl.
  * destruct (compare x a).
    - reflexivity.
    - rewrite IHs1. reflexivity.
    - rewrite IHs2. reflexivity.
  * reflexivity.
Qed.

Lemma insert_Desc:
  forall y s lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insert y s) lb ub (if sem s y then size s else (1 + size s)%Z) (fun i => (i == y) || sem s i).
Proof.
  intros ???? HB HLB HUB.

  rewrite insert_insert'.
  induction HB; intros.
  * simpl.
    applyDesc singleton_Desc; try eassumption; solve_Desc.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in *.
      rewrite Heqc.
      rewrite ?orb_true_r, ?orb_true_l.
      destruct_ptrEq.
      - solve_Desc.
      - unfold Datatypes.id.
        solve_Desc.
    + clear IHHB2.
      applyDesc IHHB1.

      rewrite (sem_outside_below HB2) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      rewrite ?orb_false_r, ?orb_false_l.

      destruct_ptrEq.
      - replace (sem s1 y) with true
           by (destruct (sem s1 y) eqn:?; auto; exfalso; lia).
        solve_Desc.
      - destruct (sem s1 y);
        applyDesc balanceL_Desc;
        solve_Desc.
    + (* more or less a copy-n-paste from above *)
      clear IHHB1.
      applyDesc IHHB2.

      rewrite (sem_outside_above HB1) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      rewrite ?orb_false_r, ?orb_false_l.

      destruct_ptrEq.
      - replace (sem s2 y) with true
           by (destruct (sem s2 y) eqn:?; auto; exfalso; lia).
        solve_Desc.
      - destruct (sem s2 y);
        applyDesc balanceR_Desc;
        solve_Desc.
Qed.

(** ** Verification of [insertR] *)

(** For our purposes, [insertR] and [insert] are equivalent (the sets
    are equal up to [==] of elements. *)

Fixpoint insertR' (x : e) (s : Set_ e ) : Set_ e :=
  match s with
    | Tip => singleton x
    | Bin sz y l r => match compare x y with
      | Lt =>
        let l' := insertR' x l in
        if PtrEquality.ptrEq l' l then s else balanceL y l' r
      | Gt =>
        let r' := insertR' x r in
        if PtrEquality.ptrEq r' r then s else balanceR y l r'
      | Eq => Bin sz y l r
     end
  end.

Lemma insertR_insertR' : forall x s, insertR x s = insertR' x s.
Proof.
  intros.
  unfold insertR.
  induction s; simpl.
  * destruct (compare x a).
    - reflexivity.
    - rewrite IHs1. reflexivity.
    - rewrite IHs2. reflexivity.
  * reflexivity.
Qed.


Lemma insertR_Desc:
  forall y s lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insertR y s) lb ub (if sem s y then size s else (1 + size s)%Z) (fun i => (i == y) || sem s i).
Proof.
  intros ???? HB HLB HUB.

  rewrite insertR_insertR'.
  induction HB; intros.
  * simpl.
    applyDesc singleton_Desc; try eassumption; solve_Desc.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in *.
      rewrite Heqc.
      rewrite ?orb_true_r, ?orb_true_l.
      solve_Desc.
    + clear IHHB2.
      applyDesc IHHB1.

      rewrite (sem_outside_below HB2) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      rewrite ?orb_false_r, ?orb_false_l.

      destruct_ptrEq.
      - replace (sem s1 y) with true
           by (destruct (sem s1 y) eqn:?; auto; exfalso; lia).
        solve_Desc.
      - destruct (sem s1 y);
        applyDesc balanceL_Desc;
        solve_Desc.
    + (* more or less a copy-n-paste from above *)
      clear IHHB1.
      applyDesc IHHB2.

      rewrite (sem_outside_above HB1) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      rewrite ?orb_false_r, ?orb_false_l.

      destruct_ptrEq.
      - replace (sem s2 y) with true
           by (destruct (sem s2 y) eqn:?; auto; exfalso; lia).
        solve_Desc.
      - destruct (sem s2 y);
        applyDesc balanceR_Desc;
        solve_Desc.
Qed.


Lemma insert_WF:
  forall y s, WF s -> WF (insert y s).
Proof. intros. eapply Desc_WF. eapply insert_Desc; try reflexivity; try assumption. Qed.

(** ** Verification of [maxViewSure] *)

Lemma maxViewSure_Desc:
  forall sz' x s1 s2 lb ub,
    Bounded (Bin sz' x s1 s2) lb ub ->
    forall P,
    (forall y r,
      ((y == x) = true \/ sem s2 y = true) /\
      Desc r lb (Some y) (size s1 + size s2)
                         (fun i => (sem s1 i || (i == x) || sem s2 i) && negb (i == y)) ->
      P (y, r)) ->
    P (maxViewSure x s1 s2).
    (* we know that y is in the input, and we actually know more: it is x or in s2 *)
Proof.
  intros ?????? HB.
  revert sz' x s1 lb ub HB.
  induction s2; intros sz' x s1 lb ub HB;subst.
  - clear IHs2_1.
    simpl.
    intros X HX; rewrite (surjective_pairing (maxViewSure _ _ _)). apply HX; clear X HX.

    inversion HB; subst; clear HB.
    inversion H4; subst.

    eapply IHs2_2; only 1: solve_Bounded; intros y r H; destruct H as [Hthere IHD]; clear IHs2_2.
    cbn -[Z.add size] in *; rewrite size_Bin in *.

    applyDesc IHD; clear IHD.

    split.
    + rewrite <- !orb_assoc. right. destruct Hthere as [H|H]; rewrite H;
      rewrite ?orb_true_r, ?orb_true_r; reflexivity.
    + destruct Hthere; applyDesc balanceL_Desc; solve_Desc.
  - intros X HX; rewrite (surjective_pairing (maxViewSure _ _ _)). apply HX; clear X HX.
    cbn -[Z.add size] in *.
    inversion HB; subst; clear HB.
    rewrite Eq_refl.
    split; [left; reflexivity | solve_Desc].
Qed.

(** ** Verification of [lookupMin] *)

Lemma lookupMinSure_Desc:
  forall s x lb ub,
    Bounded s lb ub ->
    let y := lookupMinSure x s in
    ((forall i, sem s i = false) /\ y = x \/
     sem s y = true /\ (forall i, sem s i = true -> (y GHC.Base.<= i) = true)).
Proof.
  intros ???? HD. revert x.
  induction HD. intro x.
  * left. simpl. intuition.
  * right. clear IHHD2.
    simpl.
    destruct (IHHD1 x) as [[??]|[??]]; clear IHHD1.
    - rewrite H4. clear H4.
      setoid_rewrite H3. clear H3.
      rewrite Eq_refl. split; only 1: reflexivity.
      intros i Hi.
      rewrite orb_false_l in *.
      rewrite orb_true_iff in Hi. destruct Hi.
      + order_Bounds.
      + repeat (f_solver_step; f_solver_cleanup).
    - rewrite H3. split; only 1: reflexivity.
      intros i Hi.
      rewrite !orb_true_iff in Hi. decompose [or] Hi; clear Hi.
      + intuition.
      + repeat (f_solver_step; f_solver_cleanup).
      + repeat (f_solver_step; f_solver_cleanup).
Qed.

Lemma lookupMin_Desc:
  forall s lb ub,
    Bounded s lb ub ->
    match lookupMin s with
      | None => (forall i, sem s i = false)
      | Some y => sem s y = true /\ (forall i, sem s i = true -> (y GHC.Base.<= i) = true)
    end.
Proof.
  intros.
  unfold lookupMin. unfold op_zdzn__.
  inversion H; subst; clear H.
  * reflexivity.
  * simpl.
    destruct (lookupMinSure_Desc s1 x lb (Some x) H0) as [[??]|[??]].
    - rewrite H4. clear H4.
      setoid_rewrite H. clear H.
      rewrite Eq_refl. split; only 1: reflexivity.
      intros i Hi.
      rewrite orb_false_l in *.
      rewrite orb_true_iff in Hi. destruct Hi.
      + order_Bounds.
      + repeat (f_solver_step; f_solver_cleanup).
    - rewrite H. split; only 1: reflexivity.
      intros i Hi.
      rewrite !orb_true_iff in Hi. decompose [or] Hi; clear Hi.
      + intuition.
      + repeat (f_solver_step; f_solver_cleanup).
      + repeat (f_solver_step; f_solver_cleanup).
Qed.

(** ** Verification of [lookupMax] *)

Lemma lookupMaxSure_Desc:
  forall s x lb ub,
    Bounded s lb ub ->
    let y := lookupMaxSure x s in
    ((forall i, sem s i = false) /\ y = x \/
     sem s y = true /\ (forall i, sem s i = true -> (i GHC.Base.<= y) = true)).
Proof.
  intros ???? HD. revert x.
  induction HD. intro x.
  * left. simpl. intuition.
  * right. clear IHHD1.
    simpl.
    destruct (IHHD2 x) as [[??]|[??]]; clear IHHD2.
    - rewrite H4. clear H4.
      setoid_rewrite H3. clear H3.
      rewrite Eq_refl, !orb_true_r.
      split; only 1: reflexivity.
      intros i Hi.
      rewrite orb_false_r in *.
      rewrite orb_true_iff in Hi. destruct Hi.
      + repeat (f_solver_step; f_solver_cleanup).
      + order_Bounds.
    - rewrite H3, !orb_true_r. split; only 1: reflexivity.
      intros i Hi.
      rewrite !orb_true_iff in Hi. decompose [or] Hi; clear Hi.
      + repeat (f_solver_step; f_solver_cleanup).
      + repeat (f_solver_step; f_solver_cleanup).
      + intuition.
Qed.

Lemma lookupMax_Desc:
  forall s lb ub,
    Bounded s lb ub ->
    match lookupMax s with
      | None => (forall i, sem s i = false)
      | Some y => sem s y = true /\ (forall i, sem s i = true -> (i GHC.Base.<= y) = true)
    end.
Proof.
  intros.
  unfold lookupMax. unfold op_zdzn__.
  inversion H; subst; clear H.
  * reflexivity.
  * simpl.
    destruct (lookupMaxSure_Desc s2 x (Some x) ub H1) as [[??]|[??]].
    - rewrite H4. clear H4.
      setoid_rewrite H. clear H.
      rewrite Eq_refl, orb_true_r. split; only 1: reflexivity.
      intros i Hi.
      rewrite orb_false_r in *.
      rewrite orb_true_iff in Hi. destruct Hi.
      + repeat (f_solver_step; f_solver_cleanup).
      + order_Bounds.
    - rewrite H, !orb_true_r. split; only 1: reflexivity.
      intros i Hi.
      rewrite !orb_true_iff in Hi. decompose [or] Hi; clear Hi.
      + repeat (f_solver_step; f_solver_cleanup).
      + repeat (f_solver_step; f_solver_cleanup).
      + intuition.
Qed.


(** ** Verification of [minViewSure] *)

Lemma minViewSure_Desc:
  forall sz' x s1 s2 lb ub,
    Bounded (Bin sz' x s1 s2) lb ub ->
    forall P,
    (forall y r,
      ((y == x) = true \/ sem s1 y = true) /\
      Desc r (Some y) ub (size s1 + size s2)
                         (fun i => (sem s1 i || (i == x) || sem s2 i) && negb (i == y)) ->
      P (y, r)) ->
    P (minViewSure x s1 s2).
    (* we know that y is in the input, and we actually know more: it is x or in s2 *)
Proof.
  intros ?????? HB.
  revert sz' x s2 lb ub HB.
  induction s1; intros sz' x s2 lb ub HB;subst.
  - clear IHs1_2.
    simpl.
    intros X HX; rewrite (surjective_pairing (minViewSure _ _ _)). apply HX; clear X HX.

    inversion HB; subst; clear HB.
    inversion H3; subst.

    eapply IHs1_1; only 1: solve_Bounded; intros y r [Hthere IHD]; clear IHs1_1.
    cbn -[Z.add size] in *; rewrite size_Bin in *.

    applyDesc IHD; clear IHD.

    split.
    + rewrite <- !orb_assoc. right. destruct Hthere as [H|H]; rewrite H;
      rewrite ?orb_true_r, ?orb_true_r; reflexivity.
    + destruct Hthere; applyDesc balanceR_Desc; solve_Desc.
  - intros X HX; rewrite (surjective_pairing (minViewSure _ _ _)). apply HX; clear X HX.
    cbn -[Z.add size] in *.
    inversion HB; subst; clear HB.
    rewrite Eq_refl.
    split; [left; reflexivity | solve_Desc].
Qed.

(** ** Verification of [maxView] *)

Lemma maxView_Desc:
  forall s lb ub,
    Bounded s lb ub ->
    forall (P : option (e * Set_ e) -> Prop),
    (forall y r,
      (sem s y = true) /\
      Desc r lb (Some y) (size s - 1) (fun i => sem s i && negb (i == y)) ->
      P (Some (y, r))) ->
    ((forall i, sem s i = false) -> P None) ->
    P (maxView s).
Proof.
  intros ??? HB P HSome HNone.
  unfold maxView.
  inversion HB; subst.
  * apply HNone. intro; reflexivity.
  * unfold op_zdzn__, Datatypes.id, op_zd__.
    eapply maxViewSure_Desc; only 1: eassumption.
    intros y r [??].
    apply HSome.
    split.
    - simpl. rewrite !orb_true_iff. intuition.
    - applyDesc H5. solve_Desc.
Qed.

(** ** Verification of [minView] *)

Lemma minView_Desc:
  forall s lb ub,
    Bounded s lb ub ->
    forall (P : option (e * Set_ e) -> Prop),
    (forall y r,
      (sem s y = true) /\
      Desc r (Some y) ub (size s - 1) (fun i => sem s i && negb (i == y)) ->
      P (Some (y, r))) ->
    ((forall i, sem s i = false) -> P None) ->
    P (minView s).
Proof.
  intros ??? HB P HSome HNone.
  unfold minView.
  inversion HB; subst.
  * apply HNone. intro; reflexivity.
  * unfold op_zdzn__, Datatypes.id, op_zd__.
    eapply minViewSure_Desc; only 1: eassumption.
    intros y r [??].
    apply HSome.
    split.
    - simpl. rewrite !orb_true_iff. intuition.
    - applyDesc H5. solve_Desc.
Qed.


(** ** Verification of [glue] *)

Lemma glue_Desc:
  forall s1 s2 lb ub x,
  Bounded s1 lb (Some x) ->
  Bounded s2 (Some x) ub ->
  isLB lb x = true ->
  isUB ub x = true ->
  balance_prop (size s1) (size s2) ->
  Desc (glue s1 s2) lb ub ((size s1 + size s2)%Z) (fun i => sem s1 i || sem s2 i).
Proof.
  intros ????? HB1 HB2 ???.

  inversion HB1; inversion HB2; subst; cbn -[Z.add]; clear HB1 HB2.
  1-3: solve [solve_Desc|solve_size].
  destruct (Z.ltb_spec (1 + size s4 + size s5) (1 + size s0 + size s3)).
  - eapply maxViewSure_Desc; only 1: solve_Bounded.
    intros y r [Hthere HD].
    applyDesc HD.
    destruct Hthere; applyDesc balanceR_Desc; solve_Desc.
  - eapply minViewSure_Desc; only 1: solve_Bounded.
    intros y r [Hthere HD].
    applyDesc HD.
    destruct Hthere; applyDesc balanceL_Desc; solve_Desc.
Qed.

(** ** Verification of [delete] *)

Lemma delete_Desc :
  forall x s lb ub,
  Bounded s lb ub ->
  Desc (delete x s) lb ub (if sem s x then (size s - 1) else size s) (fun i => sem s i && negb (i == x)).
Proof.
  intros ???? HB.
  induction HB; intros; subst.
  - simpl. solve_Desc.
  - cbn -[Z.add].
    destruct (compare x x0) eqn:Heq.
    + replace (x == x0) with true by solve_Bounds.
      rewrite ?orb_true_r, ?orb_true_l.
      applyDesc glue_Desc.
      solve_Desc.
    + applyDesc IHHB1; clear IHHB1 IHHB2.
      replace (x == x0) with false by solve_Bounds.
      rewrite -> (sem_outside_below HB2) by solve_Bounds.
      rewrite ?orb_false_r.
      destruct_ptrEq.
      * replace (sem s1 x) with false by (destruct (sem s1 x); try congruence; lia).
        solve_Desc.
      * destruct (sem s1 x); applyDesc balanceR_Desc; solve_Desc.
    + applyDesc IHHB2; clear IHHB1 IHHB2.
      replace (x == x0) with false by solve_Bounds.
      rewrite -> (sem_outside_above HB1) by solve_Bounds.
      rewrite ?orb_false_l.
      destruct_ptrEq.
      * replace (sem s2 x) with false by (destruct (sem s2 x); try congruence; lia).
        solve_Desc.
      * destruct (sem s2 x); applyDesc balanceL_Desc; solve_Desc.
Qed.

(** ** Verification of [deleteMin] *)

(** It is hard to phrase this without refering to [lookupMin] *)

Lemma deleteMin_Desc :
  forall s lb ub,
  Bounded s lb ub ->
  deleteMin s = match lookupMin s with | None => s
                                       | Some x => delete x s end.
Proof.
  intros ??? HD.
  induction HD.
  * reflexivity.
  * clear IHHD2.
    cbn [deleteMin].
    rewrite IHHD1; clear IHHD1.

    destruct s1 eqn:?.
    + replace (lookupMin (Bin sz x (Bin s3 e0 s4 s5) s2)) with (lookupMin (Bin s3 e0 s4 s5)) by reflexivity.
      rewrite <- Heqs in *. clear  s3 e0 s4 s5 Heqs.

      pose proof (lookupMin_Desc s1 lb (Some x) HD1) as Hlookup.
      destruct (lookupMin s1) as [ex|].
      - destruct Hlookup as [Hthere Hextrem].
        simpl.
        apply (sem_inside HD1) in Hthere. destruct Hthere.
        replace (compare ex x) with Lt by (symmetry; solve_Bounds).
        ** destruct_ptrEq.
           ++ rewrite Hpe. clear Hpe.
              eapply balanceR_noop; try eassumption.
           ++ reflexivity.
       - rewrite H1.
          eapply balanceR_noop; try eassumption.
   + simpl.
     replace (compare x x) with Eq by (symmetry; order e).
     reflexivity.
Qed.

Import ListNotations.

Lemma foldr_const_append:
  forall xs (s : Set_ e),
  foldr cons xs s = toList s ++ xs.
Proof.
  intros. revert xs. induction s; intros xs.
  * unfold toList, toAscList.
    simpl.
    rewrite !IHs2, !IHs1.
    rewrite app_nil_r.
    rewrite <- !app_assoc.
    reflexivity.
  * reflexivity.
Qed.

Lemma deleteMin_spec n x (l r : Set_ e) :
  toList (deleteMin (Bin n x l r)) = tl (toList (Bin n x l r)).
Proof.
  unfold toList, toAscList.
  generalize dependent (@nil e).
  generalize dependent r.
  generalize dependent x.
  generalize dependent n.
  induction r; intros; auto.
  simpl in *.
  rewrite <- IHr1.
Abort.

(** ** Verification of [deleteMax] *)

(** It is hard to phrase this without refering to [lookupMax] *)

Lemma deleteMax_Desc :
  forall s lb ub,
  Bounded s lb ub ->
  deleteMax s = match lookupMax s with | None => s
                                       | Some x => delete x s end.
Proof.
  intros ??? HD.
  induction HD.
  * reflexivity.
  * clear IHHD1.
    cbn [deleteMax].
    rewrite IHHD2; clear IHHD2.

    destruct s2 eqn:?.
    + replace (lookupMax (Bin sz x s1 (Bin s3 e0 s4 s5))) with (lookupMax (Bin s3 e0 s4 s5)) by reflexivity.
      rewrite <- Heqs in *. clear  s3 e0 s4 s5 Heqs.

      pose proof (lookupMax_Desc s2 (Some x) ub HD2) as Hlookup.
      destruct (lookupMax s2) as [ex|].
      - destruct Hlookup as [Hthere Hextrem].
        simpl.
        apply (sem_inside HD2) in Hthere. destruct Hthere.
        replace (compare ex x) with Gt by (symmetry; solve_Bounds).
        ** destruct_ptrEq.
           ++ rewrite Hpe. clear Hpe.
              eapply balanceL_noop; try eassumption.
           ++ reflexivity.
       - rewrite H1.
          eapply balanceL_noop; try eassumption.
   + simpl.
     replace (compare x x) with Eq by (symmetry; order e).
     destruct s1; reflexivity.
Qed.


(** ** Verification of [splitS] *)

Lemma splitS_Desc :
  forall x s lb ub,
  Bounded s lb ub ->
  forall (P : Set_ e * Set_ e -> Prop),
  (forall s1 s2,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    size s = size s1 + size s2 + (if sem s x then 1 else 0) ->
    (forall i, sem s i = (if i == x then sem s i else sem s1 i || sem s2 i)) ->
    P (s1, s2)) ->
  P (splitS x s) : Prop.
Proof.
  intros ?? ?? HB.
  Ltac solveThis := intros X HX; apply HX; clear X HX; [solve_Bounded|solve_Bounded| |f_solver].
  induction HB.
  - solveThis. reflexivity.
  - simpl.
    destruct (compare x x0) eqn:?.
  + solveThis. replace (x == x0) with true by order e.
    rewrite orb_true_r. simpl. lia.
  + apply IHHB1; intros s1_2 s1_3 HB1_2 HB1_3 Hsz Hsems1; clear IHHB1 IHHB2.
    applyDesc link_Desc.
    solveThis. destruct (sem s1 x).
    * simpl. lia.
    * replace (x == x0) with false by order e. simpl.
      rewrite (sem_outside_below HB2) by solve_Bounds. lia.
  + apply IHHB2; intros s2_2 s2_3 HB2_2 HB2_3 Hsz Hsems2; clear IHHB1 IHHB2.
    applyDesc link_Desc.
    solveThis. destruct (sem s2 x).
    * rewrite orb_true_r. lia.
    * replace (x == x0) with false by order e. simpl.
      rewrite (sem_outside_above HB1) by solve_Bounds. simpl. lia.
Qed.

(** ** Verification of [union] *)

(* The [union] uses some nested pattern match that expand to a very large
   number of patterns in Coq. So let’s take them apart here *)
Lemma union_destruct :
  forall (P : Set_ e -> Prop),
  forall s1 s2,
  (s2 = Tip -> P s1) ->
  (s1 = Tip -> P s2) ->
  (forall x l r, (s2 = Bin 1 x l r) -> P (insertR x s1)) ->
  (forall x l r, (s1 = Bin 1 x l r) -> P (insert x s2)) ->
  (forall sz1 x l1 r1, (s1 = Bin sz1 x l1 r1) ->
    P (
      match splitS x s2 with
      | pair l2 r2 =>
      match union r1 r2 with
      | r1r2 =>
      match union l1 l2 with
      | l1l2 => if andb  (PtrEquality.ptrEq l1l2 l1)
                         (PtrEquality.ptrEq r1r2 r1) : bool
                then s1 else link x l1l2 r1r2
      end end end)) ->
  P (union s1 s2).
Proof.
  intros P s1 s2 HTipR HTipL HSingletonR HSingletonL HBins.
  destruct s1, s2; simpl union;
  unfold op_zeze__, Eq_Integer___, op_zeze____;
  try destruct (Z.eqb_spec s0 1);
  try destruct (Z.eqb_spec s 1); subst;
  first [ eapply HBins; reflexivity
        | eapply HSingletonL; reflexivity
        | eapply HSingletonR; reflexivity
        | eapply HTipL; reflexivity
        | eapply HTipR; reflexivity
        | idtac
        ].
Qed.

Lemma union_Desc :
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Desc' (union s1 s2) lb ub (fun i => sem s1 i || sem s2 i).
(* We use [Desc'] here, because the result of [union] is passed to [link], which
   does a full rebalance, and hence does not need to know anything about the size.
   If it turns out we need [size (union s1 s2)], we can still add it.
*)
Proof.
  intros ???? HB1 HB2.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  * apply union_destruct; intros; subst; try congruence.
    + solve_Desc.
    + solve_Desc.
    + inversion HB3; subst; clear HB3.
      repeat find_Tip.
      (* We need to give [applyDesc] a hint about the bounds that we care about: *)
      assert (Bounded Tip lb ub) by constructor.
      applyDesc insertR_Desc.
      solve_Desc.
  * apply union_destruct; intros; subst; try congruence.
    + solve_Desc.
    + inversion HB3; subst; clear HB3.
      repeat find_Tip.
      applyDesc insertR_Desc.
      solve_Desc.
    + remember (1 + _ + _). inversion H3; subst; clear H3.
      repeat find_Tip.
      applyDesc insert_Desc. solve_Desc.
    + inversion H3; subst; clear H3.
      eapply splitS_Desc; try eassumption.
      intros.
      applyDesc IHHB1_1.
      applyDesc IHHB1_2.
      destruct_ptrEq.
      - solve_Desc.
      - applyDesc link_Desc.
        solve_Desc.
Qed.

(** ** Verification of [unions] *)

(* This is a bit of a lazy specification, but goes a long way *)

Lemma Forall_rev:
  forall A P (l : list A), Forall P (rev l) <-> Forall P l.
Proof. intros. rewrite !Forall_forall. setoid_rewrite <- in_rev. reflexivity. Qed.

Lemma existsb_rev:
  forall A P (l : list A), existsb P (rev l) = existsb P l.
Proof. intros. apply eq_iff_eq_true. rewrite !existsb_exists. setoid_rewrite <- in_rev. reflexivity. Qed.



Lemma unions_Desc:
  forall ss lb ub,
  Forall (fun s => Bounded s lb ub) ss ->
  Desc' (unions ss) lb ub (fun i => existsb (fun s => sem s i) ss).
Proof.
  intros.
  unfold unions.
  (* Switch to a fold right *)
  rewrite Proofs.Data.Foldable.hs_coq_foldl'_list.
  rewrite <- fold_left_rev_right.
  rewrite <- (rev_involutive ss).
  rewrite <- (rev_involutive ss), Forall_rev in H.
  generalize dependent (rev ss). intros.
  rewrite rev_involutive.

  induction H.
  * simpl. applyDesc empty_Desc. solve_Desc.
  * simpl fold_right.
    applyDesc IHForall.
    applyDesc union_Desc.
    solve_Desc.
    intro i.
    rewrite Hsem0, Hsem.
    rewrite !existsb_rev.
    simpl. rewrite orb_comm. reflexivity.
Qed.

(** ** Verification of [merge] *)

Lemma merge_eq: forall (l r: Set_ e), merge l r =
  match l, r with
  | Tip, r => r
  | l, Tip => l
  | (Bin sizeL x lx rx as l), (Bin sizeR y ly ry as r) =>
    if Sumbool.sumbool_of_bool
         ((delta GHC.Num.* sizeL) GHC.Base.< sizeR)
    then balanceL y (merge l ly) ry
    else if Sumbool.sumbool_of_bool
              ((delta GHC.Num.* sizeR) GHC.Base.< sizeL)
         then balanceR x lx (merge rx r)
         else glue l r
  end.
Proof.
  unfold merge at 1, merge_func at 1.
  destruct l; only 2: reflexivity.
  destruct r; only 2: reflexivity.
  lazymatch goal with
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs =>
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.


Program Fixpoint merge_Desc (s1: Set_ e)  (s2: Set_ e)
  {measure (set_size s1 + set_size s2)} :
    forall x lb ub,
      Bounded s1 lb (Some x) ->
      Bounded s2 (Some x) ub  ->
      isLB lb x = true ->
      isUB ub x = true->
      Desc (merge s1 s2) lb ub (size s1 + size s2)
           (fun i => sem s1 i || sem s2 i)
  := _.
Next Obligation.
  intros.
  rewrite merge_eq.
  inversion H; subst; clear H;
    inversion H0; subst; clear H0;
      try solve [solve_Desc].
  destruct (Sumbool.sumbool_of_bool _);
    only 2: destruct (Sumbool.sumbool_of_bool _);
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
  - applyDesc merge_Desc.
    applyDesc balanceL_Desc.
    solve_Desc.
  - applyDesc merge_Desc.
    applyDesc balanceR_Desc.
    solve_Desc.
  - applyDesc glue_Desc.
    solve_Desc.
Qed.

(** ** Verification of [splitMember] *)


Lemma splitMember_Desc:
  forall x s lb ub,
  Bounded s lb ub ->
  forall (P : Set_ e * bool * Set_ e -> Prop),
  (forall s1 b s2,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    (forall i, sem s i =
          (if i == x then b
           else  (sem s1 i || sem s2 i))) ->
    P (s1, b, s2)) ->
  P (splitMember x s) : Prop.
Proof.
  intros ?? ?? HB.
  induction HB.
  Ltac solveThis ::= intros X HX; apply HX; clear X HX; [solve_Bounded|solve_Bounded|f_solver].
  * solveThis.
  * simpl.
    destruct (compare x x0) eqn:?.
    + solveThis.
    + apply IHHB1.
      intros s1_2 b s1_3 HB1_2 HB1_3 Hsems1.
      clear IHHB1 IHHB2.
      applyDesc link_Desc.
      solveThis.
    + apply IHHB2.
      intros s2_2 b s2_3 HB2_2 HB2_3 Hsems2.
      clear IHHB1 IHHB2.
      applyDesc link_Desc.
      solveThis.
Qed.

(** ** Verification of [intersection] *)

Lemma intersection_Desc:
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Desc' (intersection s1 s2) lb ub
        (fun i => sem s1 i && sem s2 i).
Proof.
  intros ???? HB1 HB2.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  - simpl. solve_Desc.
  - simpl.
    destruct s3 eqn:Hs3.
    + rewrite<- Hs3 in *.
      clear Hs3 e0 s4 s5 s6.
      eapply splitMember_Desc;
        only 1: eassumption.
      intros s4' b s5' HB1 HB2 Hi.
      applyDesc IHHB1_1.
      applyDesc IHHB1_2.
      destruct b.
      * destruct_ptrEq.
        -- solve_Desc.
        -- applyDesc link_Desc.
           solve_Desc.
      * applyDesc merge_Desc.
        solve_Desc.
    + solve_Desc.
Qed.

(** ** Verification of [difference] *)

Lemma difference_destruct :
  forall (P : Set_ e -> Prop),
  forall s1 s2,
  (s1 = Tip -> P Tip) ->
  (s2 = Tip -> P s1) ->
  (forall sz2 x l2 r2, (s2 = Bin sz2 x l2 r2) ->
    P (
      match splitS x s1 with
      | pair l1 r1 =>
      match difference r1 r2 with
      | r1r2 =>
      match difference l1 l2 with
      | l1l2 => if size l1l2 + size r1r2 == size s1
                then s1 else merge l1l2 r1r2
      end end end)) ->
  P (difference s1 s2).
Proof.
  intros P s1 s2 HTipL HTipR HBins.
  destruct s1, s2; simpl difference;
  try destruct s1_1, s1_2;
  try destruct s2_1, s2_2;
  first [ eapply HBins; reflexivity
        | eapply HTipL; reflexivity
        | eapply HTipR; reflexivity
        | idtac
        ].
Qed.

Lemma difference_Desc :
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  forall (P : Set_ e -> Prop),
  (forall s,
    Bounded s lb ub ->
    size s <= size s1 ->
    (size s = size s1 -> forall i, sem s i = sem s1 i) ->
    (forall i, sem s i = sem s1 i && negb (sem s2 i)) ->
    P s) ->
  P (difference s1 s2).
Proof.
  intros s1 s2 lb ub Hb1 Hb2.
  revert s1 Hb1. induction Hb2; intros sl Hb1; apply hide.
  Ltac showP := apply unhide; intros X HX; apply HX; clear X HX; only 3: intro.
  - simpl.
    destruct sl; (showP; [assumption | reflexivity | reflexivity | f_solver]).
  - apply difference_destruct; intros; subst.
    + (showP; [assumption | reflexivity | reflexivity | f_solver]).
    + (showP; [assumption | reflexivity | reflexivity | f_solver]).
    + eapply splitS_Desc; try eassumption.
      intros sl1 sl2 HBsl1 HBsl2 Hsz Hsem. inversion H3; subst; clear H3.
      eapply IHHb2_1. solve_Bounded. intros sil ????. clear IHHb2_1.
      eapply IHHb2_2. solve_Bounded. intros sir ????. clear IHHb2_2.
      destruct (_ == _) eqn:Hcomp.
      * showP; [assumption | reflexivity | reflexivity | ].
        assert (size sl1 + size sl2 <= size sl) by (destruct (sem sl x0); lia).
        change (size sil + size sir =? size sl = true) in Hcomp.
        rewrite Z.eqb_eq in Hcomp.
        lapply H4; [intro; subst|lia].
        lapply H8; [intro; subst|lia].
        assert (sem sl x0 = false) by (destruct (sem sl x0); try reflexivity; lia).
        f_solver.
      * applyDesc merge_Desc.
        showP.
        -- assumption.
        -- destruct (sem sl x0); lia.
        -- assert (sem sl x0 = false) by (destruct (sem sl x0); try reflexivity; lia).
           rewrite H11 in Hsz.
           lapply H4; [intro; subst; clear H4|lia].
           lapply H8; [intro; subst; clear H8|lia].
           f_solver.
        -- f_solver.
           (* Small [f_solver] incompleteness. *)
           rewrite Hsem0 in H9.
           repeat (f_solver_cleanup; f_solver_step).
Qed.

(** ** Verification of [disjoint] *)

Lemma disjoint_Desc:
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  disjoint s1 s2 = true <-> (forall i, sem s1 i && sem s2 i = false).
Proof.
  intros ???? HB1 HB2.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  - intuition.
  - simpl. destruct s3 eqn:Hs3.
    + rewrite<- Hs3 in *. clear Hs3 e0 s4 s5 s6.
      eapply splitMember_Desc;
        only 1: eassumption.
      intros s4' b s5' HB1 HB2 Hi.
      rewrite !andb_true_iff.
      rewrite IHHB1_1 by assumption; clear IHHB1_1.
      rewrite IHHB1_2 by assumption; clear IHHB1_2.
      split;intro Hyp; [decompose [and] Hyp | split; [| split]];
        try f_solver.
      * specialize (Hyp x). specialize (Hi x).
        rewrite Eq_refl in Hi. rewrite Eq_refl in Hyp.
        rewrite negb_true_iff.
        repeat f_solver_cleanup.
    + simpl. setoid_rewrite andb_false_r. intuition.
Qed.

(** ** Verification of [foldr] *)

(** This relates [foldr] and [toList]. Hard to say which one is more primitive. *)

Lemma fold_right_toList_go:
  forall {a} k (n : a) s (xs : list e),
  fold_right k n (foldr cons xs s) = foldr k (fold_right k n xs) s.
Proof.
  intros.
  revert xs; induction s; intros.
  * simpl.
    rewrite IHs1.
    simpl.
    rewrite IHs2.
    reflexivity.
  * reflexivity.
Qed.


Lemma foldr_spec:
  forall {a} k (n : a) (s : Set_ e),
  foldr k n s = fold_right k n (toList s).
Proof.
  intros.
  unfold toList, toAscList. simpl.
  erewrite fold_right_toList_go by eassumption.
  reflexivity.
Qed.


(** ** Verification of [foldr'] *)

Lemma foldr'_spec:
  forall {a} k (n : a) (s : Set_ e),
  foldr' k n s = foldr k n s.
Proof. reflexivity. Qed.

(** ** Verification of [toList] *)

Lemma elem_app:
  forall {a} `{Eq_ a} (i : a) xs ys,
  List.elem i (xs ++ ys) = List.elem i xs || List.elem i ys.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. rewrite IHxs. rewrite orb_assoc. reflexivity.
Qed.

Lemma elem_cons:
  forall {a} `{Eq_ a} (i : a) x ys,
  List.elem i (x :: ys) = (i == x)  || List.elem i ys.
Proof.
  intros.
  reflexivity.
Qed.

Lemma toList_Bin:
  forall sz x (s1 s2 : Set_ e),
  toList (Bin sz x s1 s2) = toList s1 ++ [x] ++ toList s2.
Proof.
  intros.
  unfold toList at 1, toAscList at 1.
  simpl.
  rewrite !foldr_const_append.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma toList_sem:
  forall s lb ub, Bounded s lb ub ->
  forall i, sem s i = List.elem i (toList s).
Proof.
  intros.
  induction H.
  * simpl. reflexivity.
  * rewrite toList_Bin.
    simpl.
    rewrite IHBounded1, IHBounded2; clear IHBounded1 IHBounded2.
    rewrite elem_app.
    simpl.
    rewrite orb_assoc. reflexivity.
Qed.

Lemma toList_lb:
  forall s lb ub, Bounded s lb ub ->
  Forall (fun i => isLB lb i = true) (toList s).
Proof.
  intros.
  induction H.
  * apply Forall_nil.
  * rewrite toList_Bin.
    rewrite Forall_forall in *.
    intros y Hi.
    simpl in Hi.
    rewrite !in_app_iff in *.
    destruct Hi as [?|[?|?]].
    - intuition.
    - subst. assumption.
    - enough(isLB (Some x) y = true) by order_Bounds.
      intuition.
Qed.

Lemma toList_ub:
  forall s lb ub, Bounded s lb ub ->
  Forall (fun i => isUB ub i = true) (toList s).
Proof.
  intros.
  induction H.
  * apply Forall_nil.
  * rewrite toList_Bin.
    rewrite Forall_forall in *.
    intros y Hi.
    simpl in Hi.
    rewrite !in_app_iff in *.
    destruct Hi as [?|[?|?]].
    - enough(isUB (Some x) y = true) by order_Bounds.
      intuition.
    - subst. assumption.
    - intuition.
Qed.

Lemma toList_Tip: toList (@Tip e) = [].
Proof. reflexivity. Qed.


Lemma toList_bin:
  forall x (s1 s2 : Set_ e),
  toList (bin x s1 s2) = toList s1 ++ [x] ++ toList s2.
Proof. intros. apply toList_Bin. Qed.

Lemma toList_balanceR :
  forall x s1 s2 lb ub,
  Bounded s1 lb (Some x) ->
  Bounded s2 (Some x) ub ->
  balance_prop (size s1) (size s2) \/
  balance_prop_inserted (size s2 - 1) (size s1) /\ (1 <= size s2)%Z  \/
  balance_prop (size s1 + 1) (size s2) ->
  toList (balanceR x s1 s2) = toList s1 ++ [x] ++ toList s2.
Proof.
  intros.
  unfold balanceR.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: rewrite ?toList_Bin, <- ?app_assoc; try reflexivity.
Qed.

Lemma toList_balanceL:
  forall x s1 s2 lb ub,
  Bounded s1 lb (Some x) ->
  Bounded s2 (Some x) ub  ->
  balance_prop (size s1) (size s2) \/
  balance_prop_inserted (size s1 - 1) (size s2) /\ (1 <= size s1)%Z \/
  balance_prop (size s1) (size s2 + 1) ->
  toList (balanceL x s1 s2) = toList s1 ++ [x] ++ toList s2.
Proof.
  intros.
  unfold balanceL.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: rewrite ?toList_Bin, <- ?app_assoc; try reflexivity.
Qed.

Lemma toList_insertMax:
   forall x s lb,
   Bounded s lb (Some x) ->
   toList (insertMax x s) = toList s ++ [x].
Proof.
  intros.
  remember (Some x) as ub'. revert dependent x.
  induction H; intros.
  * reflexivity.
  * clear IHBounded1.
    simpl. subst.
    specialize (IHBounded2 x0 eq_refl).
    revert IHBounded2.
    assert (isUB None x0 = true) by reflexivity.
    applyDesc insertMax_Desc.
    intro IH.
    erewrite toList_balanceR; [ | eassumption| eassumption | solve_size ].
    rewrite IH.
    rewrite toList_Bin, <- ?app_assoc.
    reflexivity.
Qed.

Lemma toList_insertMin:
   forall x s ub,
   Bounded s (Some x) ub ->
   toList (insertMin x s) = [x] ++ toList s.
Proof.
  intros.
  remember (Some x) as ub'. revert dependent x.
  induction H; intros.
  * reflexivity.
  * clear IHBounded2.
    simpl. subst.
    specialize (IHBounded1 x0 eq_refl).
    revert IHBounded1.
    assert (isLB None x0 = true) by reflexivity.
    applyDesc insertMin_Desc.
    intro IH.
    erewrite toList_balanceL; [ | eassumption| eassumption | solve_size ].
    rewrite IH.
    rewrite toList_Bin, <- ?app_assoc.
    reflexivity.
Qed.

Program Fixpoint toList_link (x : e) (s1: Set_ e)  (s2: Set_ e)
  {measure (set_size s1 + set_size s2)} :
    forall lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub  ->
    isLB lb x = true ->
    isUB ub x = true->
    toList (link x s1 s2) = toList s1 ++ [x] ++ toList s2 := _.
Next Obligation.
  intros.
  rewrite link_eq.
  inversion H; subst; clear H;
  inversion H0; subst; clear H0.
  * reflexivity.
  * erewrite toList_insertMin by solve_Bounded.
    rewrite toList_Bin.
    reflexivity.
  * erewrite toList_insertMax by solve_Bounded.
    rewrite toList_Bin.
    reflexivity.
  * destruct (Sumbool.sumbool_of_bool _);
    only 2: destruct (Sumbool.sumbool_of_bool _);
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
    - erewrite toList_balanceL; only 3: solve_Precondition.
      erewrite toList_link by solve_Precondition.
      rewrite ?toList_Bin, <- ?app_assoc. reflexivity.
      applyDesc link_Desc; eassumption.
      applyDesc link_Desc; solve_size.
    - erewrite toList_balanceR; only 2: solve_Precondition.
      erewrite toList_link by solve_Precondition.
      rewrite ?toList_Bin, <- ?app_assoc. reflexivity.
      applyDesc link_Desc; eassumption.
      applyDesc link_Desc; solve_size.
    - rewrite ?toList_bin, ?toList_Bin, <- ?app_assoc. reflexivity.
Qed.


(** *** Sortedness of [toList] *)

Require Import Coq.Sorting.Sorted.

Close Scope Z.
Local Definition lt : e -> e -> Prop
  := fun x y => (x < y) = true.

Lemma sorted_append:
  forall l1 l2 (x : e),
  StronglySorted lt l1 ->
  StronglySorted lt l2 ->
  (forall y, In y l1 -> (y < x) = true) ->
  (forall y, In y l2 -> (x <= y) = true) ->
  StronglySorted lt (l1 ++ l2).
Proof.
  intros ??? Hsorted1 Hsorted2 Hlt Hge.
  induction Hsorted1.
  * apply Hsorted2.
  * simpl. apply SSorted_cons.
    + apply IHHsorted1.
      intros y Hy.
      apply Hlt.
      right.
      assumption.
    + rewrite Forall_forall.
      intros z Hz.
      rewrite in_app_iff in Hz.
      destruct Hz.
      - rewrite Forall_forall in H.
        apply H; auto.
      - assert (lt a x) by (apply Hlt; left; reflexivity).
        assert (x <= z = true) by (apply Hge; assumption).
        (unfold lt in *; order e).
Qed.

Lemma All_lt_elem:
  forall x i xs,
  Forall (lt x) xs ->
  List.elem i xs = true ->
  x < i = true.
Proof.
  intros.
  induction H.
  * simpl in H0. inversion H0.
  * simpl in *.
    rewrite orb_true_iff in H0.
    destruct H0.
    - unfold lt in *. order e.
    - intuition.
Qed.

Lemma to_List_sorted:
  forall s lb ub,
  Bounded s lb ub ->
  StronglySorted lt (toList s).
Proof.
  intros.
  induction H.
  * apply SSorted_nil.
  * rewrite toList_Bin.
    apply sorted_append with (x := x); only 2: apply SSorted_cons.
    - assumption.
    - assumption.
    - apply toList_lb in H0. simpl in H0.
      apply H0.
    - intros.
      apply toList_ub in H. simpl in H.
      rewrite Forall_forall in H.
      apply H; assumption.
    - intros.
      simpl in H5.
      destruct H5.
      + order e.
      + apply toList_lb in H0. simpl in H0.
        rewrite Forall_forall in H0.
        assert (x < y = true) by (apply H0; assumption).
        order e.
Qed.

(** ** Verification of [toAscList] *)

Lemma toAscList_spec: @toAscList = @toList. Proof. reflexivity. Qed.

(** ** Verification of [elems] *)

Lemma elems_spec: @elems = @toList. Proof. reflexivity. Qed.

(** ** Verification of [toDescList] *)

Lemma rev_inj {A} (x y : list A) :
  rev x = rev y -> x = y.
Proof.
  generalize dependent y.
  induction x using rev_ind; simpl; intros;
  destruct y using rev_ind; auto.
  - rewrite rev_app_distr in H.
    discriminate.
  - rewrite rev_app_distr in H.
    discriminate.
  - rewrite !rev_app_distr in H.
    inversion H; subst.
    f_equal.
    now apply IHx.
Qed.

Lemma foldl_acc_app {A : Type} (l : list A) (i : Set_ A) :
  foldl (flip cons) l i = foldl (flip cons) [] i ++ l.
Proof.
  generalize dependent l.
  induction i; simpl; intros; auto.
  rewrite IHi2.
  rewrite IHi1.
  symmetry.
  rewrite IHi2.
  rewrite <- !app_assoc.
  reflexivity.
Qed.

Lemma toDescList_spec (s : Set_ e) :
  toDescList s = rev (toAscList s).
Proof.
  unfold toDescList, toAscList.
  induction s; simpl; auto.
  rewrite !foldr_const_append in *.
  rewrite !app_nil_r in *.
  rewrite <- (rev_involutive (foldl _ _ _)) in IHs1.
  rewrite <- (rev_involutive (foldl _ _ _)) in IHs2.
  apply rev_inj in IHs1.
  apply rev_inj in IHs2.
  rewrite <- !IHs1; clear IHs1.
  rewrite <- !IHs2; clear IHs2.
  rewrite rev_app_distr, rev_involutive.
  simpl.
  rewrite rev_involutive.
  rewrite <- app_assoc.
  now rewrite foldl_acc_app.
Qed.

(** ** Verification of [foldl] *)

(** This relates [foldl] and [toList]. *)

Lemma foldl_spec:
  forall {a} k (n : a) (s : Set_ e),
  foldl k n s = fold_left k (toList s) n.
Proof.
  intros ????.
  revert n.
  induction s; intros n.
  * simpl.
    rewrite toList_Bin.
    rewrite IHs1.
    rewrite IHs2.
    simpl.
    rewrite fold_left_app.
    reflexivity.
  * reflexivity.
Qed.

(** ** Verification of [foldl'] *)

Lemma foldl'_spec:
  forall {a} k (n : a) (s : Set_ e),
  foldl' k n s = foldl k n s.
Proof. reflexivity. Qed.

(** ** Verification of [size] *)

Lemma size_spec:
  forall s lb ub,
  Bounded s lb ub ->
  size s = Z.of_nat (length (toList s)).
Proof.
  intros.
  induction H.
  * reflexivity.
  * rewrite toList_Bin.
    rewrite app_length.
    simpl.
    rewrite H3, IHBounded1, IHBounded2.
    lia.
Qed.

(** ** Verification of [fromDistinctAscList] *)

Definition fromDistinctAscList_create_f : (Int -> list e -> Set_ e * list e) -> (Int -> list e -> Set_ e * list e).
Proof.
  let rhs := eval unfold fromDistinctAscList in (@fromDistinctAscList e) in
  lazymatch rhs with context [deferredFix2 ?f] => exact f end.
Defined.

Definition fromDistinctAscList_create : Int -> list e -> Set_ e * list e
  := deferredFix2 (fromDistinctAscList_create_f).

Lemma Z_shiftr_pos:
  forall x, (1 < x -> 1 <= Z.shiftr x 1)%Z.
Proof.
  intros.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2^1)%Z with 2%Z by reflexivity.
  assert (2 <= x)%Z by lia. clear H.
  apply Z.div_le_mono with (c := 2%Z) in H0.
  apply H0.
  lia.
Qed.

Lemma Z_shiftl_pos:
  forall x, (1 <= x -> 1 <= Z.shiftl x 1)%Z.
Proof.
  intros.
  rewrite Z.shiftl_mul_pow2 by lia.
  lia.
Qed.


Lemma Z_shiftr_lt:
  forall x, (1 <= x -> Z.shiftr x 1 < x)%Z.
Proof.
  intros.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2^1)%Z with 2%Z by reflexivity.
  apply Z_div_lt; lia.
Qed.

Require Import Coq.Wellfounded.Wellfounded.


Lemma fromDistinctAscList_create_eq:
  forall i xs, (1 <= i)%Z ->
  fromDistinctAscList_create i xs = fromDistinctAscList_create_f fromDistinctAscList_create i xs.
Proof.
  intros.
  change (uncurry fromDistinctAscList_create (i, xs) = uncurry (fromDistinctAscList_create_f fromDistinctAscList_create) (i, xs)).
  apply deferredFix_eq_on with
    (f := fun g => uncurry (fromDistinctAscList_create_f (curry g)))
    (P := fun p => (1 <= fst p)%Z)
    (R := fun x y => (1 <= fst x < fst y)%Z).
  * eapply wf_inverse_image with (R := fun x y => (1 <= x < y)%Z).
    apply Z.lt_wf with (z := 1%Z).
  * clear i xs H.
    intros g h x Px Heq.
    destruct x as [i xs]. simpl in *.
    unfold fromDistinctAscList_create_f.
    destruct_match; try reflexivity.
    repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1); try reflexivity.
    unfold curry.
    assert (1 < i)%Z by lia.
    assert (1 <= Z.shiftr i 1)%Z by (apply Z_shiftr_pos; lia).
    assert (Z.shiftr i 1 < i)%Z by (apply Z_shiftr_lt; lia).
    repeat expand_pairs. simpl.
    rewrite Heq by eauto.
    destruct_match; try reflexivity.
    rewrite Heq by eauto.
    reflexivity.
  * simpl; lia.
Qed.

(* We need to know that [create] returns no longer list than it receives. *)
Program Fixpoint fromDistinctAscList_create_preserves_length
  i xs {measure (Z.to_nat i)} :
  (1 <= i)%Z ->
  forall (P : Set_ e * list e -> Prop),
  ( forall s ys,
    (length ys <= length xs)%nat ->
    P (s, ys)
  ) ->
  P (fromDistinctAscList_create i xs) := _.
Next Obligation.
  intros.
  rename fromDistinctAscList_create_preserves_length into IH.
  rewrite fromDistinctAscList_create_eq by assumption.
  unfold fromDistinctAscList_create_f.
  destruct xs.
  * apply H0. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1).
    + apply H0. simpl. lia.
    + assert (Z.to_nat (Bits.shiftR i #1) < Z.to_nat i)%nat. {
        apply Z2Nat.inj_lt.
        apply Z.shiftr_nonneg. lia.
        lia.
        apply Z_shiftr_lt; lia.
      }
      apply IH.
      - assumption.
      - apply Z_shiftr_pos; lia.
      - intros.
        destruct_match.
        ** apply H0. simpl in *. lia.
        ** apply IH.
           -- assumption.
           -- apply Z_shiftr_pos; lia.
           -- intros.
              apply H0. simpl in *. lia.
Qed.

Definition fromDistinctAscList_go_f : (Int -> Set_ e -> list e -> Set_ e) -> (Int -> Set_ e -> list e -> Set_ e).
Proof.
  let rhs := eval unfold fromDistinctAscList in (@fromDistinctAscList e) in
  let rhs := eval fold fromDistinctAscList_create_f in rhs in
  let rhs := eval fold fromDistinctAscList_create in rhs in
  lazymatch rhs with context [deferredFix3 ?f] => exact f end.
Defined.

Definition fromDistinctAscList_go : Int -> Set_ e -> list e -> Set_ e
  := deferredFix3 (fromDistinctAscList_go_f).

Lemma fromDistinctAscList_go_eq:
  forall i s xs, (0 < i)%Z ->
  fromDistinctAscList_go i s xs = fromDistinctAscList_go_f fromDistinctAscList_go i s xs.
Proof.
  intros.
  change (deferredFix (fun g => uncurry (uncurry (fromDistinctAscList_go_f (curry (curry g))))) (i, s, xs) =
    uncurry (uncurry (fromDistinctAscList_go_f fromDistinctAscList_go)) (i, s, xs)).
  rewrite deferredFix_eq_on with
    (P := fun p => (1 <= fst (fst p))%Z)
    (R := fun x y => (length (snd x) < length (snd y))%nat); only 1: reflexivity.
  * apply well_founded_ltof with (f := fun x => length (snd x)).
  * intros g h p Px Heq.
    destruct p as [[x y] z].
    simpl in *.
    unfold fromDistinctAscList_go_f.
    destruct_match; try reflexivity.
    eapply fromDistinctAscList_create_preserves_length; try lia.
    intros s' ys Hlength.
    apply Heq.
    + apply Z_shiftl_pos.
      lia.
    + simpl. lia.
  * simpl. lia.
Qed.

Definition safeHd {a} : list a -> option a := fun xs =>
  match xs with [] => None | (x::_) => Some x end.

Lemma mul_pow_sub:
  forall sz, (0 < sz)%Z -> (2 * 2 ^ (sz - 1) = 2^sz)%Z.
Proof.
  intros.
  rewrite <- Z.pow_succ_r by lia.
  f_equal.
  lia.
Qed.

Program Fixpoint fromDistinctAscList_create_Desc
  sz lb xs {measure (Z.to_nat sz)} :
  (0 <= sz)%Z ->
  StronglySorted (fun x y => x < y = true) (lb :: xs) ->
  forall (P : Set_ e * list e -> Prop),
  ( forall s ys,
    Bounded s (Some lb) (safeHd ys) ->
    xs = toList s ++ ys ->
    ys = [] \/ size s = (2*2^sz-1)%Z ->
    P (s, ys)
  ) ->
  P (fromDistinctAscList_create (2^sz)%Z xs) := _.
Next Obligation.
  intros ???? Hnonneg HSorted.
  rename fromDistinctAscList_create_Desc into IH.
  rewrite fromDistinctAscList_create_eq
    by (enough (0 < 2^sz)%Z by lia; apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctAscList_create_f.
  destruct xs.
  * intros X HX. apply HX. clear HX.
    - solve_Bounded.
    - reflexivity.
    - left. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.

    inversion HSorted. subst.
    inversion H2. subst. clear H2.
    inversion H1. subst.

    assert (isUB (safeHd xs) e0 = true). {
      destruct xs; try reflexivity.
      inversion H5. assumption.
    }

    destruct (Z.eqb_spec (2^sz) 1).
    - intros X HX. apply HX. clear HX.
      ++ solve_Bounded.
      ++ rewrite toList_Bin, toList_Tip, app_nil_r. reflexivity.
      ++ right. rewrite size_Bin. lia.
    - assert (~ (sz = 0))%Z by (intro; subst; simpl in n; congruence).
      assert (sz > 0)%Z by lia.
      replace ((Bits.shiftR (2 ^ sz)%Z 1%Z)) with (2^(sz - 1))%Z.
      Focus 2.
        unfold Bits.shiftR, Bits.instance_Bits_Int.
        rewrite Z.shiftr_div_pow2 by lia.
        rewrite Z.pow_sub_r by lia.
        reflexivity.
      assert (Z.to_nat (sz - 1) < Z.to_nat sz)%nat.
      { rewrite Z2Nat.inj_sub by lia.
        apply Nat.sub_lt.
        apply Z2Nat.inj_le.
        lia.
        lia.
        lia.
        replace (Z.to_nat 1) with 1 by reflexivity.
        lia.
      }
      eapply IH.
      ++ assumption.
      ++ lia.
      ++ eassumption.
      ++ intros l ys HBounded_l Hlist_l Hsize_l.
         destruct ys.
         + intros X HX. apply HX. clear HX.
           ** solve_Bounded.
           ** assumption.
           ** left; reflexivity.
         + simpl in HBounded_l.
           destruct Hsize_l; try congruence.
           eapply IH; clear IH.
           ** assumption.
           ** lia.
           ** rewrite Hlist_l in H1.
              apply StronglySorted_app in H1.
              destruct H1.
              eassumption.
           ** intros r zs HBounded_r Hlist_r Hsize_r.
              rewrite Hlist_l in HSorted.
              assert (isLB (Some lb) e1 = true). {
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                simpl.
                rewrite Forall_forall in H10.
                apply H10.
                apply in_or_app. right. left. reflexivity.
              }
              rewrite Hlist_r in HSorted.
              assert (isUB (safeHd zs) e1 = true). {
                destruct zs; try reflexivity.
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                apply StronglySorted_app in H10.
                destruct H10.
                apply StronglySorted_inv in H12.
                destruct H12.
                rewrite Forall_forall in H13.
                apply H13.
                apply in_or_app. right. left. reflexivity.
              }
              intros X HX. apply HX. clear HX.
              -- applyDesc link_Desc.
              -- erewrite toList_link by eassumption.
                 rewrite Hlist_l. rewrite Hlist_r.
                 rewrite <- !app_assoc.  reflexivity.
              -- destruct Hsize_r; [left; assumption| right].
                 applyDesc link_Desc.
                 replace (size l). replace (size r).
                 rewrite mul_pow_sub in * by lia.
                 lia.
Qed.

Program Fixpoint fromDistinctAscList_go_Desc
  sz s xs {measure (length xs)} :
  (0 <= sz)%Z ->
  StronglySorted (fun x y => x < y = true) xs ->
  Bounded s None (safeHd xs) ->
  xs = [] \/ size s = (2*2^sz-1)%Z ->
  Desc (fromDistinctAscList_go (2^sz)%Z s xs) None None (size s + List.length xs)
    (fun i => sem s i || List.elem i xs) := _.
Next Obligation.
  intros.
  rename fromDistinctAscList_go_Desc into IH.
  rewrite fromDistinctAscList_go_eq by (apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctAscList_go_f.
  destruct xs.
  * replace (List.length []) with 0%Z by reflexivity.
    rewrite Z.add_0_r.
    solve_Desc.
  * repeat replace (#1) with 1%Z by reflexivity.
    replace ((Bits.shiftL (2 ^ sz)%Z 1))%Z with (2 ^ (1 + sz))%Z.
    Focus 2.
      unfold Bits.shiftL, Bits.instance_Bits_Int.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.pow_add_r by lia.
      lia.

    destruct H2; try congruence.
    eapply fromDistinctAscList_create_Desc.
    - lia.
    - eassumption.
    - intros.
      subst.
      simpl safeHd in *.
      assert (isUB (safeHd ys) e0 = true). {
        destruct ys; try reflexivity.
        apply StronglySorted_inv in H0.
        destruct H0.
        rewrite Forall_forall in H4.
        apply H4.
        apply in_or_app. right. left. reflexivity.
      }
      applyDesc link_Desc.
      eapply IH.
      + simpl. rewrite app_length. lia.
      + lia.
      + apply StronglySorted_inv in H0.
        destruct H0.
        apply StronglySorted_app in H0.
        destruct H0.
        assumption.
      + assumption.
      + destruct H5; [left; assumption | right].
        replace (size s1). replace (size s).  replace (size s0).
        rewrite Z.pow_add_r by lia.
        lia.
      + intros.
        solve_Desc.
        ** replace (size s2). replace (size s1). replace (size s).
           rewrite !List.hs_coq_list_length, !Zlength_correct.
           simpl length.
           rewrite app_length, Nat2Z.inj_succ, Nat2Z.inj_add.
           erewrite <- size_spec by eassumption.
           lia.
        ** setoid_rewrite elem_cons.
           setoid_rewrite elem_app.
           setoid_rewrite <- toList_sem; only 2: eassumption.
           f_solver.
Qed.


Lemma fromDistinctAscList_Desc:
  forall xs,
  StronglySorted (fun x y => x < y = true) xs ->
  Desc (fromDistinctAscList xs) None None (List.length xs) (fun i => List.elem i xs).
Proof.
  intros.
  unfold fromDistinctAscList.
  fold fromDistinctAscList_create_f.
  fold fromDistinctAscList_create.
  fold fromDistinctAscList_go_f.
  fold fromDistinctAscList_go.
  destruct xs.
  * solve_Desc.
  * replace (#1) with (2^0)%Z by reflexivity.
    eapply fromDistinctAscList_go_Desc.
    + lia.
    + apply StronglySorted_inv in H.
      destruct H.
      assumption.
    + assert (isUB (safeHd xs) e0 = true). {
        destruct xs; try reflexivity.
        apply StronglySorted_inv in H.
        destruct H.
        rewrite Forall_forall in H0.
        apply H0.
        left. reflexivity.
      }
      solve_Bounded.
    + right. reflexivity.
    + intros.
      rewrite List.hs_coq_list_length, Zlength_cons in *.
      rewrite size_Bin in *.
      solve_Desc.
      setoid_rewrite elem_cons.
      f_solver.
Qed.

(** ** Verification of [fromDistinctDescList] *)

(** Copy’n’paste from [fromDistinctAscList] *)

Definition fromDistinctDescList_create_f : (Int -> list e -> Set_ e * list e) -> (Int -> list e -> Set_ e * list e).
Proof.
  let rhs := eval unfold fromDistinctDescList in (@fromDistinctDescList e) in
  lazymatch rhs with context [deferredFix2 ?f] => exact f end.
Defined.

Definition fromDistinctDescList_create : Int -> list e -> Set_ e * list e
  := deferredFix2 (fromDistinctDescList_create_f).

Lemma fromDistinctDescList_create_eq:
  forall i xs, (1 <= i)%Z ->
  fromDistinctDescList_create i xs = fromDistinctDescList_create_f fromDistinctDescList_create i xs.
Proof.
  intros.
  change (uncurry fromDistinctDescList_create (i, xs) = uncurry (fromDistinctDescList_create_f fromDistinctDescList_create) (i, xs)).
  apply deferredFix_eq_on with
    (f := fun g => uncurry (fromDistinctDescList_create_f (curry g)))
    (P := fun p => (1 <= fst p)%Z)
    (R := fun x y => (1 <= fst x < fst y)%Z).
  * eapply wf_inverse_image with (R := fun x y => (1 <= x < y)%Z).
    apply Z.lt_wf with (z := 1%Z).
  * clear i xs H.
    intros g h x Px Heq.
    destruct x as [i xs]. simpl in *.
    unfold fromDistinctDescList_create_f.
    destruct_match; try reflexivity.
    repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1); try reflexivity.
    unfold curry.
    assert (1 < i)%Z by lia.
    assert (1 <= Z.shiftr i 1)%Z by (apply Z_shiftr_pos; lia).
    assert (Z.shiftr i 1 < i)%Z by (apply Z_shiftr_lt; lia).
    repeat expand_pairs. simpl.
    rewrite Heq by eauto.
    destruct_match; try reflexivity.
    rewrite Heq by eauto.
    reflexivity.
  * simpl; lia.
Qed.

(* We need to know that [create] returns no longer list than it receives. *)
Program Fixpoint fromDistinctDescList_create_preserves_length
  i xs {measure (Z.to_nat i)} :
  (1 <= i)%Z ->
  forall (P : Set_ e * list e -> Prop),
  ( forall s ys,
    (length ys <= length xs)%nat ->
    P (s, ys)
  ) ->
  P (fromDistinctDescList_create i xs) := _.
Next Obligation.
  intros.
  rename fromDistinctDescList_create_preserves_length into IH.
  rewrite fromDistinctDescList_create_eq by assumption.
  unfold fromDistinctDescList_create_f.
  destruct xs.
  * apply H0. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1).
    + apply H0. simpl. lia.
    + assert (Z.to_nat (Bits.shiftR i #1) < Z.to_nat i)%nat. {
        apply Z2Nat.inj_lt.
        apply Z.shiftr_nonneg. lia.
        lia.
        apply Z_shiftr_lt; lia.
      }
      apply IH.
      - assumption.
      - apply Z_shiftr_pos; lia.
      - intros.
        destruct_match.
        ** apply H0. simpl in *. lia.
        ** apply IH.
           -- assumption.
           -- apply Z_shiftr_pos; lia.
           -- intros.
              apply H0. simpl in *. lia.
Qed.

Definition fromDistinctDescList_go_f : (Int -> Set_ e -> list e -> Set_ e) -> (Int -> Set_ e -> list e -> Set_ e).
Proof.
  let rhs := eval unfold fromDistinctDescList in (@fromDistinctDescList e) in
  let rhs := eval fold fromDistinctDescList_create_f in rhs in
  let rhs := eval fold fromDistinctDescList_create in rhs in
  lazymatch rhs with context [deferredFix3 ?f] => exact f end.
Defined.

Definition fromDistinctDescList_go : Int -> Set_ e -> list e -> Set_ e
  := deferredFix3 (fromDistinctDescList_go_f).

Lemma fromDistinctDescList_go_eq:
  forall i s xs, (0 < i)%Z ->
  fromDistinctDescList_go i s xs = fromDistinctDescList_go_f fromDistinctDescList_go i s xs.
Proof.
  intros.
  change (deferredFix (fun g => uncurry (uncurry (fromDistinctDescList_go_f (curry (curry g))))) (i, s, xs) =
    uncurry (uncurry (fromDistinctDescList_go_f fromDistinctDescList_go)) (i, s, xs)).
  rewrite deferredFix_eq_on with
    (P := fun p => (1 <= fst (fst p))%Z)
    (R := fun x y => (length (snd x) < length (snd y))%nat); only 1: reflexivity.
  * apply well_founded_ltof with (f := fun x => length (snd x)).
  * intros g h p Px Heq.
    destruct p as [[x y] z].
    simpl in *.
    unfold fromDistinctDescList_go_f.
    destruct_match; try reflexivity.
    eapply fromDistinctDescList_create_preserves_length; try lia.
    intros s' ys Hlength.
    apply Heq.
    + apply Z_shiftl_pos.
      lia.
    + simpl. lia.
  * simpl. lia.
Qed.


Program Fixpoint fromDistinctDescList_create_Desc
  sz ub xs {measure (Z.to_nat sz)} :
  (0 <= sz)%Z ->
  StronglySorted (fun x y => x > y = true) (ub :: xs) ->
  forall (P : Set_ e * list e -> Prop),
  ( forall s ys,
    Bounded s (safeHd ys) (Some ub)   ->
    xs = rev (toList s) ++ ys ->
    ys = [] \/ size s = (2*2^sz-1)%Z ->
    P (s, ys)
  ) ->
  P (fromDistinctDescList_create (2^sz)%Z xs) := _.
Next Obligation.
  intros ???? Hnonneg HSorted.
  rename fromDistinctDescList_create_Desc into IH.
  rewrite fromDistinctDescList_create_eq
    by (enough (0 < 2^sz)%Z by lia; apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctDescList_create_f.
  destruct xs.
  * intros X HX. apply HX. clear HX.
    - solve_Bounded.
    - reflexivity.
    - left. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.

    inversion HSorted. subst.
    inversion H2. subst. clear H2.
    inversion H1. subst.

    assert (isLB (safeHd xs) e0 = true). {
      destruct xs; try reflexivity.
      inversion H5. simpl. order e.
    }

    destruct (Z.eqb_spec (2^sz) 1).
    - intros X HX. apply HX. clear HX.
      ++ solve_Bounded.
      ++ rewrite toList_Bin, toList_Tip, app_nil_r. reflexivity.
      ++ right. rewrite size_Bin. lia.
    - assert (~ (sz = 0))%Z by (intro; subst; simpl in n; congruence).
      assert (sz > 0)%Z by lia.
      replace ((Bits.shiftR (2 ^ sz)%Z 1%Z)) with (2^(sz - 1))%Z.
      Focus 2.
        unfold Bits.shiftR, Bits.instance_Bits_Int.
        rewrite Z.shiftr_div_pow2 by lia.
        rewrite Z.pow_sub_r by lia.
        reflexivity.
      assert (Z.to_nat (sz - 1) < Z.to_nat sz)%nat.
      { rewrite Z2Nat.inj_sub by lia.
        apply Nat.sub_lt.
        apply Z2Nat.inj_le.
        lia.
        lia.
        lia.
        replace (Z.to_nat 1) with 1 by reflexivity.
        lia.
      }
      eapply IH.
      ++ assumption.
      ++ lia.
      ++ eassumption.
      ++ intros l ys HBounded_l Hlist_l Hsize_l.
         destruct ys.
         + intros X HX. apply HX. clear HX.
           ** solve_Bounded.
           ** assumption.
           ** left; reflexivity.
         + simpl in HBounded_l.
           destruct Hsize_l; try congruence.
           eapply IH; clear IH.
           ** assumption.
           ** lia.
           ** rewrite Hlist_l in H1.
              apply StronglySorted_app in H1.
              destruct H1.
              eassumption.
           ** intros r zs HBounded_r Hlist_r Hsize_r.
              rewrite Hlist_l in HSorted.
              assert (isUB (Some ub) e1 = true). {
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                simpl.
                rewrite Forall_forall in H10.
                enough (ub > e1 = true) by (order e).
                apply H10.
                apply in_or_app. right. left. reflexivity.
              }
              rewrite Hlist_r in HSorted.
              assert (isLB (safeHd zs) e1 = true). {
                destruct zs; try reflexivity.
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                apply StronglySorted_app in H10.
                destruct H10.
                apply StronglySorted_inv in H12.
                destruct H12.
                rewrite Forall_forall in H13.
                simpl.
                enough (e1 > e2 = true) by (order e).
                apply H13.
                apply in_or_app. right. left. reflexivity.
              }
              intros X HX. apply HX. clear HX.
              -- applyDesc link_Desc.
              -- erewrite toList_link by eassumption.
                 rewrite Hlist_l. rewrite Hlist_r.
                 rewrite !rev_app_distr; simpl.
                 rewrite <- !app_assoc.  simpl. reflexivity.
              -- destruct Hsize_r; [left; assumption| right].
                 applyDesc link_Desc.
                 replace (size l). replace (size r).
                 rewrite mul_pow_sub in * by lia.
                 lia.
Qed.

Lemma elem_rev:
  forall x xs, List.elem x (rev xs) = List.elem x xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. rewrite elem_app. rewrite orb_comm.
    simpl. rewrite orb_false_r. rewrite IHxs. reflexivity.
Qed.

Program Fixpoint fromDistinctDescList_go_Desc
  sz s xs {measure (length xs)} :
  (0 <= sz)%Z ->
  StronglySorted (fun x y => x > y = true) xs ->
  Bounded s (safeHd xs) None ->
  xs = [] \/ size s = (2*2^sz-1)%Z ->
  Desc (fromDistinctDescList_go (2^sz)%Z s xs) None None (size s + List.length xs)
    (fun i => sem s i || List.elem i xs) := _.
Next Obligation.
  intros.
  rename fromDistinctDescList_go_Desc into IH.
  rewrite fromDistinctDescList_go_eq by (apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctDescList_go_f.
  destruct xs.
  * replace (List.length []) with 0%Z by reflexivity.
    rewrite Z.add_0_r.
    solve_Desc.
  * repeat replace (#1) with 1%Z by reflexivity.
    replace ((Bits.shiftL (2 ^ sz)%Z 1))%Z with (2 ^ (1 + sz))%Z.
    Focus 2.
      unfold Bits.shiftL, Bits.instance_Bits_Int.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.pow_add_r by lia.
      lia.

    destruct H2; try congruence.
    eapply fromDistinctDescList_create_Desc.
    - lia.
    - eassumption.
    - intros.
      subst.
      simpl safeHd in *.
      assert (isLB (safeHd ys) e0 = true). {
        destruct ys; try reflexivity.
        apply StronglySorted_inv in H0.
        destruct H0.
        rewrite Forall_forall in H4.
        simpl.
        enough (e0 > e1 = true) by order e.
        apply H4.
        apply in_or_app. right. left. reflexivity.
      }
      applyDesc link_Desc.
      eapply IH.
      + simpl. rewrite app_length. lia.
      + lia.
      + apply StronglySorted_inv in H0.
        destruct H0.
        apply StronglySorted_app in H0.
        destruct H0.
        assumption.
      + assumption.
      + destruct H5; [left; assumption | right].
        replace (size s1). replace (size s).  replace (size s0).
        rewrite Z.pow_add_r by lia.
        lia.
      + intros.
        solve_Desc.
        ** replace (size s2). replace (size s1). replace (size s).
           rewrite !List.hs_coq_list_length, !Zlength_correct.
           simpl length.
           rewrite app_length, Nat2Z.inj_succ, Nat2Z.inj_add, rev_length.
           erewrite <- size_spec by eassumption.
           lia.
        ** setoid_rewrite elem_cons.
           setoid_rewrite elem_app.
           setoid_rewrite elem_rev.
           setoid_rewrite <- toList_sem; only 2: eassumption.
           f_solver.
Qed.


Lemma fromDistinctDescList_Desc:
  forall xs,
  StronglySorted (fun x y => x > y = true) xs ->
  Desc (fromDistinctDescList xs) None None (List.length xs) (fun i => List.elem i xs).
Proof.
  intros.
  unfold fromDistinctDescList.
  fold fromDistinctDescList_create_f.
  fold fromDistinctDescList_create.
  fold fromDistinctDescList_go_f.
  fold fromDistinctDescList_go.
  destruct xs.
  * solve_Desc.
  * replace (#1) with (2^0)%Z by reflexivity.
    eapply fromDistinctDescList_go_Desc.
    + lia.
    + apply StronglySorted_inv in H.
      destruct H.
      assumption.
    + assert (isLB (safeHd xs) e0 = true). {
        destruct xs; try reflexivity.
        apply StronglySorted_inv in H.
        destruct H.
        rewrite Forall_forall in H0.
        simpl.
        enough (e0 > e1 = true) by order e.
        apply H0.
        left. reflexivity.
      }
      solve_Bounded.
    + right. reflexivity.
    + intros.
      rewrite List.hs_coq_list_length, Zlength_cons in *.
      rewrite size_Bin in *.
      solve_Desc.
      setoid_rewrite elem_cons.
      f_solver.
Qed.


(** ** Verification of [combineEq] *)

Definition combineEqGo : e -> list e -> list e.
Proof.
  let rhs := eval unfold combineEq in (@combineEq e _) in
  match rhs with fun _ => match _ with [] => [] | cons _ _ => ?go _ _ end => exact go end.
Defined.

(* Too much duplication here *)

Lemma Forall_le_elem:
  forall x xs,
  Forall (fun y => x <= y = true) xs <-> (forall i, List.elem i xs = true -> x <= i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi.
      rewrite orb_true_iff in Hi. destruct Hi.
      + order e.
      + apply H3; assumption.
    - constructor.
      + apply H. simpl. rewrite Eq_refl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. apply orb_true_r.
Qed.

Lemma Forall_ge_elem:
  forall x xs,
  Forall (fun y => x >= y = true) xs <-> (forall i, List.elem i xs = true -> x >= i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi.
      rewrite orb_true_iff in Hi. destruct Hi.
      + order e.
      + apply H3; assumption.
    - constructor.
      + apply H. simpl. rewrite Eq_refl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. apply orb_true_r.
Qed.

Lemma Forall_lt_elem:
  forall x xs,
  Forall (fun y => x < y = true) xs <-> (forall i, List.elem i xs = true -> x < i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi.
      rewrite orb_true_iff in Hi. destruct Hi.
      + order e.
      + apply H3; assumption.
    - constructor.
      + apply H. simpl. rewrite Eq_refl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. apply orb_true_r.
Qed.


Lemma Forall_gt_elem:
  forall x xs,
  Forall (fun y => x > y = true) xs <-> (forall i, List.elem i xs = true -> x > i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi.
      rewrite orb_true_iff in Hi. destruct Hi.
      + order e.
      + apply H3; assumption.
    - constructor.
      + apply H. simpl. rewrite Eq_refl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. apply orb_true_r.
Qed.


Lemma combineEqGo_spec:
  forall x xs,
  StronglySorted (fun x y => x <= y = true) (x :: xs) ->
  forall P : list e -> Prop,
  (forall ys,
     StronglySorted (fun x y => x < y = true) ys ->
     (forall i, List.elem i ys = List.elem i (x :: xs)) ->
     P ys) ->
  P (combineEqGo x xs).
Proof.
  intros x xs Hsorted.
  inversion Hsorted; subst; clear Hsorted.
  revert x H2.
  induction H1; intros x Hlt.
  * intros X HX; apply HX; clear X HX.
    + constructor; constructor.
    + intro. reflexivity.
  * inversion Hlt; subst; clear Hlt.
    simpl.
    destruct_match.
    + eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - assumption.
      - intro i. rewrite Hiys. simpl.
        destruct (i == x) eqn:?, (i == a) eqn:?; order e.
    + assert (Hlt : x < a = true) by order e. clear H3 Heq.
      eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - constructor.
        ** eapply StronglySorted_R_ext; only 2: apply Hsortedys.
           intros. simpl. order e.
        ** apply Forall_lt_elem.
           rewrite Forall_le_elem in H.
           intros i Hi. rewrite Hiys in Hi. simpl in Hi. rewrite orb_true_iff in Hi. destruct Hi.
           ++ order e.
           ++ apply H in H0. order e.
      - intro i. simpl. rewrite Hiys. simpl. reflexivity.
Qed.


Lemma combineEqGo_spec2:
  forall x xs,
  StronglySorted (fun x y => x >= y = true) (x :: xs) ->
  forall P : list e -> Prop,
  (forall ys,
     StronglySorted (fun x y => x > y = true) ys ->
     (forall i, List.elem i ys = List.elem i (x :: xs)) ->
     P ys) ->
  P (combineEqGo x xs).
Proof.
  intros x xs Hsorted.
  inversion Hsorted; subst; clear Hsorted.
  revert x H2.
  induction H1; intros x Hlt.
  * intros X HX; apply HX; clear X HX.
    + constructor; constructor.
    + intro. reflexivity.
  * inversion Hlt; subst; clear Hlt.
    simpl.
    destruct_match.
    + eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - assumption.
      - intro i. rewrite Hiys. simpl.
        destruct (i == x) eqn:?, (i == a) eqn:?; order e.
    + assert (Hlt : x > a = true) by order e. clear H3 Heq.
      eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - constructor.
        ** eapply StronglySorted_R_ext; only 2: apply Hsortedys.
           intros. simpl. order e.
        ** apply Forall_gt_elem.
           rewrite Forall_ge_elem in H.
           intros i Hi. rewrite Hiys in Hi. simpl in Hi. rewrite orb_true_iff in Hi. destruct Hi.
           ++ order e.
           ++ apply H in H0. order e.
      - intro i. simpl. rewrite Hiys. simpl. reflexivity.
Qed.


Lemma combineEq_spec:
  forall xs,
  StronglySorted (fun x y => x <= y = true) xs ->
  forall P : list e -> Prop,
  (forall ys,
     StronglySorted (fun x y => x < y = true) ys ->
     (forall i, List.elem i ys = List.elem i xs) ->
     P ys) ->
  P (combineEq xs).
Proof.
  intros xs Hsorted.
  inversion Hsorted.
  * intros X HX. apply HX. clear X HX.
    - constructor.
    - intro. reflexivity.
  * rewrite <- H1 in Hsorted. clear xs H0 H1.
    unfold combineEq. fold combineEqGo.
    apply combineEqGo_spec. assumption.
Qed.


Lemma combineEq_spec2:
  forall xs,
  StronglySorted (fun x y => x >= y = true) xs ->
  forall P : list e -> Prop,
  (forall ys,
     StronglySorted (fun x y => x > y = true) ys ->
     (forall i, List.elem i ys = List.elem i xs) ->
     P ys) ->
  P (combineEq xs).
Proof.
  intros xs Hsorted.
  inversion Hsorted.
  * intros X HX. apply HX. clear X HX.
    - constructor.
    - intro. reflexivity.
  * rewrite <- H1 in Hsorted. clear xs H0 H1.
    unfold combineEq. fold combineEqGo.
    apply combineEqGo_spec2. assumption.
Qed.


(** ** Verification of [fromAscList] *)

Lemma fromAscList_Desc:
  forall xs,
  StronglySorted (fun x y => x <= y = true) xs ->
  Desc' (fromAscList xs) None None (fun i => List.elem i xs).
Proof.
  intros.
  unfold fromAscList.
  eapply combineEq_spec; only 1: assumption; intros ys HSorted Helem.
  apply fromDistinctAscList_Desc; only 1: assumption.
  intros s HB Hsz Hf.
  solve_Desc.
Qed.


(** ** Verification of [fromDescList] *)

Lemma fromDescList_Desc:
  forall xs,
  StronglySorted (fun x y => x >= y = true) xs ->
  Desc' (fromDescList xs) None None (fun i => List.elem i xs).
Proof.
  intros.
  unfold fromDescList.
  eapply combineEq_spec2; only 1: assumption; intros ys HSorted Helem.
  apply fromDistinctDescList_Desc; only 1: assumption.
  intros s HB Hsz Hf.
  solve_Desc.
Qed.

(** ** Verification of [fromList] *)

(** The verification of [fromList] should be similar to that of [fromDistinctAscList], only
that the condition is checked and -- if it fails -- we resort to a backup implementation. *)

(* The following definitions are copied from the local definitions of [fromList];
   my ltac foo failed to do that automatic.
*)
Definition fromList' :=
     fun (t0 : Set_ e) (xs : list e) =>
     let ins := fun (t : Set_ e) (x : e) => insert x t in Foldable.foldl ins t0 xs.

Definition not_ordered :=
      fun (arg_4__ : e) (arg_5__ : list e) =>
      match arg_5__ with
      | [] => false
      | y :: _ => _GHC.Base.>=_ arg_4__ y
      end.

Definition fromList_create_f : (Int -> list e -> Set_ e * list e * list e) -> (Int -> list e -> Set_ e * list e  * list e)
  := (fun create (arg_8__ : Int) (arg_9__ : list e) =>
           match arg_9__ with
           | [] => (Tip, [], [])
           | x :: xss =>
               if _GHC.Base.==_ arg_8__ #1
               then
                if not_ordered x xss
                then (Bin #1 x Tip Tip, [], xss)
                else (Bin #1 x Tip Tip, xss, [])
               else
                let (p, zs) := create (Bits.shiftR arg_8__ #1) arg_9__ in
                let (l0, ys) := p in
                match ys with
                | [] => (l0, [], zs)
                | [y] => (insertMax y l0, [], zs)
                | y :: (_ :: _) as yss =>
                    if not_ordered y yss
                    then (l0, [], ys)
                    else
                     let
                     '(r, zs0, ws) := create (Bits.shiftR arg_8__ #1) yss in
                      (link y l0 r, zs0, ws)
                end
           end).

Definition fromList_create : Int -> list e -> Set_ e * list e * list e
  := deferredFix2 (fromList_create_f).

Definition fromList_go_f :=
  (fun (go : Int -> Set_ e -> list e -> Set_ e) (arg_22__ : Int)
          (arg_23__ : Set_ e) (arg_24__ : list e) =>
        match arg_24__ with
        | [] => arg_23__
        | [x] => insertMax x arg_23__
        | x :: (_ :: _) as xss =>
            if not_ordered x xss
            then fromList' arg_23__ arg_24__
            else
             let (p, ys) := fromList_create arg_22__ xss in
             let (r, ys0) := p in
             match ys with
             | [] => go (Bits.shiftL arg_22__ #1) (link x arg_23__ r) ys0
             | _ :: _ => fromList' (link x arg_23__ r) ys
             end
        end).

Definition fromList_go := deferredFix3 (fromList_go_f).


(** zeta-reduces exactly one (the outermost) [let] *)
Ltac zeta_one :=
  lazymatch goal with |- context A [let x := ?rhs in @?body x] =>
     let e' := eval cbv beta in (body rhs) in
     let e'' := context A [e'] in
     change e''
  end.

(* Identical to [fromDistinctAscList_create_eq] *)
Lemma fromList_create_eq:
  forall i xs, (1 <= i)%Z ->
  fromList_create i xs = fromList_create_f fromList_create i xs.
Proof.
  intros.
  change (uncurry fromList_create (i, xs) = uncurry (fromList_create_f fromList_create) (i, xs)).
  apply deferredFix_eq_on with
    (f := fun g => uncurry (fromList_create_f (curry g)))
    (P := fun p => (1 <= fst p)%Z)
    (R := fun x y => (1 <= fst x < fst y)%Z).
  * eapply wf_inverse_image with (R := fun x y => (1 <= x < y)%Z).
    apply Z.lt_wf with (z := 1%Z).
  * clear i xs H.
    intros g h x Px Heq.
    destruct x as [i xs]. simpl in *.
    unfold fromList_create_f.
    destruct_match; try reflexivity.
    repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1); try reflexivity.
    unfold curry.
    assert (1 < i)%Z by lia.
    assert (1 <= Z.shiftr i 1)%Z by (apply Z_shiftr_pos; lia).
    assert (Z.shiftr i 1 < i)%Z by (apply Z_shiftr_lt; lia).
    repeat expand_pairs. simpl.
    rewrite Heq by eauto.
    destruct_match; try reflexivity.
    rewrite Heq by eauto.
    reflexivity.
  * simpl; lia.
Qed.

(* We need to know that [create] returns no longer list than it receives.
   Like [fromDistinctAscList_create_preserves_length], just a few more cases.
 *)
Program Fixpoint fromList_create_preserves_length
  i xs {measure (Z.to_nat i)} :
  (1 <= i)%Z ->
  forall (P : Set_ e * list e * list e -> Prop),
  ( forall s ys zs ,
    (length ys <= length xs)%nat ->
    P (s, ys, zs)
  ) ->
  P (fromList_create i xs) := _.
Next Obligation.
  intros.
  rename fromList_create_preserves_length into IH.
  rewrite fromList_create_eq by assumption.
  unfold fromList_create_f.
  destruct xs.
  * apply H0. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1).
    + destruct_match.
      - apply H0. simpl. lia.
      - apply H0. simpl. lia.
    + assert (Z.to_nat (Bits.shiftR i #1) < Z.to_nat i)%nat. {
        apply Z2Nat.inj_lt.
        apply Z.shiftr_nonneg. lia.
        lia.
        apply Z_shiftr_lt; lia.
      }
      apply IH.
      - assumption.
      - apply Z_shiftr_pos; lia.
      - intros.
        destruct_match.
        ** apply H0. simpl in *. lia.
        ** apply IH.
           -- assumption.
           -- apply Z_shiftr_pos; lia.
           -- intros.
              repeat destruct_match.
              ++ apply H0. simpl in *. lia.
              ++ apply H0. simpl in *. lia.
              ++ apply H0. simpl in *. lia.
Qed.

Lemma fromList_go_eq:
  forall i s xs, (0 < i)%Z ->
  fromList_go i s xs = fromList_go_f fromList_go i s xs.
Proof.
  intros.
  change (deferredFix (fun g => uncurry (uncurry (fromList_go_f (curry (curry g))))) (i, s, xs) =
    uncurry (uncurry (fromList_go_f fromList_go)) (i, s, xs)).
  rewrite deferredFix_eq_on with
    (P := fun p => (1 <= fst (fst p))%Z)
    (R := fun x y => (length (snd x) < length (snd y))%nat); only 1: reflexivity.
  * apply well_founded_ltof with (f := fun x => length (snd x)).
  * intros g h p Px Heq.
    destruct p as [[x y] z].
    simpl in *.
    unfold fromList_go_f.
    destruct_match; try reflexivity.
    eapply fromList_create_preserves_length; try lia.
    intros s' ys zs Hlength.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    apply Heq.
    + apply Z_shiftl_pos.
      lia.
    + simpl. simpl in *. lia.
  * simpl. lia.
Qed.

Program Fixpoint fromList_create_Desc
  sz lb xs {measure (Z.to_nat sz)} :
  (0 <= sz)%Z ->
  not_ordered lb xs = false ->
(*   StronglySorted (fun x y => x < y = true) (lb :: xs) -> *)
  forall (P : Set_ e * list e * list e -> Prop),
  ( forall s ys zs,
    Bounded s (Some lb) (safeHd ys) ->
    isUB (safeHd ys) lb = true ->
    xs = toList s ++ ys ++ zs->
    ys = [] \/ (size s = (2*2^sz-1)%Z /\ zs = []) ->
    P (s, ys, zs)
  ) ->
  P (fromList_create (2^sz)%Z xs) := _.
Next Obligation.
  intros ???? Hnonneg HheadOrdered.
  rename fromList_create_Desc into IH.
  rewrite fromList_create_eq
    by (enough (0 < 2^sz)%Z by lia; apply Z.pow_pos_nonneg; lia).
  unfold fromList_create_f.
  destruct xs.
  * intros X HX. apply HX. clear HX.
    - solve_Bounded.
    - reflexivity.
    - reflexivity.
    - left. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.

    simpl in HheadOrdered.

(*     assert (isUB (safeHd xs) e0 = true). {
      destruct xs; try reflexivity.
      inversion H5. assumption.
    } *)

    destruct (Z.eqb_spec (2^sz) 1); [ destruct_match | ].
    - intros X HX. apply HX; clear HX.
      ++ solve_Bounded.
      ++ reflexivity.
      ++ rewrite toList_Bin, toList_Tip, app_nil_r. reflexivity.
      ++ left. reflexivity.
    - intros X HX. apply HX; clear HX.
      ++ destruct xs; simpl in Heq; solve_Bounded.
      ++ destruct xs; simpl in *; solve_Bounds.
      ++ rewrite toList_Bin, toList_Tip, !app_nil_r, !app_nil_l. reflexivity.
      ++ right. split. rewrite size_Bin. lia. reflexivity.
    - assert (~ (sz = 0))%Z by (intro; subst; simpl in n; congruence).
      assert (sz > 0)%Z by lia.
      replace ((Bits.shiftR (2 ^ sz)%Z 1%Z)) with (2^(sz - 1))%Z.
      Focus 2.
        unfold Bits.shiftR, Bits.instance_Bits_Int.
        rewrite Z.shiftr_div_pow2 by lia.
        rewrite Z.pow_sub_r by lia.
        reflexivity.
      assert (Z.to_nat (sz - 1) < Z.to_nat sz)%nat.
      { rewrite Z2Nat.inj_sub by lia.
        apply Nat.sub_lt.
        apply Z2Nat.inj_le.
        lia.
        lia.
        lia.
        replace (Z.to_nat 1) with 1 by reflexivity.
        lia.
      }
      eapply IH.
      ++ assumption.
      ++ lia.
      ++ eassumption.
      ++ intros l ys zs HBounded_l HisUB_l Hlist_l Hsize_l.
         destruct ys.
         + intros X HX. apply HX. clear HX.
           ** solve_Bounded.
           ** assumption.
           ** assumption.
           ** left; reflexivity.
         + simpl in HBounded_l.
           destruct Hsize_l as [? | [??]]; try congruence.
           subst. rewrite app_nil_r in Hlist_l.
           assert (isLB (Some lb) e1 = true) by solve_Bounds.
           destruct ys; only 2: destruct_match.
           -- intros X HX. apply HX; clear HX.
              ** assert (isUB None e1 = true) by reflexivity.
                 applyDesc insertMax_Desc.
              ** reflexivity.
              ** erewrite toList_insertMax by eassumption.
                 rewrite app_nil_l, <- app_assoc.
                 assumption.
              ** left; reflexivity.
           -- intros X HX. apply HX; clear HX.
              ** solve_Bounded.
              ** reflexivity.
              ** rewrite app_nil_l. simpl in Hlist_l.
                 assumption.
              ** left; reflexivity.
           -- eapply IH; clear IH.
              ** assumption.
              ** lia.
              ** eassumption.
              ** simpl in Heq.
                 intros r zs zs' HBounded_r HisUB_r Hlist_r Hsize_r.
                 intros X HX. apply HX. clear HX.
                 --- applyDesc link_Desc.
                 --- solve_Bounds.
                 --- erewrite toList_link by eassumption.
                     rewrite Hlist_l. rewrite Hlist_r.
                     rewrite <- !app_assoc.  reflexivity.
                 --- destruct Hsize_r; [left; assumption| right].
                     destruct H4.
                     split; only 2: assumption.
                     applyDesc link_Desc.
                     replace (size l). rewrite H4.
                     rewrite mul_pow_sub in * by lia.
                     lia.
Qed.

Lemma fromList'_Desc:
  forall s l,
  Bounded s None None ->
  Desc' (fromList' s l) None None (fun i => sem s i || List.elem i l).
Proof.
  intros.
  unfold fromList'.
  rewrite Foldable.hs_coq_foldl_list.
  revert s H.
  induction l.
  * intros.
    simpl.
    solve_Desc.
  * intros.
    simpl.
    applyDesc insert_Desc.
    applyDesc IHl.
    solve_Desc.
Qed.

Program Fixpoint fromList_go_Desc
  sz s xs {measure (length xs)} :
  (0 <= sz)%Z ->
  Bounded s None (safeHd xs) ->
  xs = [] \/ size s = (2*2^sz-1)%Z ->
  Desc' (fromList_go (2^sz)%Z s xs) None None
    (fun i => sem s i || List.elem i xs) := _.
Next Obligation.
  intros.
  rename fromList_go_Desc into IH.
  rewrite fromList_go_eq by (apply Z.pow_pos_nonneg; lia).
  unfold fromList_go_f.
  destruct xs as [ | ? [ | ?? ]].
  * solve_Desc.
  * destruct H1; try congruence.
    simpl safeHd in *.
    assert (isUB None e0 = true) by reflexivity.
    applyDesc insertMax_Desc.
    solve_Desc.
    setoid_rewrite elem_cons.
    f_solver.
  * destruct H1; try congruence.
    repeat replace (#1) with 1%Z by reflexivity.
    replace ((Bits.shiftL (2 ^ sz)%Z 1))%Z with (2 ^ (1 + sz))%Z.
    Focus 2.
      unfold Bits.shiftL, Bits.instance_Bits_Int.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.pow_add_r by lia.
      lia.
    destruct_match.
    --  apply Bounded_relax_ub_None in H0.
        applyDesc fromList'_Desc.
        solve_Desc.
    --  eapply fromList_create_Desc.
        - lia.
        - eassumption.
        - intros.
          subst.
          simpl safeHd in *.

          applyDesc link_Desc.
          destruct zs.
          ++  rewrite app_nil_r in H4.
              eapply IH.
              + rewrite H4. simpl. rewrite app_length. lia.
              + lia.
              + assumption.
              + destruct H5 as [?|[??]]; [left; assumption | right].
                replace (size s1). replace (size s).  replace (size s0).
                rewrite Z.pow_add_r by lia.
                lia.
              + intros.
                rewrite H4.
                solve_Desc.
                setoid_rewrite elem_cons.
                setoid_rewrite elem_app.
                setoid_rewrite <- toList_sem; only 2: eassumption.
                f_solver.
         ++ destruct H5 as [ ? | [? Habsurd]]; try congruence.
            subst. rewrite app_nil_l in H4.
            rewrite H4.
            apply Bounded_relax_ub_None in HB.
            applyDesc fromList'_Desc.
            solve_Desc.
            setoid_rewrite elem_cons.
            setoid_rewrite elem_app.
            setoid_rewrite <- toList_sem; only 2: eassumption.
            f_solver.
Qed.

Lemma fromList_Desc:
  forall xs,
  Desc' (fromList xs) None None (fun i => List.elem i xs).
Proof.
  intros.
  cbv beta delta [fromList].
  destruct xs as [ | ? [|??] ].
  * solve_Desc.
  * solve_Desc.
  * fold fromList'.
    zeta_one.
    fold not_ordered.
    zeta_one.
    fold fromList_create_f.
    fold fromList_create.
    zeta_one.
    fold fromList_go_f.
    fold fromList_go.
    zeta_one.
    destruct_match.
    - applyDesc fromList'_Desc.
      solve_Desc.
      setoid_rewrite elem_cons.
      f_solver.
    - repeat replace (#1) with (2^0)%Z by reflexivity.
      eapply fromList_go_Desc.
      + lia.
      + simpl in Heq.
        solve_Bounded.
      + right. reflexivity.
      + intros.
        solve_Desc.
        setoid_rewrite elem_cons.
        f_solver.
Qed.


(** ** Verification of [Eq] *)

Lemma eqlist_sym:
  forall {a} `{EqLaws a} (xs ys : list a),
  eqlist xs ys = eqlist ys xs.
Proof.
  intros. revert ys.
  induction xs; intros ys; destruct ys; simpl in *; try congruence.
  rewrite Eq_sym. rewrite IHxs.
  reflexivity.
Qed.

Lemma eqlist_length:
  forall {a} `{Eq_ a} (xs ys : list a),
  eqlist xs ys = true ->
  length xs = length ys.
Proof.
  intros. revert ys H0.
  induction xs; intros ys Heqlist; destruct ys; simpl in *; try congruence.
  rewrite andb_true_iff in Heqlist; destruct Heqlist.
  erewrite -> IHxs by eassumption.
  reflexivity.
Qed.

Lemma eqlist_elem:
  forall {a} `{EqLaws a} (xs ys : list a) (x : a),
  eqlist xs ys = true ->
  List.elem x xs = List.elem x ys.
Proof.
  intros. revert ys H1.
  induction xs; intros ys H1; destruct ys; simpl in *; try congruence.
  rewrite andb_true_iff in H1; destruct H1.
  erewrite IHxs by eassumption.
  f_equal.
  rewrite eq_iff_eq_true.
  split; intro.
  - eapply Eq_trans; eassumption.
  - rewrite Eq_sym in H1. eapply Eq_trans; eassumption.
Qed.


Lemma sem_false_nil:
  forall s, (forall i, sem s i = false) -> s = Tip.
Proof.
  intros.
  destruct s; try reflexivity; exfalso.
  specialize (H e0).
  simpl in H.
  rewrite Eq_refl in H.
  rewrite orb_true_r in H.
  simpl in H.
  congruence.
Qed.

Lemma strongly_sorted_unique:
  forall (xs ys : list e),
  StronglySorted lt xs ->
  StronglySorted lt ys ->
  (forall x, List.elem x xs = List.elem x ys) ->
  eqlist xs ys = true.
Proof.
  intros.
  revert dependent ys.
  induction H; intros ys Hys Helem; inversion Hys; subst; clear Hys.
  * reflexivity.
  * specialize (Helem a). simpl in Helem. rewrite Eq_refl in Helem. inversion Helem.
  * specialize (Helem a). simpl in Helem. rewrite Eq_refl in Helem. inversion Helem.
  * simpl. rewrite andb_true_iff.
    assert (a == a0 = true).
    { clear IHStronglySorted.
      pose proof (Helem a) as Ha.
      pose proof (Helem a0) as Ha0.
      simpl in Ha, Ha0.
      rewrite Eq_refl in Ha, Ha0; rewrite ?orb_true_l, ?orb_true_r in Ha, Ha0.
      symmetry in Ha.
      rewrite orb_true_iff in Ha, Ha0.
      destruct Ha, Ha0; only 1-3 : order e; exfalso.
      pose proof (All_lt_elem _ _ _ H0 H4).
      pose proof (All_lt_elem _ _ _ H2 H3).
      order e.
    }
    split; try assumption.
    apply IHStronglySorted; clear IHStronglySorted.
      + assumption.
      + intros i.
        specialize (Helem i).
        simpl in Helem.
        destruct (List.elem i l) eqn:?, (List.elem i l0) eqn:?;
          rewrite ?orb_true_l, ?orb_true_r, ?orb_false_l, ?orb_false_r  in Helem;
          try reflexivity;
          try order e.
        - pose proof (All_lt_elem _ _ _ H0 Heqb). order e.
        - pose proof (All_lt_elem _ _ _ H2 Heqb0). order e.
Qed.

Lemma equals_spec:
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  s1 == s2 = true <-> (forall i, sem s1 i = sem s2 i).
Proof.
  intros.
  unfold op_zeze__, Eq___Set_, op_zeze____.
  unfold Internal.Eq___Set__op_zeze__.
  unfold op_zeze__, Eq_Integer___, Eq_list, op_zeze____.
  rewrite andb_true_iff.
  split; intro.
  * destruct H1.
    intro i.
    erewrite !toList_sem by eassumption.
    erewrite eqlist_elem by eassumption.
    reflexivity.
  * erewrite !size_spec by eassumption.
    assert (Heqlist : eqlist (toList s1) (toList s2) = true).
    { apply strongly_sorted_unique.
      * eapply to_List_sorted; eassumption.
      * eapply to_List_sorted; eassumption.
      * intros i; specialize (H1 i).
        erewrite !toList_sem in H1 by eassumption.
        assumption.
    }
    erewrite  eqlist_length by eassumption.
    rewrite Z.eqb_refl. intuition.
Qed.

(** ** Verification of [isSubsetOf] *)

Lemma isSubsetOfX_spec:
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  isSubsetOfX s1 s2 = true <-> (forall i, sem s1 i = true -> sem s2 i = true).
Proof.
  intros ???? HB1 HB2.
  revert dependent s2.
  induction HB1; intros; simpl; subst.
  * intuition.
  * destruct s0 eqn:Hs0.
    - rewrite <- Hs0 in *.
      clear s3 e0 s4 s5 Hs0.
      eapply splitMember_Desc; [solve_Bounded|].
      intros sr1 b sr2 HBsr1 HBsr2 Hsem.
      rewrite !andb_true_iff.
      rewrite IHHB1_1 by eassumption.
      rewrite IHHB1_2 by eassumption.
      split; intro; [destruct H1 as [?[??]] | split; [|split] ].
      -- intros i Hi.
         rewrite Hsem.
         rewrite !orb_true_iff in Hi.
         destruct Hi as [[Hi|Hi]|Hi];
         destruct (i == x);
         try reflexivity;
         try congruence;
         try apply H3 in Hi;
         try apply H4 in Hi;
         rewrite Hi;
         rewrite ?orb_true_l, ?orb_true_r; reflexivity.
     -- specialize (Hsem x).
        rewrite Eq_refl in Hsem. rewrite <- Hsem.
        apply H1.
        rewrite Eq_refl.
        rewrite ?orb_true_l, ?orb_true_r; reflexivity.
     -- intros i Hi.
        specialize (H1 i).
        rewrite Hi in H1.
        rewrite ?orb_true_l, ?orb_true_r in H1.
        rewrite Hsem in H1.
        specialize (H1 eq_refl).
        repeat (f_solver_step; f_solver_cleanup).
     -- intros i Hi.
        specialize (H1 i).
        rewrite Hi in H1.
        rewrite ?orb_true_l, ?orb_true_r in H1.
        rewrite Hsem in H1.
        specialize (H1 eq_refl).
        repeat (f_solver_step; f_solver_cleanup).
    - intuition.
      specialize (H1 x).
      rewrite Eq_refl, orb_true_r in H1.
      simpl in H1. intuition.
Qed.

Lemma subset_size:
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  (forall i, sem s1 i = true -> sem s2 i = true) ->
  (size s1 <= size s2)%Z.
Proof.
  intros ???? HB1 HB2 Hsubset.
  revert dependent s2.
  induction HB1; intros; simpl; subst.
  * simpl. solve_size.
  * assert (sem s0 x = true)
      by (apply Hsubset; simpl; rewrite Eq_refl, orb_true_r; reflexivity).
    assert (size s0 = let '(sl,sr) := split x s0 in 1 + size sl + size sr)%Z.
    { eapply splitS_Desc; [eassumption|]. intros. rewrite H1 in H5. lia. }
    rewrite H3.
    eapply splitS_Desc; [eassumption|]. intros.
    assert (size s1 <= size s3)%Z.
    { apply IHHB1_1; try assumption.
      intros i Hi.
      specialize (Hsubset i). simpl in Hsubset.
      rewrite Hi in Hsubset. rewrite orb_true_l in Hsubset.
      specialize (Hsubset eq_refl).
      rewrite H7 in Hsubset.
      repeat (f_solver_step; f_solver_cleanup).
    }
    assert (size s2 <= size s4)%Z.
    { apply IHHB1_2; try assumption.
      intros i Hi.
      specialize (Hsubset i). simpl in Hsubset.
      rewrite Hi in Hsubset. rewrite orb_true_r in Hsubset.
      specialize (Hsubset eq_refl).
      rewrite H7 in Hsubset.
      repeat (f_solver_step; f_solver_cleanup).
    }
    lia.
Qed.

Lemma isSubsetOf_spec:
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  isSubsetOf s1 s2 = true <-> (forall i, sem s1 i = true -> sem s2 i = true).
Proof.
  intros.
  unfold isSubsetOf.
  rewrite andb_true_iff.
  erewrite isSubsetOfX_spec by eassumption.
  intuition.
  unfold op_zlze__, Ord_Integer___, op_zlze____.
  rewrite Z.leb_le.
  eapply subset_size; eassumption.
Qed.


(** ** Verification of [filter] *)

(**
For filter we need two lemmas: We need to know that [filter P s] is
well-formed even if P does not respect equality (this is
required by the [FSetInterface]). But to prove something about its
semantics, we need to assume that [P] respects equality.
*)

Lemma filter_Bounded:
  forall (P : e -> bool) s lb ub,
  Bounded s lb ub ->
  Bounded (Internal.filter P s) lb ub.
Proof.
  intros.
  induction H.
  * simpl. solve_Bounded.
  * simpl.
    destruct (P x) eqn:HPx.
    - destruct_ptrEq.
      + solve_Bounded.
      + applyDesc link_Desc.
    - applyDesc merge_Desc.
Qed.

Lemma filter_Desc:
  forall (P : e -> bool) s lb ub,
  Bounded s lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) P ->
  Desc' (Internal.filter P s) lb ub (fun i => P i && sem s i).
Proof.
  intros.
  induction H.
  * simpl. solve_Desc.
  * simpl.
    applyDesc IHBounded1.
    applyDesc IHBounded2.
    destruct (P x) eqn:HPx.
    - destruct_ptrEq.
      + solve_Desc.
      + applyDesc link_Desc.
        solve_Desc.
    - applyDesc merge_Desc.
      solve_Desc.
Qed.

(** ** Verification of [partition] *)

Lemma partition_Bounded:
  forall p s lb ub,
  Bounded s lb ub ->
  forall (P : (Set_ e * Set_ e) -> Prop),
  (forall s1 s2, Bounded s1 lb ub /\ Bounded s2 lb ub -> P (s1, s2)) ->
  P (partition p s).
Proof.
  intros ???? HB.
  induction HB.
  * intros X HX; apply HX; clear X HX; split; solve_Bounded.
  * simpl.
    apply IHHB1; intros sl1 sl2 [HDsl1 HDsl2]; clear IHHB1.
    apply IHHB2; intros sr1 sr2 [HDsr1 HDsr2]; clear IHHB2.
    destruct (p x) eqn:?.
    - intros X HX; apply HX; clear X HX; split.
      + destruct_ptrEq.
        -- solve_Bounded.
        -- applyDesc link_Desc.
      + applyDesc merge_Desc.
    - intros X HX; apply HX; clear X HX; split.
      + applyDesc merge_Desc.
      + destruct_ptrEq.
        -- solve_Bounded.
        -- applyDesc link_Desc.
Qed.


Lemma partition_spec:
  forall p s lb ub,
  Bounded s lb ub ->
  Proper ((fun i j : e => i == j = true) ==> eq) p ->
  forall (P : (Set_ e * Set_ e) -> Prop),
  (forall s1 s2,
    Desc' s1 lb ub (fun i => p i && sem s i) /\
    Desc' s2 lb ub (fun i => negb (p i) && sem s i) ->
    P (s1, s2)) ->
  P (partition p s).
Proof.
  intros ???? HB HProper.
  induction HB.
  * intros X HX; apply HX; clear X HX; split; solve_Desc.
  * simpl.
    apply IHHB1; intros sl1 sl2 [HDsl1 HDsl2]; clear IHHB1.
    applyDesc HDsl1; clear HDsl1.
    applyDesc HDsl2; clear HDsl2.
    apply IHHB2; intros sr1 sr2 [HDsr1 HDsr2]; clear IHHB2.
    applyDesc HDsr1; clear HDsr1.
    applyDesc HDsr2; clear HDsr2.
    destruct (p x) eqn:?.
    - intros X HX; apply HX; clear X HX; split.
      + destruct_ptrEq.
        -- solve_Desc.
        -- applyDesc link_Desc.
           solve_Desc.
      + applyDesc merge_Desc.
        solve_Desc.
    - intros X HX; apply HX; clear X HX; split.
      + applyDesc merge_Desc.
        solve_Desc.
      + destruct_ptrEq.
        -- solve_Desc.
        -- applyDesc link_Desc.
           solve_Desc.
Qed.

(** ** Verification of [take] *)

Definition takeGo : Int -> Set_ e -> Set_ e.
Proof.
  let rhs := eval unfold take in (@take e) in
  match rhs with fun n s => if _ then _ else ?go _ _  => exact go end.
Defined.

Lemma take_neg: forall a n (l : list a), (n <= 0)%Z -> List.take n l = [].
Proof.
  intros. destruct l; simpl; destruct (Z.leb_spec n 0); try lia; try reflexivity.
Qed.

Lemma take_all:
  forall a n (xs : list a), (Z.of_nat (length xs) <= n)%Z -> List.take n xs = xs.
Proof.
  intros. revert n H.
  induction xs; intros n Hall.
  * simpl. destruct (Z.leb_spec n 0); reflexivity.
  * simpl.
    simpl length in Hall. rewrite Nat2Z.inj_succ, <- Z.add_1_l in Hall.
    rewrite IHxs by lia.
    destruct (Z.leb_spec n 0); [lia|reflexivity].
Qed.

Lemma take_app_cons:
  forall a n (l1 : list a) (x : a) (l2 : list a),
  List.take n (l1 ++ x :: l2) = match (n ?= Z.of_nat (length l1))%Z with
    | Lt => List.take n l1
    | Eq => l1
    | Gt => l1 ++ [x] ++ List.take (n - Z.of_nat (length l1) - 1)%Z l2
  end.
Proof.
  intros. revert n.
  induction l1; intros n.
  * simpl.
    rewrite Z.sub_0_r.
    destruct (Z.leb_spec n 0), (Z.compare_spec n 0)%Z; try reflexivity; lia.
  * cbn -[Z.add Z.of_nat].
    rewrite IHl1. clear IHl1.
    rewrite Nat2Z.inj_succ, <- Z.add_1_l.
    replace (n - (1 + Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    replace (n - 1 - (Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    destruct (Z.leb_spec n 0),
             (Z.compare_spec (n - 1) (Z.of_nat (length l1)))%Z,
             (Z.compare_spec n (1 + Z.of_nat (length l1)))%Z; try reflexivity; lia.
Qed.


Lemma takeGo_spec :
  forall n s lb ub,
  Bounded s lb ub ->
  forall (P : Set_ e -> Prop),
  (forall s',
    Bounded s' lb ub /\
    toList s' = List.take n (toList s) ->
    P s') ->
  P (takeGo n s).
Proof.
  intros ???? HD. revert n.
  induction HD; intros n.
  * intros X HX; apply HX. split.
    + simpl. destruct_match; solve_Bounded.
    + simpl. do 2 destruct_match; reflexivity.
  * simpl.
    intros X HX; apply HX.
    rewrite toList_Bin.
    unfold op_zlze__ , Ord_Integer___, op_zlze____.
    unfold compare , Ord_Integer___, compare__.
    rewrite size_size.
    apply IHHD1. intros s1' [HBs1' Hs1']. clear IHHD1.
    apply IHHD2. intros s2' [HBs2' Hs2']. clear IHHD2.
    destruct (Z.leb_spec n 0).
    + rewrite take_neg by assumption. split.
      - solve_Bounded.
      - reflexivity.
    + simpl app.
      rewrite take_app_cons.
      erewrite <- size_spec by eassumption.
      destruct (Z.compare_spec n (size s1)).
      - split.
        ** eapply Bounded_relax_ub; eassumption.
        ** reflexivity.
      - split.
        ** eapply Bounded_relax_ub; eassumption.
        ** assumption.
      - split.
        ** applyDesc link_Desc.
        ** erewrite toList_link by solve_Precondition.
           rewrite Hs2'.
           reflexivity.
Qed.

Lemma toList_take:
  forall n s lb ub,
  Bounded s lb ub ->
  forall (P : Set_ e -> Prop),
  (forall s',
    Bounded s' lb ub /\
    toList s' = List.take n (toList s) ->
    P s') ->
  P (take n s).
Proof.
  intros. apply H0.
  unfold take. fold takeGo.
  unfold op_zgze__ , Ord_Integer___, op_zgze____.
  rewrite size_size.
  destruct (Z.leb_spec (size s) n).
  * split; [assumption|].
    rewrite take_all. reflexivity.
    erewrite <- size_spec by eassumption.
    assumption.
  * eapply takeGo_spec; [solve_Precondition..|].
    intros. assumption.
Qed.

(** ** Verification of [drop] *)

Definition dropGo : Int -> Set_ e -> Set_ e.
Proof.
  let rhs := eval unfold drop in (@drop e) in
  match rhs with fun n s => if _ then _ else ?go _ _  => exact go end.
Defined.

Lemma drop_neg: forall a n (l : list a), (n <= 0)%Z -> List.drop n l = l.
Proof.
  intros. destruct l; simpl; destruct (Z.leb_spec n 0); try lia; try reflexivity.
Qed.

Lemma drop_all:
  forall a n (xs : list a), (Z.of_nat (length xs) <= n)%Z -> List.drop n xs = [].
Proof.
  intros. revert n H.
  induction xs; intros n Hall.
  * simpl. destruct (Z.leb_spec n 0); reflexivity.
  * simpl.
    simpl length in Hall. rewrite Nat2Z.inj_succ, <- Z.add_1_l in Hall.
    rewrite IHxs by lia.
    destruct (Z.leb_spec n 0); [lia|reflexivity].
Qed.

Lemma drop_app_cons:
  forall a n (l1 : list a) (x : a) (l2 : list a),
  List.drop n (l1 ++ x :: l2) = match (n ?= Z.of_nat (length l1))%Z with
    | Lt => List.drop n l1 ++ [x] ++ l2
    | Eq => [x] ++ l2
    | Gt => List.drop (n - Z.of_nat (length l1) - 1)%Z l2
  end.
Proof.
  intros. revert n.
  induction l1; intros n.
  * simpl.
    rewrite Z.sub_0_r.
    destruct (Z.leb_spec n 0), (Z.compare_spec n 0)%Z; try reflexivity; lia.
  * cbn -[Z.add Z.of_nat].
    rewrite IHl1. clear IHl1.
    rewrite Nat2Z.inj_succ, <- Z.add_1_l.
    replace (n - (1 + Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    replace (n - 1 - (Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    destruct (Z.leb_spec n 0),
             (Z.compare_spec (n - 1) (Z.of_nat (length l1)))%Z,
             (Z.compare_spec n (1 + Z.of_nat (length l1)))%Z; try reflexivity; lia.
Qed.


Lemma dropGo_spec :
  forall n s lb ub,
  Bounded s lb ub ->
  forall (P : Set_ e -> Prop),
  (forall s',
    Bounded s' lb ub /\
    toList s' = List.drop n (toList s) ->
    P s') ->
  P (dropGo n s).
Proof.
  intros ???? HD. revert n.
  induction HD; intros n.
  * intros X HX; apply HX. split.
    + simpl. destruct_match; solve_Bounded.
    + simpl. do 2 destruct_match; reflexivity.
  * simpl.
    intros X HX; apply HX.
    rewrite toList_Bin.
    unfold op_zlze__ , Ord_Integer___, op_zlze____.
    unfold compare , Ord_Integer___, compare__.
    rewrite size_size.
    apply IHHD1. intros s1' [HBs1' Hs1']. clear IHHD1.
    apply IHHD2. intros s2' [HBs2' Hs2']. clear IHHD2.
    destruct (Z.leb_spec n 0).
    + rewrite drop_neg by assumption. split.
      - solve_Bounded.
      - rewrite toList_Bin.
        reflexivity.
    + simpl app.
      rewrite drop_app_cons.
      erewrite <- size_spec by eassumption.
      destruct (Z.compare_spec n (size s1)).
      - split.
        ** applyDesc insertMin_Desc.
        ** erewrite toList_insertMin  by solve_Precondition.
           reflexivity.
      - split.
        ** applyDesc link_Desc.
        ** erewrite toList_link by solve_Precondition.
           rewrite Hs1'.
           reflexivity.
      - split.
        ** eapply Bounded_relax_lb; eassumption.
        ** assumption.
Qed.

Lemma toList_drop:
  forall n s lb ub,
  Bounded s lb ub ->
  forall (P : Set_ e -> Prop),
  (forall s',
    Bounded s' lb ub /\
    toList s' = List.drop n (toList s) ->
    P s') ->
  P (drop n s).
Proof.
  intros. apply H0.
  unfold drop. fold dropGo.
  unfold op_zgze__ , Ord_Integer___, op_zgze____.
  rewrite size_size.
  destruct (Z.leb_spec (size s) n).
  * split; [solve_Precondition|].
    rewrite drop_all. reflexivity.
    erewrite <- size_spec by eassumption.
    assumption.
  * eapply dropGo_spec; [solve_Precondition..|].
    intros. assumption.
Qed.

(** ** Verification of [splitAt] *)

Definition splitAtGo : Int -> Set_ e -> (Set_ e * Set_ e).
Proof.
  let rhs := eval unfold splitAt in (@splitAt e) in
  match rhs with fun n s => if _ then _ else Datatypes.id (?go _ _)  => exact go end.
Defined.

Lemma splitAtGo_spec :
  forall n s, splitAtGo n s = (takeGo n s, dropGo n s).
Proof.
  intros ??.
  revert n.
  induction s; intros n.
  * simpl.
    repeat destruct_match; try congruence.
  * simpl. repeat destruct_match; reflexivity.
Qed.

(** ** Verification of [valid] *)

(* This is nicer than the [bounded] in [ordered],
   because it is compatible with [isLB] and [isUB] *)
Fixpoint bounded' lo hi t :=
  match t with
  | Bin _ x l r =>
    lo x && (hi x &&
         (bounded' lo (isUB (Some x)) l &&
          bounded' (isLB (Some x)) hi r))
    | Tip => true
  end.

Lemma ordered_bounded': forall t, ordered t = bounded' (isLB None) (isUB None) t.
Proof.
  intro t.
  unfold ordered.
  lazymatch goal with |- ?b _ _ _ = _ => set (bounded := b) end.
  enough (forall lo lo' hi hi',
    (forall x, lo x = lo' x) -> (forall x, hi x = hi' x) ->
    bounded lo hi t = bounded' lo' hi' t)
    by (apply H; intro; reflexivity).
  induction t; intros; simpl.
  * erewrite !H, !H0, IHt1, IHt2; auto.
    intro; simpl; rewrite Ord_lt_le, Ord_gt_le; reflexivity.
  * reflexivity.
Qed.

Require Import Tactics.

(* This is a copy of the local fixpoint from Haskell’s [validsize] function. *)

Definition realsize :=
  fix realsize (t' : Set_ e) : option Size :=
    match t' with
    | Bin sz _ l r =>
      match realsize l with
      | Some n =>
        match realsize r with
        | Some m =>
          if _GHC.Base.==_ (_GHC.Num.+_ (_GHC.Num.+_ n m) #1) sz
          then Some sz
          else None
        | None => None
        end
      | None => None
      end
    | Tip => Some #0
    end.

Lemma validsize_realsize : forall s,
    validsize s = true <-> realsize s = Some (size s).
Proof.
  intros.
  change (realsize s == Some (size s) = true  <-> realsize s = Some (size s)).
  unfold op_zeze__, Eq___option, op_zeze____, Base.Eq___option_op_zeze__.
  unfold op_zeze__, Eq_Integer___, op_zeze____.
  destruct (realsize s); try rewrite  Z.eqb_eq; simpl;
  intuition (subst; congruence || reflexivity).
Qed.

Lemma validsize_children : forall l (a : e) s1 s2,
    validsize (Bin l a s1 s2) = true ->
    validsize s1 = true /\ validsize s2 = true.
Proof.
  split.
  - destruct s1; unfold validsize in *.
    + intros. repeat destruct_match; try ssreflect.done.
      rewrite size_size in *. cbn.
      rewrite Z.eqb_eq. inversion Heq; reflexivity.
    + reflexivity.
  - destruct s2; unfold validsize in *.
    + intros. repeat destruct_match; try ssreflect.done.
      rewrite size_size in *. cbn.
      rewrite Z.eqb_eq. inversion Heq0; reflexivity.
    + reflexivity.
Qed.

Lemma Bounded_valid' : forall s lb ub,
    Bounded s lb ub <->
    (balanced s = true /\ bounded' (isLB lb) (isUB ub) s = true /\ validsize s = true).
Proof.
  intros s lb ub. split.
  - induction 1; (split; [|split]); try reflexivity;
      destruct IHBounded1 as [IHb1 [IHbd1 IHv1]];
      destruct IHBounded2 as [IHb2 [IHbd2 IHv2]].
    + cbn -[Z.add Z.mul]. rewrite size_size.
      repeat rewrite andb_true_iff.
      split; [| split]; try assumption.
      unfold balance_prop in H4.
      rewrite orb_true_iff.
      rewrite andb_true_iff. cbn -[Z.mul].
      repeat rewrite Z.leb_le.
      assumption.
    + simpl.
      rewrite H1, H2, IHbd1, IHbd2. reflexivity.
    + unfold validsize.
      repeat destruct_match; try ssreflect.done; rewrite size_size;
        unfold validsize in IHv1, IHv2;
        rewrite Heq in IHv1.
      * cbn. rewrite Z.eqb_eq; reflexivity.
      * rewrite Heq0 in IHv2.
        rewrite size_size in IHv1, IHv2. cbn in IHv1, IHv2.
        rewrite Z.eqb_neq in Heq1. exfalso.
        apply Heq1. cbn. rewrite H3.
        rewrite Z.eqb_eq in IHv1, IHv2; subst. lia.
      * rewrite Heq0 in IHv2. cbn in IHv2. congruence.
      * cbn in IHv1; congruence.
  - revert lb ub. induction s.
    + intros.
      destruct H as [? [? ?]].
      simpl in H0. repeat rewrite andb_true_iff in H0.
      destruct H0 as [? [? [? ?]]].
      cbn -[Z.mul] in H. repeat rewrite andb_true_iff in H.
      destruct H as [? [? ?]].
      constructor;
        try solve [apply validsize_children in H1; destruct H1; auto].
      * pose proof validsize_children _ _ _ _ H1.
        destruct H7. apply validsize_realsize in H1.
        apply validsize_realsize in H7.
        apply validsize_realsize in H8.
        simpl in H1. revert H1.
        destruct (realsize s2) eqn:Hrs1;
          destruct (realsize s3) eqn:Hrs2; try congruence.
        match goal with
         |- context[if ?a then _ else _] =>
         destruct a eqn:Heq
        end; try congruence.
        intro. cbn in Heq. apply Z.eqb_eq in Heq.
        inversion H7; inversion H8; subst. lia.
      * unfold balance_prop. rewrite size_size in H.
        rewrite orb_true_iff, andb_true_iff in H.
        repeat rewrite Z.leb_le in H. assumption.
    + simpl. intros. constructor.
Qed.

Lemma Bounded_iff_valid : forall s,
    WF s <-> valid s = true.
Proof.
  intros s. unfold valid.
  rewrite ordered_bounded'.
  repeat rewrite andb_true_iff. split.
  - intros. apply Bounded_valid' in H. intuition.
  - intros. apply Bounded_valid'. intuition.
Qed.

End WF.

(** ** Verification of [map] *)

Lemma elem_map:
  forall a b `{Eq_ b} (f : a -> b) (xs : list a) i,
  List.elem i (List.map f xs) = existsb (fun j : a => i == f j) xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. rewrite IHxs. reflexivity.
Qed.

Lemma map_spec:
  forall e ee `{Ord e} `{OrdLaws ee} (f : e -> ee) (s : Set_ e) lb ub,
  Bounded s lb ub ->
  (forall i, sem (map f s) i = existsb (fun j => i == f j) (toList s)).
Proof.
  intros.
  unfold map.
  unfold Base.map.
  simpl.
  eapply fromList_Desc. intros s' Hs' _ Hsem'.
  rewrite Hsem'.
  apply elem_map.
Qed.

(** ** Verification of [mapMonotonic] *)

Lemma mapMonotonic_Desc:
  forall e ee `{Ord e}`{Ord ee} (f : e -> ee) (s : Set_ e) lb ub,
  (forall x y, (f x < f y) = (x < y)) ->
  (forall x y, (f x == f y) = (x == y)) ->
  Bounded s lb ub ->
  forall (P : Set_ ee -> Prop),
  (forall s',
    Bounded s' (option_map f lb) (option_map f ub) ->
    size s' = size s ->
    (forall i, sem s' (f i) = sem s i) ->
    P s'
  ) ->
  P (mapMonotonic f s).
Proof.
  intros ? ? HEq HOrd HHEq HHOrd f s lb ub Hcompatlt Hcompateq H.
  induction H.
  * intros X HX. simpl. apply HX.
    - constructor.
    - reflexivity.
    - intro. reflexivity.
  * simpl. simpl option_map in *.
    eapply IHBounded1. intros s'l H'l Hsizel Hfl. clear IHBounded1.
    eapply IHBounded2. intros s'r H'r Hsizer Hfr. clear IHBounded2.
    intros X HX. simpl. apply HX.
    - constructor.
      + assumption.
      + assumption.
      + destruct lb; try reflexivity; simpl. rewrite Hcompatlt. assumption.
      + destruct ub; try reflexivity; simpl. rewrite Hcompatlt. assumption.
      + lia.
      + rewrite Hsizel, Hsizer. assumption.
    - reflexivity.
    - intro j.
      simpl.
      rewrite Hfl, Hfr, Hcompateq.
      reflexivity.
Qed.



(** ** [IntSet]s with [WF] *)

Definition WFSet  (e : Type) `{Ord e} : Type := {s : Set_ e | WF s}.
Definition pack   {e : Type} `{Ord e} : forall (s : Set_ e), WF s -> WFSet e := exist _.
Definition unpack {e : Type} `{Ord e} : WFSet e                   -> Set_  e := @proj1_sig _ _.

(** * Type classes *)

(** Because a [Set_ e] is only useful if it well-formed, we instantiate
the law classes with a subset type. *)

Require Import Proofs.GHC.Base.

Section TypeClassLaws.
Context {e : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(** ** Verification of [Eq] *)

Global Program Instance Eq_Set_WF : Eq_ (WFSet e) := fun _ k => k
  {| op_zeze____ := @op_zeze__ (Set_ e) _
   ; op_zsze____ := @op_zsze__ (Set_ e) _
  |}.

Local Ltac unfold_WFSet_Eq :=
  unfold "_==_", "_/=_", Eq_Set_WF; simpl;
  unfold "_==_", "_/=_", Eq___Set_; simpl;
  unfold Data.Set.Internal.Eq___Set__op_zsze__, Data.Set.Internal.Eq___Set__op_zeze__; simpl.

Global Instance EqLaws_Set : EqLaws (WFSet e).
Proof.
  constructor.
  - now intros x; unfold_WFSet_Eq; rewrite !Eq_refl.
  - now intros x y; unfold_WFSet_Eq; f_equal; rewrite Eq_sym.
  - intros x y z; unfold_WFSet_Eq; rewrite <-!(ssrbool.rwP ssrbool.andP);
      intros [size_xy list_xy] [size_yz list_yz].
    now split; eapply Eq_trans; eassumption.
  - now intros x y; unfold_WFSet_Eq; rewrite negb_involutive.
Qed.


(** ** Verification of [Ord] *)

Global Program Instance Ord_Set_WF : Ord (WFSet e) := fun _ k => k
  {| op_zlze____ := @op_zlze__ (Set_ e) _ _
   ; op_zgze____ := @op_zgze__ (Set_ e) _ _
   ; op_zl____ := @op_zl__ (Set_ e) _ _
   ; op_zg____ := @op_zg__ (Set_ e) _ _
   ; compare__ := @compare (Set_ e) _ _
   ; min__ := @min (Set_ e) _ _
   ; max__ := @max (Set_ e) _ _
  |}.
Next Obligation.
  destruct x as [s1 HB1], x0 as [s2 HB2]. simpl.
  unfold max, Ord__Set_, max__, Internal.Ord__Set__max.
  destruct (Internal.Ord__Set__op_zlze__ _ _); assumption.
Qed.
Next Obligation.
  destruct x as [s1 HB1], x0 as [s2 HB2]. simpl.
  unfold min, Ord__Set_, min__, Internal.Ord__Set__min.
  destruct (Internal.Ord__Set__op_zlze__ _ _); assumption.
Qed.

Lemma compare_neq_gt_iff_le {t} `{OrdLaws t} (l1 l2 : t) :
  (compare l1 l2 /= Gt = true) <-> (l1 <= l2) = true.
Proof.
  rewrite Neq_inv, negb_true_iff.
  destruct (_ <= _) eqn:LE; simpl.
  - split; trivial; intros _.
    enough ((compare l1 l2 == Gt) = false <-> compare l1 l2 <> Gt) as OK.
    + now apply OK; rewrite Ord_compare_Gt, LE.
    + now rewrite (ssrbool.rwP (Eq_eq _ Gt)); unfold is_true; rewrite not_true_iff_false.
  - now rewrite <-Ord_compare_Gt in LE; rewrite LE.
Qed.

Lemma WFSet_eq_size_length' (a : WFSet e) :
  Data.Set.Internal.size (proj1_sig a) = Z.of_nat (Datatypes.length (toAscList (proj1_sig a))).
Proof.
  destruct a as [a WFa]; unfold "==", Eq_Set_WF; simpl.
  rewrite size_size; erewrite size_spec; trivial; exact WFa.
Qed.

Lemma WFSet_eq_size_length (a : WFSet e) :
  Data.Set.Internal.size (unpack a) = Z.of_nat (Datatypes.length (toAscList (unpack a))).
Proof. apply WFSet_eq_size_length'. Qed.


Local Ltac unfold_WFSet_Ord :=
  unfold "_<=_", "_<_", "_>=_", "_>_", compare, Ord_Set_WF; simpl;
  unfold "_<=_", "_<_", "_>=_", "_>_", compare, Ord__Set_; simpl;
  unfold Data.Set.Internal.Ord__Set__op_zlze__, Data.Set.Internal.Ord__Set__op_zl__,
         Data.Set.Internal.Ord__Set__op_zgze__, Data.Set.Internal.Ord__Set__op_zg__,
         Data.Set.Internal.Ord__Set__compare; simpl.




Local Ltac hideToAscList a :=
  let la := fresh "l" a in
  let EQ := fresh "EQ"  in
  remember (toAscList (unpack a)) as la eqn:EQ; try clear a EQ.

(* Hastily converted from an SSReflect proof -- could probably be cleaned up.
   (This is not the only proof like that.) --ASZ *)
Global Instance OrdLaws_Set : OrdLaws (WFSet e).
Proof.
  constructor; unfold_WFSet_Eq; unfold_WFSet_Ord.
  - intros a b; rewrite !compare_neq_gt_iff_le => LEab LEba.
    generalize (Ord_antisym _ _ LEab LEba) => EQab.
    match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP ssrbool.andP); split; trivial.
    rewrite !WFSet_eq_size_length'; rewrite <-(ssrbool.rwP (Eq_eq _ _)).
    rewrite Nat2Z.inj_iff; apply eqlist_length, EQab.
  - intros a b c; rewrite !compare_neq_gt_iff_le; order (list e).
  - intros a b; rewrite !compare_neq_gt_iff_le; apply Ord_total.
  - intros a b; rewrite Ord_compare_Lt,Neq_inv,negb_false_iff.
    match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP (Eq_eq _ _)).
    order (list e).
  - intros a b; rewrite Ord_compare_Eq.
    repeat match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP ssrbool.andP), <-(ssrbool.rwP (Eq_eq _ _)).
    split; [intros EQ | intros [LIST EQ]]; rewrite EQ; trivial.
    split; trivial. rewrite !WFSet_eq_size_length'.
    rewrite Nat2Z.inj_iff; apply eqlist_length, EQ. apply Eq_refl.
    apply Eq_refl.
  - intros a b; rewrite Ord_compare_Gt,Neq_inv,negb_false_iff.
    match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP (Eq_eq _ _)).
    order (list e).
  - now intros a b; rewrite  Neq_inv, negb_involutive, compare_flip; destruct (compare _ _).
  - now intros a b; rewrite !Neq_inv,                  compare_flip; destruct (compare _ _).
  - now intros a b; rewrite  Neq_inv, negb_involutive, compare_flip; destruct (compare _ _).
Qed.

(** ** Verification of [Semigroup] *)

Ltac unfold_Monoid_Set :=
  unfold mappend, mconcat, mempty, Monoid__Set_, mappend__, mconcat__, mempty__,
         Internal.Monoid__Set__mappend, Internal.Monoid__Set__mconcat, Internal.Monoid__Set__mempty,
         op_zlzlzgzg__,  Semigroup__Set_, op_zlzlzgzg____,
         Internal.Semigroup__Set__op_zlzlzgzg__
    in *.

Global Program Instance Semigroup_WF : Semigroup (WFSet e) := fun _ k => k
  {| op_zlzlzgzg____  := @mappend (Set_ e) _ _ |}.
Next Obligation.
  destruct x as [s1 HB1], x0 as [s2 HB2]. simpl.
  unfold_Monoid_Set.
  eapply union_Desc; try eassumption. intuition.
Qed.


Global Instance SemigroupLaws_Set : SemigroupLaws (WFSet e).
Proof.
  constructor.
  intros.
  destruct x as [s1 HB1], y as [s2 HB2], z as [s3 HB3].
  unfold op_zeze__, Eq_Set_WF, op_zeze____, proj1_sig.
  unfold op_zlzlzgzg__, Semigroup_WF, op_zlzlzgzg____.
  unfold mappend, Monoid__Set_, mappend__.
  unfold Internal.Monoid__Set__mappend.
  unfold proj1_sig.
  unfold op_zlzlzgzg__, Semigroup__Set_, op_zlzlzgzg____.
  unfold Internal.Semigroup__Set__op_zlzlzgzg__.
  eapply (union_Desc s1 s2); try eassumption. intros s12 Hs12 _ Hsem12.
  eapply (union_Desc s2 s3); try eassumption. intros s23 Hs23 _ Hsem23.
  eapply (union_Desc s1 s23); try eassumption. intros s1_23 Hs1_23 _ Hsem1_23.
  eapply (union_Desc s12 s3); try eassumption. intros s12_3 Hs12_3 _ Hsem12_3.
  rewrite -> equals_spec by eassumption.
  intro i. rewrite Hsem12_3,Hsem1_23,Hsem23,Hsem12.
  rewrite orb_assoc. reflexivity.
Qed.

(** ** Verification of [Monoid] *)

Global Program Instance Monoid_WF : Monoid (WFSet e) := fun _ k => k
  {| mempty__   := @mempty (Set_ e) _ _
   ; mappend__  := @mappend (Set_ e) _ _
   ; mconcat__  xs := @mconcat (Set_ e) _ _ (List.map (fun x => unpack x) xs)
  |}.
Next Obligation.
  destruct x as [s1 HB1], x0 as [s2 HB2]. simpl.
  unfold_Monoid_Set.
  eapply union_Desc; try eassumption. intuition.
Qed.
Next Obligation.
  unfold_Monoid_Set.
  eapply unions_Desc.
  * induction xs.
    + constructor.
    + destruct a as [s HB]. simpl. constructor. apply HB. apply IHxs.
  * intros. assumption.
Qed.
Next Obligation.
  unfold_Monoid_Set.
  eapply empty_Desc.
  eauto.
Qed.

Lemma unions_foldr_union:
  forall (ss : list (Set_ e)),
  Forall WF ss -> (unions ss == Base.foldr union empty ss) = true.
Proof.
  intros.
  assert (Desc' (Base.foldr union empty ss) None None (fun i => existsb (fun s => sem s i) ss)). {
    induction H.
    * simpl. eapply empty_Desc; intros. apply showDesc'. eauto.
    * simpl.
      apply IHForall. intros.
      eapply union_Desc; try eassumption; intros.
      apply showDesc'. intuition. rewrite H6,H3. reflexivity.
  }
  eapply H0. intros.
  eapply unions_Desc; try eassumption; intros.
  rewrite -> equals_spec by eassumption.
  intro i. rewrite H6,H3. reflexivity.
Qed.

Global Instance MonoidLaws_Set : MonoidLaws (WFSet e).
Proof.
  constructor;
    unfold op_zeze__, Eq_Set_WF, op_zeze____,  unpack;
    repeat unfold mappend, mconcat, mempty, Monoid_WF, mappend__, mconcat__, mempty__,
      Internal.Monoid__Set__mappend, Internal.Monoid__Set__mempty,
      op_zlzlzgzg__,  Semigroup__Set_, Semigroup_WF, op_zlzlzgzg____,
      Internal.Semigroup__Set__op_zlzlzgzg__,
      mappend, mempty, Monoid__Set_, mappend__, mempty__,
      Internal.Monoid__Set__mappend, Internal.Monoid__Set__mempty, Internal.Monoid__Set__mconcat.
  * intros. destruct x as [s Hs]; unfold proj1_sig.
    eapply empty_Desc. intros.
    eapply union_Desc; try eassumption; intros.
    rewrite -> equals_spec by eassumption.
    intro i. rewrite H4,H1. reflexivity.
  * intros. destruct x as [s Hs]; unfold proj1_sig.
    eapply empty_Desc. intros.
    eapply union_Desc; try eassumption; intros.
    rewrite -> equals_spec by eassumption.
    intro i. rewrite H4,H1. rewrite orb_false_r. reflexivity.
  * intros. destruct x as [s1 Hs1], y as [s2 Hs2]; unfold proj1_sig.
    eapply union_Desc; try eassumption; intros.
    rewrite -> equals_spec by eassumption.
    reflexivity.
  * intros.
    rename x into xs.
    lazymatch goal with |- (_ == ?y) = true  =>
      replace y with (Base.foldr union  empty (List.map (fun x => unpack x) xs))
    end.
    + apply unions_foldr_union.
      induction xs.
      - constructor.
      - destruct a as [s Hs]; unfold unpack.
        constructor; assumption.
    + induction xs.
      - reflexivity.
      - simpl in *.
        f_equal.
        assumption.
Qed.

End TypeClassLaws.


(** ** Verification of [Eq1] *)
Require Import Data.Functor.Classes.
Require Import Proofs.Data.Functor.Classes.
Global Instance Eq1Laws_list: Eq1Laws list (@Eq_list).
Proof.
  constructor.
  intros ? ? xs ys.
  unfold liftEq, Eq1__list, liftEq__.
  replace (xs == ys) with (eqlist xs ys) by reflexivity.
  revert ys.
  induction xs; intros ys.
  * reflexivity.
  * destruct ys.
    - reflexivity.
    - simpl. rewrite IHxs. reflexivity.
Qed.

Global Instance Eq1Laws_Set : Eq1Laws Set_ (@Eq___Set_).
Proof.
  split.
  intros.
  unfold liftEq, Eq1__Set_, liftEq__, Internal.Eq1__Set__liftEq.
  rewrite Eq1_same.
  reflexivity.
Qed.


(** ** Verification of [Ord1] *)

Global Instance Ord1Laws_list: Ord1Laws list (@Eq_list) (@Ord_list).
Proof.
  constructor.
  intros ??? xs ys.
  unfold liftCompare, Ord1__list, liftCompare__.
  revert ys.
  induction xs; intros ys.
  * reflexivity.
  * destruct ys.
    - reflexivity.
    - simpl. rewrite IHxs. reflexivity.
Qed.

Global Instance Ord1Laws_Set : Ord1Laws Set_ (@Eq___Set_) (@Ord__Set_).
Proof.
  split.
  intros.
  unfold liftCompare, Ord1__Set_, liftCompare__, Internal.Ord1__Set__liftCompare.
  rewrite Ord1_same.
  reflexivity.
Qed.

(** * Instantiating the [FSetInterface] *)

Require Import Coq.FSets.FSetInterface.
Require OrdTheories.

Module SetFSet (E : OrderedType) <: WSfun(E) <: WS <: Sfun(E) <: S.
  Module E := E.

  Include OrdTheories.OrdTheories E.

  Lemma E_eq_zeze:
    forall x y : elt, E.eq x y <-> (x == y) = true.
  Proof. apply elt_eq. Qed.

  Lemma E_lt_zl:
    forall x y : elt, E.lt x y <-> (x < y) = true.
  Proof. apply elt_lt. Qed.

  Lemma InA_Eeq_elem:
    forall x xs,
    InA E.eq x xs <-> List.elem x xs = true.
  Proof.
    intros.
    induction xs.
    * simpl. split; intro; inversion H.
    * simpl. rewrite InA_cons, orb_true_iff, IHxs, elt_eq. reflexivity.
  Qed.

  Lemma compat_bool_Eeq_op_zeze:
    forall f, compat_bool E.eq f ->
    Proper ((fun i j : elt => i == j = true) ==> eq) f.
  Proof.
    intros.
    intros i j Heq.
    rewrite <- E_eq_zeze in Heq.
    apply H. assumption.
  Qed.

  (* Well-formedness *)
  Definition t := {s : Set_ elt | Bounded s None None}.
  Program Definition In (x :elt) (s : t) : Prop := sem s x = true.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.

  Program Definition empty : t := empty.
  Next Obligation. constructor. Defined.

  Program Definition is_empty : t -> bool := null.

  (* IntSet comparison predicate *)

  Definition lt (s s' : t) : Prop := (s < s') = true.

  (* More information later, after we've proved theorems *)

  (* Minimal and maximal elements *)

  Definition min_elt : t -> option elt := lookupMin ∘ unpack.

  Definition max_elt : t -> option elt := lookupMax ∘ unpack.

  (* Theorems *)

  Lemma empty_1 : Empty empty.
  Proof. intros x H. inversion H. Qed.

  Lemma Empty_tip : forall s, Empty s <-> unpack s = Tip.
  Proof.
    unfold unpack, WF. (* Get the implicit parameters right *)
    intros. split; intro.
    * destruct s as [[|]?].
      + exfalso. specialize (H e).
        contradict H.
        unfold In. simpl. rewrite Eq_refl, orb_true_r. reflexivity.
      + reflexivity.
    * intros x H1. inversion H1. rewrite H in H2. inversion H2.
  Qed.

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    intros.
    rewrite Empty_tip in *.
    unfold is_empty, unpack, WF in *.
    rewrite H. reflexivity.
  Qed.

  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof.
    intros.
    rewrite Empty_tip in *.
    unfold is_empty, unpack, WF in *.
    destruct (proj1_sig s); [ inversion H | reflexivity].
  Qed.

  Definition eq : t -> t -> Prop := Equal.
  Definition eq_dec : forall s s' : t, {eq s s'} + {~ eq s s'}.
  Proof.
    intros.
    destruct s as [s1 ?], s' as [s2 ?].
    unfold eq, Equal, In, proj1_sig.
    destruct (s1 == s2) eqn:?.
    * left. intro i.  apply eq_iff_eq_true. eapply equals_spec; try eassumption.
    * right.
      assert (~ (forall a : elt, sem s1 a = sem s2 a)).
      { rewrite <- equals_spec by eassumption.
        rewrite not_true_iff_false. assumption.
      }
      contradict H. intro i. apply eq_iff_eq_true. apply H.
  Qed.

  Lemma eq_refl : forall s : t, eq s s.
  Proof. destruct s. unfold eq. unfold Equal. intro. reflexivity. Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. destruct s; destruct s';
    unfold eq, Equal in *. intros. rewrite H. intuition. Qed.

  Lemma eq_trans :
    forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
    destruct s; destruct s'; destruct s''; simpl.
    unfold eq, Equal. intros ???. rewrite H, H0. reflexivity.
  Qed.

  Program Definition mem : elt -> t -> bool := member.

  Program Definition singleton : elt -> t := singleton.
  Next Obligation. eapply singleton_Desc with (ub := None) (lb := None); intuition. Qed.

  Program Definition add : elt -> t -> t := insert.
  Next Obligation.
    destruct x0. simpl.
    eapply insert_Desc with (ub := None) (lb := None); intuition.
  Qed.

  Program Definition remove : elt -> t -> t := delete.
  Next Obligation.
    destruct x0. simpl.
    eapply delete_Desc with (ub := None) (lb := None); intuition.
  Qed.

  Program Definition union : t -> t -> t := union.
  Next Obligation.
    destruct x, x0. simpl.
    eapply union_Desc with (ub := None) (lb := None); intuition.
  Qed.

  Program Definition inter : t -> t -> t:= intersection.
  Next Obligation.
    destruct x, x0. simpl.
    eapply intersection_Desc with (ub := None) (lb := None);intuition.
  Qed.

  Program Definition diff : t -> t -> t := difference.
  Next Obligation.
    destruct x, x0. simpl.
    eapply difference_Desc with (ub := None) (lb := None); intuition.
  Qed.

  Program Definition equal : t -> t -> bool := fun s1 s2 => @op_zeze__ (Set_ elt) _ s1 s2.
  Program Definition subset : t -> t -> bool := isSubsetOf.

  Program Definition fold : forall A : Type, (elt -> A -> A) -> t -> A -> A
    := fun a k s n => foldl (fun x e => k e x) n s.

  Program Definition filter : (elt -> bool) -> t -> t := filter.
  Next Obligation.
    destruct x0. simpl.
    eapply filter_Bounded with (ub := None) (lb := None); assumption.
  Qed.

  Program Definition partition : (elt -> bool) -> t -> t * t := partition.
  Next Obligation.
    destruct x0. simpl.
    eapply partition_Bounded with (ub := None) (lb := None); intuition.
  Qed.
  Next Obligation.
    destruct x0. simpl.
    eapply partition_Bounded with (ub := None) (lb := None); intuition.
  Qed.

  Program Definition cardinal : t -> nat := fun s => Z.to_nat (size s).
  Program Definition elements : t -> list elt := toList.

  Lemma In_1 :
    forall (s : t) (x y : elt), E.eq x y -> In x s -> In y s.
  Proof.
    intros [s?] x y Heq.
    rewrite E_eq_zeze in Heq.
    unfold In, unpack.
    rewrite (sem_resp_eq _ _ _ Heq).
    intuition.
  Qed.

  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof.
    intros. destruct s. unfold In, mem in *. simpl in *.
    erewrite member_spec; eassumption.
  Qed.

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof.
    intros. destruct s. unfold In, mem in *. simpl in *.
    erewrite member_spec in H; eassumption.
  Qed.

  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true.
  Proof.
    intros [s1?] [s2?].
    unfold Equal, equal, In, unpack.
    rewrite equals_spec by eassumption.
    intros. apply eq_iff_eq_true. apply H.
  Qed.

  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
  Proof.
    intros [s1?] [s2?].
    unfold Equal, equal, In, unpack.
    rewrite equals_spec by eassumption.
    intros. apply eq_iff_eq_true. apply H.
  Qed.

  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true.
  Proof.
    intros [s1?] [s2?].
    unfold Subset, subset, In, unpack.
    rewrite isSubsetOf_spec by eassumption.
    intuition.
  Qed.

  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
  Proof.
    intros [s1?] [s2?].
    unfold Subset, subset, In, unpack.
    rewrite isSubsetOf_spec by eassumption.
    intuition.
  Qed.

  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> E.eq x y.
  Proof.
    intros x y.
    unfold In, singleton, proj1_sig.
    rewrite E_eq_zeze.
    eapply singleton_Desc with (ub := None) (lb := None); try reflexivity.
    intros.
    simpl in H1.
    unfold elt in *.
    rewrite H1 in H2.
    rewrite Eq_sym in H2.
    assumption.
  Qed.

  Lemma singleton_2 :
    forall x y : elt, E.eq x y -> In y (singleton x).
  Proof.
    intros x y.
    unfold In, singleton, proj1_sig.
    rewrite E_eq_zeze.
    eapply singleton_Desc with (ub := None) (lb := None); try reflexivity.
    intros.
    unfold elt in *. rewrite H1.
    rewrite Eq_sym.
    assumption.
  Qed.

  Lemma add_1 :
    forall (s : t) (x y : elt), E.eq x y -> In y (add x s).
  Proof.
    intros [s Hs] x y.
    unfold In, add, proj1_sig.
    rewrite E_eq_zeze.
    eapply insert_Desc with (ub := None) (lb := None); try assumption; try reflexivity.
    intros.
    unfold elt in *. rewrite H1.
    rewrite Eq_sym.
    rewrite H2. reflexivity.
  Qed.

  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s).
  Proof.
    intros [s Hs] x y.
    unfold In, add, proj1_sig.
    eapply insert_Desc with (ub := None) (lb := None); try assumption; try reflexivity.
    intros.
    unfold elt in *. rewrite H1, H2.
    rewrite orb_true_r.
    reflexivity.
  Qed.

  Lemma add_3 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y (add x s) -> In y s.
  Proof.
    intros [s Hs] x y.
    unfold In, add, proj1_sig.
    rewrite E_eq_zeze.
    eapply insert_Desc with (ub := None) (lb := None); try assumption; try reflexivity.
    intros.
    unfold elt in *. rewrite H1 in H3.
    rewrite Eq_sym in H3.
    rewrite orb_true_iff in H3. destruct H3 as [H3|H3].
    * congruence.
    * assumption.
  Qed.

  Lemma remove_1 :
    forall (s : t) (x y : elt), E.eq x y -> ~ In y (remove x s).
  Proof.
    intros [s Hs] x y.
    unfold In, remove, proj1_sig.
    rewrite E_eq_zeze.
    eapply delete_Desc with (ub := None) (lb := None); try assumption; try reflexivity.
    intros.
    unfold elt in *.
    rewrite H1.
    rewrite Eq_sym in H2.
    rewrite H2. simpl.
    rewrite andb_false_r.
    congruence.
  Qed.

  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y s -> In y (remove x s).
  Proof.
    intros [s Hs] x y.
    unfold In, remove, proj1_sig.
    rewrite E_eq_zeze.
    eapply delete_Desc with (ub := None) (lb := None); try assumption; try reflexivity.
    intros.
    unfold elt in *.
    rewrite H1, H3.
    rewrite andb_true_l.
    rewrite Eq_sym in H2.
    rewrite negb_true_iff.
    apply not_true_is_false.
    assumption.
  Qed.

  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s.
  Proof.
    intros [s Hs] x y.
    unfold In, remove, proj1_sig.
    eapply delete_Desc with (ub := None) (lb := None); try assumption; try reflexivity.
    intros.
    unfold elt in *.
    rewrite H1 in H2.
    rewrite andb_true_iff in H2. intuition.
  Qed.

  Lemma union_1 :
    forall (s s' : t) (x : elt), In x (union s s') -> In x s \/ In x s'.
   Proof.
     intros [s1 Hs1] [s2 Hs2] x.
     unfold In, union, proj1_sig.
    eapply union_Desc with (ub := None) (lb := None); try assumption.
    intros.
    rewrite H1 in H2.
    rewrite orb_true_iff in H2.
    assumption.
  Qed.


  Lemma union_2 :
    forall (s s' : t) (x : elt), In x s -> In x (union s s').
  Proof.
    intros [s1 Hs1] [s2 Hs2] x.
    unfold In, union, proj1_sig.
    eapply union_Desc with (ub := None) (lb := None); try assumption.
    intros.
    rewrite H1 in *.
    rewrite orb_true_iff.
    intuition.
  Qed.

  Lemma union_3 :
    forall (s s' : t) (x : elt), In x s' -> In x (union s s').
  Proof.
    intros [s1 Hs1] [s2 Hs2] x.
    unfold In, union, proj1_sig.
    eapply union_Desc with (ub := None) (lb := None); try assumption.
    intros.
    rewrite H1 in *.
    rewrite orb_true_iff.
    intuition.
  Qed.

  Lemma inter_1 : forall (s s' : t) (x : elt),
      In x (inter s s') -> In x s.
  Proof.
    intros [s1 Hs1] [s2 Hs2] x.
    unfold In, inter, proj1_sig.
    eapply intersection_Desc with (ub := None) (lb := None);
      try assumption.
    intros.
    rewrite H1 in *.
    rewrite andb_true_iff in H2.
    intuition.
  Qed.

  Lemma inter_2 : forall (s s' : t) (x : elt),
      In x (inter s s') -> In x s'.
  Proof.
    intros [s1 Hs1] [s2 Hs2] x.
    unfold In, inter, proj1_sig.
    eapply intersection_Desc with (ub := None) (lb := None);
      try assumption.
    intros.
    rewrite H1 in *.
    rewrite andb_true_iff in H2.
    intuition.
  Qed.

  Lemma inter_3 : forall (s s' : t) (x : elt),
      In x s -> In x s' -> In x (inter s s').
  Proof.
    intros [s1 Hs1] [s2 Hs2] x.
    unfold In, inter, proj1_sig.
    eapply intersection_Desc with (ub := None) (lb := None);
      try assumption.
    intros.
    rewrite H1, H2, H3.
    intuition.
  Qed.

  Lemma diff_1 :
    forall (s s' : t) (x : elt), In x (diff s s') -> In x s.
  Proof.
    intros [s1 Hs1] [s2 Hs2] x.
    unfold In, diff, proj1_sig.
    eapply difference_Desc with (ub := None) (lb := None);
      try assumption.
    intros.
    rewrite H2 in H3.
    rewrite andb_true_iff in H3.
    intuition.
  Qed.

  Lemma diff_2 :
    forall (s s' : t) (x : elt), In x (diff s s') -> ~ In x s'.
  Proof.
    intros [s1 Hs1] [s2 Hs2] x.
    unfold In, diff, proj1_sig.
    eapply difference_Desc with (ub := None) (lb := None);
      try assumption.
    intros. intro.
    rewrite H2 in H3.
    rewrite andb_true_iff in H3.
    rewrite negb_true_iff in H3.
    intuition congruence.
  Qed.

  Lemma diff_3 :
    forall (s s' : t) (x : elt), In x s -> ~ In x s' -> In x (diff s s').
  Proof.
    intros [s1 Hs1] [s2 Hs2] x.
    unfold In, diff, proj1_sig.
    eapply difference_Desc with (ub := None) (lb := None);
      try assumption.
    intros.
    rewrite H2.
    rewrite andb_true_iff.
    rewrite negb_true_iff.
    intuition try congruence.
    destruct (sem s2 x); congruence.
  Qed.

  Lemma fold_1 :
    forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
      fold A f s i =
      fold_left (fun (a : A) (e : elt) => f e a) (elements s) i.
  Proof.
    intros [s?] A n k.
    unfold fold, elements, proj1_sig.
    rewrite foldl_spec.
    reflexivity.
  Qed.

  Lemma cardinal_1 : forall s : t, cardinal s = length (elements s).
  Proof.
    intros [s?].
    unfold cardinal, elements, proj1_sig.
    erewrite size_spec by eassumption.
    rewrite Nat2Z.id.
    reflexivity.
  Qed.

  Lemma filter_1 :
    forall (s : t) (x : elt) (f : elt -> bool),
      compat_bool E.eq f -> In x (filter f s) -> In x s.
  Proof.
    intros [s?] x f HProper.
    apply compat_bool_Eeq_op_zeze in HProper.
    unfold In, filter, proj1_sig.
    eapply filter_Desc; try eassumption.
    intros s' HB _ Hsem.
    rewrite Hsem.
    rewrite andb_true_iff.
    intuition.
  Qed.

  Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
      compat_bool E.eq f -> In x (filter f s) -> f x = true.
  Proof.
    intros [s?] x f HProper.
    apply compat_bool_Eeq_op_zeze in HProper.
    unfold In, filter, proj1_sig.
    eapply filter_Desc; try eassumption.
    intros s' HB _ Hsem.
    rewrite Hsem.
    rewrite andb_true_iff.
    intuition.
  Qed.

  Lemma filter_3 :
    forall (s : t) (x : elt) (f : elt -> bool),
      compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).
  Proof.
    intros [s?] x f HProper.
    apply compat_bool_Eeq_op_zeze in HProper.
    unfold In, filter, proj1_sig.
    eapply filter_Desc; try eassumption.
    intros s' HB _ Hsem.
    rewrite Hsem.
    rewrite andb_true_iff.
    intuition.
  Qed.

  Lemma partition_1 :
    forall (s : t) (f : elt -> bool),
      compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s).
  Proof.
    intros [s?] f HProper.
    apply compat_bool_Eeq_op_zeze in HProper.
    unfold Equal, In, filter, partition, fst, proj1_sig.
    eapply filter_Desc; try eassumption.
    intros s' HB _ Hsem.
    eapply partition_spec; try eassumption.
    intros s1 s2 [HD1 HD2].
    eapply HD1; intros s1' HBs1' _ Hsems1'.
    intro.
    rewrite Hsem, Hsems1'.
    reflexivity.
  Qed.

  Lemma compat_bool_negb:
    forall A R (f : A -> bool), compat_bool R f -> compat_bool R (fun x => negb (f x)).
  Proof. intros. intros x y HR. f_equal. apply H. assumption. Qed.

  Lemma partition_2 :
    forall (s : t) (f : elt -> bool),
      compat_bool E.eq f ->
      Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s).
  Proof.
    intros [s?] f HProper.
    apply compat_bool_Eeq_op_zeze in HProper.
    pose proof (compat_bool_negb _ _ _ HProper).
    unfold Equal, In, filter, partition, snd, proj1_sig.
    eapply filter_Desc; try eassumption.
    intros s' HB _ Hsem.
    eapply partition_spec; try eassumption.
    intros s1 s2 [HD1 HD2].
    eapply HD2; intros s2' HBs2' _ Hsems2'.
    intro.
    rewrite Hsem, Hsems2'.
    reflexivity.
  Qed.

  Lemma elements_1 :
    forall (s : t) (x : elt), In x s -> InA E.eq x (elements s).
  Proof.
    intros [s?] x H.
    unfold In, elements, proj1_sig in *.
    rewrite InA_Eeq_elem in *.
    erewrite toList_sem in H by eassumption.
    assumption.
  Qed.

  Lemma elements_2 :
    forall (s : t) (x : elt), InA E.eq x (elements s) -> In x s.
  Proof.
    intros [s?] x H.
    unfold In, elements, proj1_sig in *.
    rewrite InA_Eeq_elem in *.
    erewrite toList_sem in * by eassumption.
    assumption.
  Qed.

  Lemma elements_3 (s : t) : Sorted E.lt (elements s).
  Proof.
    destruct s as [s WFs]; unfold elements; simpl.
    eapply StronglySorted_Sorted, StronglySorted_R_ext.
    - apply E_lt_zl.
    - eapply to_List_sorted; eassumption.
  Qed.

  Lemma elements_3w (s : t) : NoDupA E.eq (elements s).
  Proof. apply OrdFacts.Sort_NoDup, elements_3. Qed.

  (* Ordering theorems *)

  Definition compare (s s' : t) : Compare lt eq s s'.
  Proof.
    destruct (compare s s') eqn:CMP.
    - apply EQ. abstract now apply equal_2; destruct s, s'; generalize dependent CMP;
                             rewrite Ord_compare_Eq; unfold "==", Eq_Set_WF; simpl.
    - apply LT; abstract order t.
    - apply GT; abstract order t.
  Defined.

  Theorem lt_trans (s1 s2 s3 : t) :
    lt s1 s2 -> lt s2 s3 -> lt s1 s3.
  Proof. unfold lt; order t. Qed.

  Theorem lt_not_eq (s1 s2 : t) :
    lt s1 s2 -> ~ eq s1 s2.
  Proof.
    unfold lt; intros LT EQ; apply equal_1 in EQ; unfold equal in EQ.
    assert (s1 == s2 = true) as EQ' by apply EQ.
    order t.
  Qed.

  Lemma min_elt_1 (s : t) (x : elt) : min_elt s = Some x -> In x s.
  Proof.
    destruct s as [s WFs]; unfold min_elt, In; simpl; intros def_x.
    now specialize (lookupMin_Desc s _ _ WFs); rewrite def_x.
  Qed.

  Lemma min_elt_2 (s : t) (x y : elt) : min_elt s = Some x -> In y s -> ~ E.lt y x.
  Proof.
    destruct s as [s WFs]; unfold min_elt, In; simpl; intros def_x.
    specialize (lookupMin_Desc s _ _ WFs); rewrite def_x; intros [sem_x x_min] sem_y.
    specialize (x_min y sem_y).
    rewrite E_lt_zl; order elt.
  Qed.

  Lemma min_elt_3 (s : t) : min_elt s = None -> Empty s.
  Proof.
    destruct s as [s WFs]; unfold min_elt, Empty, In; simpl; intros def_x.
    specialize (lookupMin_Desc s _ _ WFs); rewrite def_x; intros def_sem x.
    now rewrite def_sem.
  Qed.

  Lemma max_elt_1 (s : t) (x : elt) : max_elt s = Some x -> In x s.
  Proof.
    destruct s as [s WFs]; unfold max_elt, In; simpl; intros def_x.
    now specialize (lookupMax_Desc s _ _ WFs); rewrite def_x.
  Qed.

  Lemma max_elt_2 (s : t) (x y : elt) : max_elt s = Some x -> In y s -> ~ E.lt x y.
  Proof.
    destruct s as [s WFs]; unfold max_elt, In; simpl; intros def_x.
    specialize (lookupMax_Desc s _ _ WFs); rewrite def_x; intros [sem_x x_max] sem_y.
    specialize (x_max y sem_y).
    rewrite E_lt_zl; order elt.
  Qed.

  Lemma max_elt_3 (s : t) : max_elt s = None -> Empty s.
  Proof.
    destruct s as [s WFs]; unfold max_elt, Empty, In; simpl; intros def_x.
    specialize (lookupMax_Desc s _ _ WFs); rewrite def_x; intros def_sem x.
    now rewrite def_sem.
  Qed.

  (**
  These portions of the [FMapInterface] have no counterpart in the [IntSet] interface.
  We implement them generically.
  *)

  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Definition for_all : (elt -> bool) -> t -> bool :=
    fun P s => forallb P (elements s).
  Definition exists_ : (elt -> bool) -> t -> bool :=
    fun P s => existsb P (elements s).

  Lemma for_all_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    For_all (fun x : elt => f x = true) s -> for_all f s = true.
  Proof.
    intros.
    unfold For_all, for_all in *.
    rewrite forallb_forall.
    intros. apply H0.
    apply elements_2.
    apply OrdFacts.ListIn_In.
    assumption.
  Qed.

  Lemma for_all_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    for_all f s = true -> For_all (fun x : elt => f x = true) s.
  Proof.
    intros.
    unfold For_all, for_all in *.
    rewrite forallb_forall in H0.
    intros.
    apply elements_1 in H1.
    rewrite InA_alt in H1.
    destruct H1 as [?[??]].
    assert (f x0 = true) by (apply H0; assumption).
    unfold compat_bool in H.
    setoid_rewrite H1.
    assumption.
  Qed.

  Lemma exists_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    Exists (fun x : elt => f x = true) s -> exists_ f s = true.
  Proof.
    intros.
    unfold Exists, exists_ in *.
    rewrite existsb_exists.
    destruct H0 as [x[??]].
    apply elements_1 in H0.
    rewrite InA_alt in H0.
    destruct H0 as [?[??]].
    exists x0.
    split; auto.
    unfold compat_bool in H.
    setoid_rewrite <- H0.
    assumption.
  Qed.

  Lemma exists_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    exists_ f s = true -> Exists (fun x : elt => f x = true) s.
  Proof.
    intros.
    unfold Exists, exists_ in *.
    rewrite existsb_exists in H0.
    destruct H0 as [x[??]].
    exists x.
    split; auto.
    apply elements_2.
    apply OrdFacts.ListIn_In.
    assumption.
  Qed.

  Definition choose : t -> option elt := min_elt.

  Lemma choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s.
  Proof. apply min_elt_1. Qed.

  Lemma choose_2 : forall s : t, choose s = None -> Empty s.
  Proof. apply min_elt_3. Qed.

  Lemma choose_3 (s1 s2 : t) (x1 x2 : elt) :
    choose s1 = Some x1 ->
    choose s2 = Some x2 ->
    Equal s1 s2         ->
    E.eq  x1 x2.
  Proof.
    destruct s1 as [s1 WF1], s2 as [s2 WF2]; unfold choose, min_elt, Equal, In; simpl.
    intros def_x1 def_x2 EQ.
    specialize (lookupMin_Desc s1 _ _ WF1); specialize (lookupMin_Desc s2 _ _ WF2);
      rewrite def_x1, def_x2.
    intros [sem_x2 min_x2] [sem_x1 min_x1].
    generalize (min_x1 x2); generalize (min_x2 x1).
    rewrite <-EQ, sem_x1, EQ, sem_x2.
    intros LE21 LE12; specialize (LE21 Logic.eq_refl); specialize (LE12 Logic.eq_refl).
    apply E_eq_zeze; order elt.
  Qed.
End SetFSet.

(** * Rewrite rules *)

(**
@
{-# RULES "Set.toAscList" [~1] forall s . toAscList s = build (\c n -> foldrFB c n s) #-}
{-# RULES "Set.toAscListBack" [1] foldrFB (:) [] = toAscList #-}
{-# RULES "Set.toDescList" [~1] forall s . toDescList s = build (\c n -> foldlFB (\xs x -> c x xs) n s) #-}
{-# RULES "Set.toDescListBack" [1] foldlFB (\xs x -> x : xs) [] = toDescList #-}
@
*)

Lemma rule_toAscList: forall e (s : Set_ e), toAscList s = build (fun _ c n => foldrFB c n s).
Proof. intros.  reflexivity. Qed.

Lemma rule_toAscListBack: forall e, @foldrFB e _ cons nil = toAscList.
Proof. intros.  reflexivity. Qed.

Lemma rule_toDescList: forall e (s : Set_ e), toDescList s = build (fun _ c n => foldlFB (fun xs x => c x xs) n s).
Proof. intros.  reflexivity. Qed.

Lemma rule_toDescListBack: forall e, foldlFB (fun xs x => x :: xs) nil = @toDescList e.
Proof. intros.  reflexivity. Qed.
