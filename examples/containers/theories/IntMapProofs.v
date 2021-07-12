Require Import Omega.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Bool.Bool.


Require Import BitUtils.
Require Import DyadicIntervals.
Require Import CustomTactics.

(** * The IntMap formalization *)

Require Import GHC.DeferredFix.
Require Import IntSetProofs.
Require Import Data.IntSet.Internal.
Require Import Data.IntMap.Internal.
Require Import MapProofs.Bounds.

Import GHC.Base.

Set Bullet Behavior "Strict Subproofs".

Axiom deferredFix2_eq : forall a b r `{Default r} (f : (a -> b -> r) -> (a -> b -> r)),
  deferredFix2 f = f (deferredFix2 f).

From Coq Require Import ssreflect.

Lemma oro_None_r {a} (x:option a) : oro x None = x.
Proof. destruct x; simpl; reflexivity. Qed.
Lemma oro_None_l {a} (x:option a) : oro None x = x.
Proof. reflexivity. Qed.
Lemma oro_Some_l a (v:a) x : oro (Some v) x = Some v.
Proof. destruct x; simpl; auto. Qed.
Lemma oro_Some a (v:a) x y : oro x y = Some v -> x = Some v \/ y = Some v.
Proof.
  destruct x; destruct y; simpl; auto.
Qed.


(** ** Well-formed IntMap.
This section introduces the predicate to describe the well-formedness of
an IntMap. It has parameters that describe the range that this map covers,
and a function that carries it denotation. This way, invariant preservation
and functional correctness of an operation can be expressed in one go.
*)

Definition singletonRange k : range := (k, 0%N).


Local Open Scope N_scope.

Inductive Desc : forall {a}, IntMap a -> range -> (N -> option a) -> Prop :=
  | DescTip : forall a k (v : a) r f,
    (forall i, f i = if i =? k then Some v else None) ->
    r = singletonRange k ->
    Desc (Tip k v) r f
  | DescBin : forall a m1 r1 f1 m2 r2 f2 p msk r (f : N  -> option a),
    Desc m1 r1 f1 ->
    Desc m2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = rPrefix r ->
    msk = rMask r ->
    (forall i, f i = oro (f1 i) (f2 i)) ->
    Desc (Bin p msk m1 m2) r f.

(** A variant that also allows [Nil], or sets that do not
    cover the full given range, but are certainly contained in them.
    This is used to describe operations that may delete elements.
 *)

Inductive Desc0 : forall {a}, IntMap a -> range -> (N -> option a) -> Prop :=
  | Desc0Nil : forall {a} r (f : N -> option a), (forall i, f i = None) -> Desc0 Nil r f
  | Desc0NotNil :
      forall {a},
      forall m r f r' (f' : N -> option a),
      forall (HD : Desc m r f),
      forall (Hsubrange: isSubrange r r' = true)
      (Hf : forall i, f' i = f i),
      Desc0 m r' f'.

(** A variant that also allows [Nil] and does not reqiure a range. Used
    for the top-level specification.
 *)

Inductive Sem : forall {a}, IntMap a -> (N -> option a) -> Prop :=
  | SemNil : forall {a} (f : N -> option a), (forall i, f i = None) -> Sem Nil f
  | DescSem : forall {a} s r (f : N -> option a) (HD : Desc s r f), Sem s f.

(** The highest level: Just well-formedness.
 *)

Fixpoint sem {a} (s: IntMap a) (i: Key) :=
  match s with
  | Nil => None
  | Tip k x => if (i == k) then Some x else None
  | Bin p msk m1 m2 => oro (sem m1 i) (sem m2 i)
  end.

Definition WF {a} (s : IntMap a) : Prop := exists f, Sem s f.

Ltac inversion_Desc HD1 :=
  inversion HD1;
  repeat match goal with [ H : existT ?f ?a ?s1 = existT ?f ?a ?s2 |- _ ] =>
                  apply Eqdep.EqdepTheory.inj_pair2 in H
  end;
  subst.


(** ** Lemmas related to well-formedness *)


(** All of these respect extensionality of [f] *)

Lemma Desc_change_f:
  forall {a} (s:IntMap a) r f f',
  Desc s r f -> (forall i, f' i = f i) -> Desc s r f'.
Proof.
  intros.
  induction H.
  * eapply DescTip; try eassumption.
    intro i. rewrite H0 H. reflexivity.
  * eapply DescBin; try eassumption.
    intro i. rewrite H0 H7. reflexivity.
Qed.

Lemma Sem_change_f:
  forall {a} (s:IntMap a) f f',
  Sem s f -> (forall i, f' i = f i) -> Sem s f'.
Proof.
  intros.
  destruct H.
  * apply SemNil.
    intro i. rewrite H0 H. reflexivity.
  * eapply DescSem. eapply Desc_change_f. eassumption.
    intro i. rewrite H0. reflexivity.
Qed.


Lemma Desc_Desc0:
  forall {a} (s:IntMap a) r f, Desc s r f -> Desc0 s r f.
Proof. intros.
  eapply Desc0NotNil.
  * eassumption.
  * apply isSubrange_refl.
  * intro. reflexivity.
Qed.

Lemma Desc0_Sem:
  forall {a} (s:IntMap a) r f, Desc0 s r f -> Sem s f.
Proof.
  intros.
  destruct H.
  * apply SemNil; eassumption.
  * eapply DescSem. eapply Desc_change_f. eassumption. assumption.
Qed.

Lemma Desc0_WF:
  forall {a} (s:IntMap a) r f, Desc0 s r f -> WF s.
Proof.
  intros. eexists. eapply Desc0_Sem. eassumption.
Qed.

Lemma Desc_outside:
 forall {a} {s : IntMap a} {r f i}, Desc s r f -> inRange i r = false -> f i = None.
Proof.
 intros ????? HD Houtside.
 induction HD;subst.
 * rewrite H.
   unfold inRange, singletonRange in *.
   simpl in Houtside.
   destruct (i =? k) eqn:IsI.
   inversion Houtside.
   auto.
 * rewrite H4; clear H4.
   rewrite IHHD1; last inRange_false.
   rewrite IHHD2; last inRange_false.
   reflexivity.
Qed.

Lemma Desc_inside:
 forall {a} {s : IntMap a} {r f i} {v}, Desc s r f -> f i = Some v -> inRange i r = true.
Proof.
 intros ?????? HD Hf.
 destruct (inRange i r) eqn:?; intuition.
 rewrite (Desc_outside HD) // in Hf.
Qed.

Lemma Desc0_outside:
  forall {a} {s : IntMap a} {r f i}, Desc0 s r f -> inRange i r = false -> f i = None.
Proof.
  intros.
  destruct H; auto.
  rewrite Hf.
  rewrite (Desc_outside HD) //; inRange_false.
Qed.

Lemma Desc0_subRange:
  forall {a} {s : IntMap a} {r r' f}, Desc0 s r f -> isSubrange r r' = true -> Desc0 s r' f.
Proof.
  intros.
  induction H.
  * apply Desc0Nil; assumption.
  * eapply Desc0NotNil; try eassumption.
    isSubrange_true.
Qed.

(** The [Desc] predicate only holds for non-empty sets. *)
Lemma Desc_some_f:
  forall {a} {s:IntMap a} {r f}, Desc s r f -> exists i v, f i = Some v.
Proof.
  intros ???? HD.
  induction HD; subst.
  +
    exists k. exists v.
    rewrite H.
    rewrite N.eqb_refl.
    auto.
  + destruct IHHD1  as [j [v1 ?]].
    exists j. exists v1.
    rewrite H4.
    rewrite H2.
    reflexivity.
Qed.

(** The [Desc] predicate is right_unique *)
Lemma Desc_unique_f:
  forall {a}{s:IntMap a}{r1 f1 r2 f2}, Desc s r1 f1 -> Desc s r2 f2 -> (forall i, f1 i = f2 i).
Proof.
  intros ?????? HD.
  revert r2 f2.
  induction HD; subst.
  + intros r2 f2 HD2 i.
    inversion_Desc HD2.
    rewrite H H5.
    reflexivity.
  + intros r3 f3 HD3 i.
    inversion_Desc HD3.
    rewrite H17 H4.
    erewrite IHHD1 by eassumption.
    erewrite IHHD2 by eassumption.
    reflexivity.
Qed.


Lemma DescBin' : forall {a} (s1:IntMap a) r1 f1 s2 r2 f2 p msk r f,
    Desc s1 r1 f1 ->
    Desc s2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = rPrefix r ->
    msk = rMask r ->
    (forall i, inRange i (halfRange r false) = true  -> f i = f1 i) ->
    (forall i, inRange i (halfRange r true)  = true  -> f i = f2 i) ->
    (forall i, inRange i r                   = false -> f i = None) ->
    Desc (Bin p msk s1 s2) r f.
Proof.
  intros.
  eapply DescBin; try eassumption.
  intro i.
  destruct (inRange i r) eqn:Hir.
  * destruct (inRange i (halfRange r false)) eqn: Hir1.
    + assert (Hir2 : inRange i (halfRange r true) = false).
      { eapply rangeDisjoint_inRange_false.
        eapply halves_disj; auto.
        assumption.
      }
      rewrite H6 //.
      rewrite (Desc_outside H0); last inRange_false.
      rewrite oro_None_r. reflexivity.
    + assert (Hir2 : inRange i (halfRange r true) = true).
      { rewrite halfRange_inRange_testbit // in Hir1.
        rewrite halfRange_inRange_testbit //.
        destruct (N.testbit _ _); simpl in *; congruence.
      }
      rewrite H7 //.
      rewrite (Desc_outside H); last inRange_false.
      rewrite oro_None_l //.
  * rewrite H8 //.
    rewrite (Desc_outside H) ; last inRange_false.
    rewrite (Desc_outside H0) ; last inRange_false.
    reflexivity.
Qed.


Ltac point_to_inRange :=
  lazymatch goal with
    | [ HD : Desc ?s ?r ?f, Hf : ?f ?i = Some ?v |- _ ]
      => apply (Desc_inside HD) in Hf
  end.


(**
 Like [solve_f_eq], but tries to solve the resulting bogus cases
 using reasoning about [inRange]. *)

Ltac solve_f_eq_disjoint :=
  solve_f_eq;
  repeat point_to_inRange;
  repeat saturate_inRange;
  try inRange_disjoint. (* Only try this, so that we see where we are stuck. *)


(** *** Uniqueness of representation *)

Lemma larger_f_imp:
  forall a (s1 : IntMap a) r1 f1 s2 r2 f2,
  (rBits r2 < rBits r1)%N ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall (i : N) v, f1 i = Some v -> f2 i = Some v) ->
  False.
Proof.
  intros ???? ??? Hsmaller HD1 HD2 Hf.
  destruct HD1.
  * subst. simpl in Hsmaller. Nomega.
  * subst.
    assert (isSubrange r2 (halfRange r false) = true).
      { destruct (Desc_some_f HD1_1) as [i [v Hi]].
        pose proof (Desc_inside HD1_1 Hi).
        specialize (H4 i).
        (* TODO: Why do we need Coq rewrite + by ? *)
        rewrite -> (Desc_outside HD1_2) in H4 by inRange_false.
        rewrite oro_None_r in H4.
        rewrite <- H4 in Hi; clear H4.
        apply Hf in Hi; clear Hf.
        apply (Desc_inside HD2) in Hi.
        apply inRange_both_smaller_subRange with (i := i).
        * inRange_true.
        * inRange_true.
        * rewrite rBits_halfRange. Nomega.
      }
    assert (isSubrange r2 (halfRange r true) = true).
      { destruct (Desc_some_f HD1_2) as [i [v Hi]].
        pose proof (Desc_inside HD1_2 Hi).
        specialize (H4 i).
        rewrite -> (Desc_outside HD1_1) in H4 by inRange_false.
        rewrite oro_None_l in H4.
        rewrite <- H4 in Hi; clear H4.
        apply Hf in Hi; clear Hf.
        apply (Desc_inside HD2) in Hi.
        apply inRange_both_smaller_subRange with (i := i).
        * inRange_true.
        * inRange_true.
        * rewrite rBits_halfRange. Nomega.
      }
      inRange_disjoint.
Qed.

Lemma Desc_unique:
  forall a (s1:IntMap a) r1 f1 s2 r2 f2,
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i, f1 i = f2 i) ->
  s1 = s2.
Proof.
  intros ??????? HD1.
  revert s2 r2 f2.
  induction HD1.
  * intros s2 r2 f2 HD2 Hf.
    destruct HD2.
    + subst.
      destruct (N.eq_decidable k k0).
      ++ subst.
         specialize (H k0). rewrite Hf H1 in H.
         rewrite N.eqb_refl in H. inversion H.
         reflexivity.
      ++ specialize (H k0). rewrite Hf H1 in H.
         rewrite N.eqb_refl in H.
         destruct (N.eqb_neq k k0) as [h0 h1].
         rewrite N.eqb_sym in H.
         rewrite (h1 H0)  in H.
         inversion H.
    +
      exfalso. subst.
      eapply larger_f_imp with (r1 := r0) (r2 := singletonRange k).
      - simpl. auto.
      - eapply DescBin with (m1 := m1) (m2 := m2); try eassumption; reflexivity.
      - eapply DescTip; try eassumption; reflexivity.
      - intros i Hi. rewrite Hf. auto.
  * intros s3 r3 f3 HD3 Hf.
    destruct HD3.
    + exfalso. subst.
      eapply larger_f_imp with (r1 := r) (r2 := singletonRange k).
      - simpl. auto.
      - eapply DescBin with (m1 := m1) (m2 := m2); try eassumption; reflexivity.
      - eapply DescTip; try eassumption; reflexivity.
      - intros i Hi. rewrite <- Hf. auto.

    + subst.
      assert (r4 = r). {
        destruct (Desc_some_f HD3_1) as [i1 [v1 Hi1]].
        destruct (Desc_some_f HD3_2) as [i2 [v2 Hi2]].
        destruct (Desc_some_f HD1_1) as [i3 [v3 Hi3]].
        destruct (Desc_some_f HD1_2) as [i4 [v4 Hi4]].
        apply criss_cross with i1 i2 i3 i4; try assumption.
        * apply (Desc_inside HD3_1) in Hi1; inRange_true.
        * apply (Desc_inside HD3_2) in Hi2; inRange_true.
        * apply (Desc_inside HD1_1) in Hi3; inRange_true.
        * apply (Desc_inside HD1_2) in Hi4; inRange_true.
        * specialize (H10 i1); rewrite Hi1 in H10.
          rewrite oro_Some_l in H10.
          rewrite <- Hf in H10.
          specialize (H4 i1); rewrite H10 in H4; clear H10; symmetry in H4.
          apply oro_Some in H4.
          destruct H4.
          + apply (Desc_inside HD1_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
        * specialize (H10 i2); rewrite Hi2 in H10;
          destruct (f0 i2) eqn:If0; simpl in H10;
          rewrite <- Hf in H10;
          specialize (H4 i2); rewrite H10 in H4; clear H10; symmetry in H4;
          apply oro_Some in H4; destruct H4.
          + apply (Desc_inside HD1_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.

        * specialize (H4 i3); rewrite Hi3 in H4.
          rewrite oro_Some_l in H4.
          rewrite -> Hf in H4.
          specialize (H10 i3); rewrite H4 in H10; clear H4; symmetry in H10.
          apply oro_Some in H10; destruct H10.
          + apply (Desc_inside HD3_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD3_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
        * specialize (H4 i4); rewrite Hi4 in H4.
          destruct (f1 i4) eqn:Is4; simpl in H4;
          rewrite -> Hf in H4;
          specialize (H10 i4); rewrite H4 in H10; clear H4; symmetry in H10;
          apply oro_Some in H10; destruct H10.
          + apply (Desc_inside HD3_1) in H2;
            eapply inRange_isSubrange_true; [|eassumption];
            isSubrange_true.
          + apply (Desc_inside HD3_2) in H2;
            eapply inRange_isSubrange_true; [|eassumption];
            isSubrange_true.
          + apply (Desc_inside HD3_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD3_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.

      }
      subst.
      assert (IH_prem_1 : (forall i : N, f1 i = f0 i)). {
        intro i.
        specialize (H4 i). specialize (H10 i). specialize (Hf i).
        destruct (inRange i (halfRange r false)) eqn:?.
        -- rewrite -> (Desc_outside HD1_2) in H4 by inRange_false.
           rewrite oro_None_r in H4.
           rewrite <- H4; clear H4.

           rewrite -> (Desc_outside HD3_2) in H10 by inRange_false.
           rewrite oro_None_r in H10.
           rewrite <- H10; clear H10.

           assumption.
        -- rewrite (Desc_outside HD1_1) ; last inRange_false.
           rewrite (Desc_outside HD3_1) ; last inRange_false.
           reflexivity.
      }
      assert (IH_prem_2 : (forall i : N, f2 i = f3 i)). {
        intro i.
        specialize (H4 i). specialize (H10 i). specialize (Hf i).
        destruct (inRange i (halfRange r true)) eqn:?.
        -- rewrite -> (Desc_outside HD1_1) in H4 by inRange_false.
           rewrite oro_None_l in H4.
           rewrite <- H4; clear H4.

           rewrite -> (Desc_outside HD3_1) in H10 by inRange_false.
           rewrite oro_None_l in H10.
           rewrite <- H10; clear H10.

           assumption.
        -- rewrite (Desc_outside HD1_2) ; last inRange_false.
           rewrite (Desc_outside HD3_2) ; last inRange_false.
           reflexivity.
      }
      specialize (IHHD1_1 _ _ _ HD3_1 IH_prem_1).
      destruct IHHD1_1; subst.
      specialize (IHHD1_2 _ _ _ HD3_2 IH_prem_2).
      destruct IHHD1_2; subst.
      reflexivity.
Qed.


Lemma Sem_unique:
  forall a (s1:IntMap a) f1 s2 f2,
  Sem s1 f1 -> Sem s2 f2 ->
  (forall i, f1 i = f2 i) ->
  s1 = s2.
Proof.
  intros.
  destruct H, H0.
  * reflexivity.
  * exfalso.
    destruct (Desc_some_f HD) as [i [v Hi]].
    rewrite <- H1 in Hi.
    rewrite H in Hi.
    congruence.
  * exfalso.
    destruct (Desc_some_f HD) as [i [v Hi]].
    rewrite -> H1 in Hi.
    rewrite H in Hi.
    congruence.
  * eapply Desc_unique; eassumption.
Qed.

Theorem Sem_extensional {a} (s : IntMap a) (f1 f2 : N -> option a) :
  Sem s f1 ->
  Sem s f2 ->
  forall i, f1 i = f2 i.
Proof.
  intros S1 S2 k;
    inversion S1 as [a1 f1' E1 | a1 s1 r1 f1' D1];
    apply Eqdep.EqdepTheory.inj_pair2 in H0;
    apply Eqdep.EqdepTheory.inj_pair2 in H1;
    subst f1' s;
    inversion S2 as [a2 f2' E2 | a2 s2 r2 f2' D2];
    apply Eqdep.EqdepTheory.inj_pair2 in H1.
    subst f2';
    try subst s1; try subst s2.
  - now rewrite E1 E2.
  - subst.
    inversion D2.
  - subst.
    inversion D1.
  - apply Eqdep.EqdepTheory.inj_pair2 in H2.
    subst.
    eauto using Desc_unique_f.
Qed.

(** *** Verification of [nomatch] *)

Lemma nomatch_spec:
  forall i r,
  (0 < rBits r)%N ->
  IntMap.Internal.nomatch i (rPrefix r) (rMask r) =
  negb (inRange i r).
Proof.
  intros.
  destruct r as [p b]. simpl in *.
  unfold nomatch, zero, inRange.
  unfoldMethods.
  unfold mask, IntSet.Internal.maskW.
  f_equal.
  rewrite eq_iff_eq_true.
  rewrite !N.eqb_eq.
  rewrite <- N.pow_succ_r  by Nomega.
  replace (N.succ (b - 1)) with b by Nomega.
  rewrite N.sub_1_r.
  rewrite <- N.ones_equiv.
  rewrite -> N.ldiff_ones_r by nonneg.
  rewrite -> N_shiftl_inj by nonneg.
  reflexivity.
Qed.

Lemma match_nomatch: forall x p ms,
  match_ x p ms = negb (nomatch x p ms).
Proof.
  intros. unfold match_, nomatch. unfoldMethods.
  rewrite negb_involutive.
  reflexivity.
Qed.

(**
The IntMap code has a repeating pattern consisting of calls to [nomatch] and [zero].
The following two lemmas capture that pattern concisely.
*)

Lemma nomatch_zero:
  forall {a} i r (P : a -> Prop) left right otherwise,
  (0 < rBits r)%N ->
  (inRange i r = false -> P otherwise) ->
  (inRange i (halfRange r false) = true -> inRange i (halfRange r true) = false -> P left) ->
  (inRange i (halfRange r false) = false -> inRange i (halfRange r true) = true -> P right) ->
  P (if nomatch i (rPrefix r) (rMask r) then otherwise else
     if zero i (rMask r) then left else right).
Proof.
  intros.
  rewrite nomatch_spec //.
  rewrite if_negb.
  destruct (inRange i r) eqn:?.
  * rewrite zero_spec //.
    rewrite if_negb.
    destruct (N.testbit i (rBits r - 1)) eqn:Hbit.
    + apply H2.
      all: rewrite halfRange_inRange_testbit // Hbit //.
    + apply H1.
      all: rewrite halfRange_inRange_testbit // Hbit //.
  * apply H0; reflexivity.
Qed.

Lemma nomatch_zero_smaller:
  forall {a} r1 r (P : a -> Prop) left right otherwise,
  (rBits r1 < rBits r)%N ->
  (rangeDisjoint r1 r = true -> P otherwise) ->
  (isSubrange r1 (halfRange r false) = true  -> isSubrange r1 (halfRange r true) = false -> P left) ->
  (isSubrange r1 (halfRange r false) = false -> isSubrange r1 (halfRange r true) = true -> P right) ->
  P (if nomatch (rPrefix r1) (rPrefix r) (rMask r) then otherwise else
     if zero (rPrefix r1) (rMask r) then left else right).
Proof.
  intros ????????.
  assert (rBits r1 <= rBits r)%N by Nomega.
  assert (forall h, rBits r1 <= rBits (halfRange r h))%N
    by (intros; rewrite rBits_halfRange; Nomega).
  rewrite <- smaller_not_subrange_disjoint_iff; auto.
  repeat rewrite <- smaller_inRange_iff_subRange by auto.
  apply nomatch_zero.
  Nomega.
Qed.


(** *** Verification of [equal] *)

Lemma equal_spec a `{Base.Eq_ a} `{Base.EqExact a} :
  forall (s1 s2 : IntMap a), equal s1 s2 = true <-> s1 = s2.
Proof.
  induction s1; intro s2; destruct s2;
    try solve [simpl; intuition congruence].
  * simpl. unfoldMethods.
    rewrite !andb_true_iff.
    rewrite !N.eqb_eq.
    rewrite IHs1_1.
    rewrite IHs1_2.
    intuition congruence.
  * simpl.
    rewrite !andb_true_iff.
    rewrite <- (reflect_iff _ _ (Base.Eq_eq a0 a1)).
    rewrite !N.eqb_eq.
    intuition congruence.
Qed.

(** *** Verification of [nequal] *)

Lemma nequal_spec {a} `{Base.Eq_ a}`{ Base.EqLaws a} :
  forall (s1 s2:IntMap a), nequal s1 s2 = negb (equal s1 s2).
Proof.
  induction s1; intro s2; destruct s2;
    try solve [simpl; intuition congruence].
  * simpl. unfoldMethods.
    rewrite !negb_andb.
    rewrite IHs1_1.
    rewrite IHs1_2.
    reflexivity.
  * simpl.
    rewrite !negb_andb.
    rewrite (Base.Eq_inv k k0).
    rewrite (Base.Eq_inv a0 a1).
    rewrite !negb_involutive.
    auto.
Qed.

(** *** Verification of [singleton] *)

Lemma singleton_Desc:
  forall a k (v : a),
   Desc (singleton k v) (singletonRange k) (fun x => if x =? k then Some v else None).
Proof.
  intros.
  apply DescTip; try nonneg; try isBitMask.
Qed.

Lemma singleton_Sem:
  forall a k (v:a), Sem (singleton k v) (fun x => if x =? k then Some v else None).
Proof.
  intros.
  eapply DescSem.
  apply singleton_Desc; assumption.
Qed.

Lemma singleton_WF:
  forall a k (v:a), WF (singleton k v).
Proof. intros. eexists. apply singleton_Sem; auto. Qed.

(** *** Verification of [lookup] *)


Lemma lookup_Desc:
 forall {a}{s : IntMap a}{r f i}, Desc s r f -> lookup i s = f i.
Proof.
 intros ????? HD.
 induction HD; subst.
 * simpl.
   unfoldMethods.
   rewrite H.
   destruct (i =? k) eqn:Ei; simpl; auto.
 * rewrite H4. clear H4.
   simpl lookup.
   rewrite IHHD1 IHHD2. clear IHHD1 IHHD2.

   apply nomatch_zero; [auto|..]; intros.
   + rewrite (Desc_outside HD1) ; last inRange_false.
     rewrite (Desc_outside HD2) ; last inRange_false.
     reflexivity.
   + rewrite (Desc_outside HD2) ; last inRange_false.
     rewrite oro_None_r. reflexivity.
   + rewrite (Desc_outside HD1) ; last inRange_false.
     rewrite oro_None_l. reflexivity.
Qed.


Lemma lookup_Desc0:
  forall {a}{s:IntMap a} {r f i}, Desc0 s r f -> lookup i s = f i.
Proof.
  intros.
  destruct H; simpl; auto.
  rewrite Hf.
  eapply lookup_Desc; eauto.
Abort.

Lemma lookup_Sem:
  forall {a}{s:IntMap a}{f i}, Sem s f -> lookup i s = f i.
Proof.
  intros.
  destruct H.
  * rewrite H. reflexivity.
  * erewrite lookup_Desc; eauto.
Qed.


(* For the sake of simplicity, we are writing a new findWithdefault that returns an option *)

Definition findWithDefaultOption {a} (def : a) (k : Key) (s : IntMap a) :=
  Some (findWithDefault def k s).

Lemma Desc_not_inRange_None : forall a (s : IntMap a) r f,
    Desc s r f ->
    forall i, inRange i r = false -> f i = None. 
Proof.
  intros. induction H.
  * rewrite H1 in H0. unfold inRange in H0. simpl in H0. specialize (H i).
    rewrite H0 in H. apply H.
  * assert (Desc (Bin p msk m1 m2) r f).
    eapply DescBin with (r1:= r1) (f1:= f1) (r2:=r2) (f2:=f2); auto.
    move: (Desc_outside H8 H0 ) => H9. apply H9.
Qed.


Lemma findWithDefault_Desc:
  forall {a}{s: IntMap a} {r f} x i, Desc s r f ->
                                     match (f i) with
                                     | Some v => findWithDefaultOption x i s = Some v
                                     | None => findWithDefaultOption x i s = Some x
                                     end.
Proof.
  intros. induction H.
  * destruct (f i) eqn: E.
    + unfold findWithDefaultOption. unfold findWithDefault. specialize (H i).
      destruct (i == k) eqn: ik; rewrite ik; rewrite E in H; destruct (i =? k) eqn: ik2; try discriminate.
      - congruence.
      - apply Neqb_ok in ik2. rewrite Base.Eq_reflI in ik. discriminate. apply ik2.
     + unfold findWithDefaultOption. unfold findWithDefault. specialize (H i).
       destruct (i == k) eqn: ik; rewrite ik; rewrite E in H; destruct (i =? k) eqn: ik2;
         try discriminate.
      - unfold "==" in ik. unfoldMethods. rewrite ik in ik2. discriminate.
      - reflexivity.  
  * destruct (f i) eqn: E. 
    + unfold findWithDefaultOption. simpl. subst. apply nomatch_zero.
      - apply H1.
      - rewrite <- E. 
        specialize (IHDesc1 x). specialize (IHDesc2 x).
        intros IRH. assert (Desc (Bin (rPrefix r) (rMask r) m1 m2) r f).
        eapply DescBin with (r1:= r1) (f1:= f1) (r2:= r2) (f2:=f2); auto.
         move: (Desc_not_inRange_None a (Bin (rPrefix r) (rMask r) m1 m2) r f) => H7.
        intuition. specialize (H5 i). intuition. rewrite H7. congruence.
      - specialize (IHDesc1 x). specialize (H6 i). destruct (f1 i) eqn: Hf. simpl in H6.
        rewrite H6 in E. inversion E. subst. unfold findWithDefaultOption in IHDesc1. intros. apply IHDesc1.
        intros. unfold findWithDefaultOption in IHDesc1. simpl in H6. specialize (IHDesc2 x).
        rewrite <- H6 in IHDesc2. rewrite E in IHDesc2. move: (Desc_not_inRange_None _ _ _ _ H0) => H7.
        specialize (H7 i). 
        move: (inRange_isSubrange_false i _ _ H3 H5) => H8. rewrite H8 in H7. intuition.
        rewrite H9 in H6. rewrite E in H6. discriminate.
      - specialize (IHDesc2 x). specialize (IHDesc1 x). intros.
        unfold findWithDefaultOption in IHDesc2. destruct (f2 i) eqn: Hf.
        ** rewrite IHDesc2. move: (Desc_not_inRange_None a m2 r2 f2 H0 i) => H8.
           move: (Desc_not_inRange_None a m1 r1 f1 H i) => H9.
           move: (inRange_isSubrange_false i _ _  H2 H4) => H10.
           rewrite H10 in H9. intuition. specialize (H6 i). unfold oro in H6. rewrite H7 in H6.
           rewrite Hf in H6. rewrite E in H6. symmetry. apply H6.
        ** rewrite IHDesc2. rewrite <- E. move: (Desc_not_inRange_None a m1 r1 f1 H i) => H7.
           move: (inRange_isSubrange_false i _ _ H2 H4) => H8. rewrite H8 in H7. intuition.
           specialize (H6 i). unfold oro in H6. rewrite H9 in H6. rewrite Hf in H6. rewrite E in H6.
           discriminate.                                    
    + unfold findWithDefaultOption.  simpl. subst. apply nomatch_zero;
       specialize (H6 i); unfold oro in H6; specialize (IHDesc1 x).
      - apply H1.
      - reflexivity.
      - destruct (f1 i) eqn: Hf1 in H6.
        ** rewrite H6 in E. discriminate.
        ** destruct (f2 i).
          ++ rewrite H6 in E. discriminate.
          ++ rewrite Hf1 in IHDesc1. rewrite <- IHDesc1. unfold findWithDefaultOption. congruence.
      -  destruct (f1 i) eqn: Hf1 in H6.
        ** rewrite H6 in E. discriminate.
        ** destruct (f2 i).
          ++ rewrite H6 in E. discriminate.
          ++ rewrite Hf1 in IHDesc1. unfold findWithDefaultOption in IHDesc2. congruence.
Qed.

Lemma findWithDefault_Sem:
  forall {a} {s: IntMap a} {f x i}, Sem s f ->
                      match (f i) with
                      | Some v => findWithDefaultOption x i s = Some v
                      | None => findWithDefaultOption x i s = Some x
                      end.
Proof.
  intros. destruct H.
  * destruct (f i) eqn:E; specialize (H i).
    + rewrite E in H. discriminate.
    + unfold findWithDefaultOption. simpl. reflexivity.
  * destruct (f i) eqn:E; move: (findWithDefault_Desc x i HD) => H;
       rewrite E in H; apply H.
Qed.

(** Verification of [lookupLT] **)

(** *** Verification of [isSubmapOf] *)
Lemma isSubmapOfBy_disjoint {a} (f : a -> a -> bool) :
  forall (s1 :IntMap a) r1 f1 s2 r2 f2,
  rangeDisjoint r1 r2 = true ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall (i : N) v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ (f v1 v2 = true)) <-> False.
Proof.
  intros ??? ??? Hdis HD1 HD2.
  intuition.
  destruct (Desc_some_f HD1) as [i [v Hi]].
  eapply rangeDisjoint_inRange_false_false with (i := i).
  ** eassumption.
  ** eapply Desc_inside; eassumption.
  ** eapply H in Hi.
     destruct Hi as [v2 [Hi EQ]].
     apply (Desc_inside HD2) in Hi.
     assumption.
Qed.


Lemma isSubmapOfBy_disjoint1 {a} :
  forall (s1 :IntMap a) r1 f1 (s2:IntMap a) r2 f2,
  rangeDisjoint r1 r2 = true ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  forall (i : N) v1, f1 i = Some v1 -> f2 i = None.
Proof.
  intros ??? ??? Hdis HD1 HD2.
  intuition.
  eapply Desc_outside; eauto.
  apply not_true_is_false.
  unfold not.
  eapply rangeDisjoint_inRange_false_false with (i := i).

  ** eassumption.
  ** eapply Desc_inside; eassumption.
Qed.



Program Fixpoint isSubmapOfBy_Desc {a} (f : a -> a -> bool)
  (s1 :IntMap a) r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  isSubmapOfBy f s1 s2 = true <->
  (forall i v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ f v1 v2 = true) := _.
Next Obligation.
  revert isSubmapOfBy_Desc H H0.
  intros IH HD1 HD2.
  inversion_Desc HD1; inversion_Desc HD2.
  * (* Both are tips *)
    clear IH.
    unfold isSubmapOfBy.
    simpl; subst.
    unfoldMethods.
    destruct (k =? k0) eqn:h.
    + apply N.eqb_eq in h; subst.
      split.
      -- intros fh i v1 h0.
         rewrite H2 in h0.
         destruct (i =? k0) eqn:EQ; try discriminate.
         inversion h0; subst.
         exists v0. split; auto.
         rewrite H3. rewrite EQ. auto.
      -- intro h0.
         destruct (Desc_some_f HD1) as [i1 [v1 E]].
         destruct (h0 i1 v1 E) as [v2 [E2 F]].
         rewrite H2 in E.  rewrite H3 in E2.
         destruct (i1 =? k0) eqn:EQ; try discriminate.
         inversion E. inversion E2. subst.
         auto.
    + split. intro h1; discriminate.
      intro h1.
      destruct (Desc_some_f HD1) as [i1 [v1 E]].
      destruct (h1 i1 v1 E) as [v2 [E2 F]].
      rewrite H2 in E.  rewrite H3 in E2.
      destruct (i1 =? k0) eqn:EQ0; try discriminate.
      destruct (i1 =? k) eqn:EQ1; try discriminate.
      apply N.eqb_eq in EQ1.
      apply N.eqb_eq in EQ0.
      subst.
      rewrite N.eqb_refl in h.
      discriminate.
  * (* Tip left, Bin right *)
    unfold isSubmapOfBy.
    erewrite lookup_Desc; eauto.
    assert (K: f1 k = Some v).
    { rewrite H2. rewrite N.eqb_refl. auto. }
    rewrite H11.

    destruct (f0 k) eqn:F0; simpl;
      [| destruct (f3 k) eqn:F3; simpl].
    

Admitted.



(** *** Verification of [member] *)

Lemma member_Desc:
 forall {a}{s : IntMap a}{r f i}, Desc s r f -> member i s = ssrbool.isSome (f i).
Proof.
 intros ????? HD.
 induction HD; subst.
 * simpl.
   unfoldMethods.
   rewrite H.
   destruct (i =? k) eqn:Ei.
   - simpl. auto.
   - simpl. auto.
 * rewrite H4. clear H4.
   simpl member.
   rewrite IHHD1 IHHD2. clear IHHD1 IHHD2.

   apply nomatch_zero; [auto|..]; intros.
   + rewrite (Desc_outside HD1) ; last inRange_false.
     rewrite (Desc_outside HD2) ; last inRange_false.
     reflexivity.
   + rewrite (Desc_outside HD2) ; last inRange_false.
     rewrite oro_None_r. reflexivity.
   + rewrite (Desc_outside HD1) ; last inRange_false.
     rewrite oro_None_l. reflexivity.
Qed.


Lemma member_Desc0:
  forall {a}{s:IntMap a} {r f i}, Desc0 s r f -> member i s = ssrbool.isSome (f i).
Proof.
  intros.
  destruct H; simpl; auto.
  rewrite H. simpl. auto.
  eapply member_Desc; eauto.
Abort.

Lemma member_Sem:
  forall {a}{s:IntMap a}{f i}, Sem s f -> member i s = ssrbool.isSome (f i).
Proof.
  intros.
  destruct H.
  * rewrite H. reflexivity.
  * erewrite member_Desc; eauto.
Qed.

Lemma Desc_has_member:
  forall {a}{s:IntMap a}{r f}, Desc s r f -> exists i, member i s = true.
Proof.
  intros ???? HD.
  destruct (Desc_some_f HD) as [j [v ?]].
  exists j.
  rewrite (member_Desc HD).
  rewrite H. reflexivity.
Qed.

(** *** Verification of [notMember] *)

Lemma notMember_Sem:
  forall {a}{s:IntMap a}{f i}, Sem s f -> notMember i s = negb (ssrbool.isSome (f i)).
Proof.
  intros.
  change (negb (member i s) = negb (ssrbool.isSome (f i))).
  f_equal.
  apply member_Sem.
  assumption.
Qed.

(** *** Verification of [null] *)

Lemma null_Sem:
  forall {a}{s:IntMap a}{f}, Sem s f -> null s = true <-> (forall i, f i = None).
Proof.
  intros a s f HSem.
  destruct HSem.
  * intuition.
  * assert (null s = false) by (destruct HD; reflexivity).
    intuition try congruence.
    destruct (Desc_some_f HD) as [x [v ?]].
    specialize (H0 x).
    congruence.
Qed.




 
(** *** Verification of [empty] *)

Lemma empty_Sem {a} (f : N -> option a) : Sem empty f <-> forall i, f i = None.
Proof.
  split.
  - intro s.
    apply null_Sem in s.
    simpl in s. destruct s as [s _].
    apply s.
    auto.
  - now constructor.
Qed.

Lemma empty_WF {a} : WF (empty : IntMap a).
Proof. now exists (fun _ => None); constructor. Qed.
Hint Resolve empty_WF.


(** *** Verification of [insert] *)

Lemma disjoint_reorder a (s1 : IntMap a) r1 f1 s2 r2 f2 :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  rangeDisjoint r2 r1 = true ->
   forall i : N, oro (f1 i) (f2 i) = oro (f2 i) (f1 i).
Proof.
  intros h0 h1 h2 i.
  destruct (f1 i) eqn:F1; destruct (f2 i) eqn:F2; simpl; auto.
  - assert (h3 : f2 i = None).
    rewrite rangeDisjoint_sym in h2.
    eapply isSubmapOfBy_disjoint1; eauto.
    rewrite h3 in F2.
    discriminate.
Qed.


Lemma link_Desc:
    forall {a} p1' (s1 : IntMap a) r1 f1 p2' s2 r2 f2 r f,
    Desc s1 r1 f1 ->
    Desc s2 r2 f2 ->
    p1' = rPrefix r1 ->
    p2' = rPrefix r2 ->
    rangeDisjoint r1 r2 = true->
    r = commonRangeDisj r1 r2 ->
    (forall i, f i = oro (f1 i) (f2 i)) ->
  Desc (link p1' s1 p2' s2) r f.
Proof.
  intros; subst.
  unfold link.
  rewrite -> branchMask_spec. (* Uses the fact that IntSet.Internal.branchMask = branchMask *)
  rewrite mask_spec.
  rewrite -> zero_spec by (apply commonRangeDisj_rBits_pos; eapply Desc_rNonneg; eassumption).
  rewrite if_negb.
  match goal with [ |- context [N.testbit ?i ?b] ]  => destruct (N.testbit i b) eqn:Hbit end.
  * assert (Hbit2 : N.testbit (rPrefix r2) (rBits (commonRangeDisj r1 r2) - 1)%N = false).
    { apply not_true_is_false.
      rewrite <- Hbit.
      apply not_eq_sym.
      apply (commonRangeDisj_rBits_Different r1 r2);
          try (eapply Desc_rNonneg; eassumption); auto.
    }
    rewrite rangeDisjoint_sym in H3.
    rewrite -> commonRangeDisj_sym in * by (eapply Desc_rNonneg; eassumption).
    apply (DescBin _ _ _ _ _ _ _  _ _ _ f H0 H); auto.
    + apply commonRangeDisj_rBits_pos; (eapply Desc_rNonneg; eassumption).
    + rewrite <- Hbit2.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
    + rewrite <- Hbit at 1.
      rewrite -> commonRangeDisj_sym by (eapply Desc_rNonneg; eassumption).
      rewrite rangeDisjoint_sym in H3.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
    +
      intro i. erewrite disjoint_reorder; eauto.
      rewrite rangeDisjoint_sym.
      auto.
  * assert (Hbit2 : N.testbit (rPrefix r2) (rBits (commonRangeDisj r1 r2) - 1)%N = true).
    { apply not_false_iff_true.
      rewrite <- Hbit.
      apply not_eq_sym.
      apply commonRangeDisj_rBits_Different; try (eapply Desc_rNonneg; eassumption); auto.
    }
    apply (DescBin _ _ _ _ _ _ _ _ _ _ f H H0); auto.
    + apply commonRangeDisj_rBits_pos; (eapply Desc_rNonneg; eassumption).
    + rewrite <- Hbit.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
    + rewrite <- Hbit2 at 1.
      rewrite -> commonRangeDisj_sym by (eapply Desc_rNonneg; eassumption).
      rewrite rangeDisjoint_sym in H3.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
Qed.

Lemma disjoint_neq : forall x y, (x =? y) = false ->
  rangeDisjoint (singletonRange x) (singletonRange y) = true.
Proof.
       unfold singletonRange, rangeDisjoint. unfold isSubrange, rPrefix, inRange.
intros x y EE.
rewrite !N.shiftl_0_r.
rewrite !N.shiftr_0_r.
rewrite EE.
rewrite andb_false_l.
rewrite orb_false_l.
rewrite N.eqb_sym.
rewrite EE.
rewrite andb_false_l.
simpl. auto.
Qed.

Lemma insert_Nil_Desc a:
  forall e (v:a) r f,
  r = (singletonRange e) ->
  (forall i, f i = if (i =? e) then Some v else None) ->
  Desc (insert e v Nil) r f.
Proof.
  intros; subst.
  apply DescTip; try nonneg.
Qed.

Lemma rPrefix_singletonRange e : rPrefix (singletonRange e) = e.
Proof. unfold rPrefix, singletonRange. rewrite N.shiftl_0_r. auto. Qed.
Hint Rewrite rPrefix_singletonRange.

Lemma insert_Desc a:
  forall e v r1,
  forall (s2:IntMap a) r2 f2,
  forall r f,
  Desc s2 r2 f2 ->
  r1 = (singletonRange e) ->
  r = commonRange r1 r2 ->
  (forall i, f i = if (i =? e) then Some v else f2 i) ->
  Desc (insert e v s2) r f.
Proof.
  intros ???????? HD ?? Sf; subst.
  generalize dependent f.
  induction HD as [p2' bm2 r2 f2|s2 r2 f2 s3 r3 f3 p2' r]; subst; intros f' Hf.
  + simpl.
    unfoldMethods.
    pose (h0 := H e). clearbody h0.
    destruct (e =? bm2) eqn:EE.
    rewrite <- reflect_iff in EE; try eapply N.eqb_spec. subst.
    eapply DescTip.
    ++ intro i. specialize (Hf i). rewrite H in Hf.
       destruct (i =? bm2) eqn:EI; auto.
    ++ unfold singletonRange, commonRange, isSubrange, inRange, commonRangeDisj, rPrefix. simpl.
       rewrite andb_true_r.
       rewrite N.shiftl_0_r.
       rewrite N.eqb_refl. auto.
    ++ assert (h1 : rangeDisjoint (singletonRange e) (singletonRange bm2) = true).
         { eapply disjoint_neq; eauto. }
       eapply link_Desc with (f1 := fun i => if i =? e then Some v else None) (f2 := f); eauto.
       eapply DescTip; eauto.
       eapply DescTip; eauto.
       simpl. rewrite N.shiftl_0_r. auto.
       simpl. rewrite N.shiftl_0_r. auto.
       eapply disjoint_commonRange; eauto.
       intro i. rewrite Hf. unfold oro.
       destruct (i =? e); simpl; auto.
  + simpl.
    eapply nomatch_zero; auto.
    ++ intro RF.
       assert (h0: rangeDisjoint (singletonRange e) r0 = true). {
         unfold singletonRange, rangeDisjoint.
         unfold isSubrange. simpl. rewrite N.shiftl_0_r.
         rewrite RF.
         rewrite andb_false_l.
         rewrite orb_false_l.
         admit.
       }
       eapply link_Desc with (f1 := fun i => if i =? e then Some v else None); eauto.
       eapply DescTip; eauto.
       eapply DescBin; eauto.
       rewrite rPrefix_singletonRange; auto.
       eapply disjoint_commonRange; eauto.
       intro i. rewrite Hf. unfold oro. destruct (i =? e); simpl; auto.
    ++ intros R1 R2.
       eapply DescBin with (f1 := fun i => if i =? e then Some v else s3 i); eauto.
       admit.
       admit.
       admit.
       admit.
       admit.
       intro i. rewrite Hf.
       destruct (i =? e); simpl; auto.
    ++ intros R1 R2.
       admit.
Admitted.


Lemma insert_Sem:
  forall a e (v:a) s2 f2 f,
  Sem s2 f2 ->
  (forall i, f i = if (i =? e) then Some v else f2 i) ->
  Sem (insert e v s2) f.
Proof.
  intros.
  destruct H.
  * eapply DescSem. apply insert_Nil_Desc; auto.
    solve_f_eq.
  * eapply DescSem. eapply insert_Desc; eauto.
Qed.

Lemma insert_WF:
  forall a n (v:a) s, WF s -> WF (insert n v s).
Proof.
  intros.
  destruct H.
  eexists.
  eapply insert_Sem; eauto.
  intro i; reflexivity.
Qed.

(* Verification of [filter] *)

Definition IMFilter {a} p (s: IntMap a) :=
  Data.IntMap.Internal.filter p s.

Print Data.IntMap.Internal.filter.

Lemma filter_Desc:
  forall {a} p (s: IntMap a) r f f',
    Desc s r f ->
    (forall (i: N), f' i = match f i with
                 | None => None
                 | Some v => if p v then Some v else None
                 end) ->                                    
    Desc0 (IMFilter p s) r f'.
Proof.
  intros.
  revert f' H0.
  induction H.
  * intros.
    simpl. subst. destruct (p v) eqn: Hpv.
     + eapply  Desc0NotNil; eauto. apply DescTip; eauto.
       intro. specialize (H1 i). specialize (H i). rewrite H in H1.
       destruct (i =? k) eqn: Hik; auto. rewrite Hpv in H1. auto.
       eapply isSubrange_refl.
     + eapply Desc0Nil. intro. specialize (H i). specialize (H1 i). destruct (f i).
       - destruct (i =? k).
         ** inversion H. subst. rewrite Hpv in H1. auto.
         ** discriminate.
       - auto.
  * intros. subst. simpl.
    rewrite foldl'Bits_foldlBits.
    fold (filterBits p (rPrefix r) bm).
    eapply tip_Desc0; try assumption; try reflexivity.
    + intro i.
      rewrite H3.
      rewrite H1.
      unfold bitmapInRange.
      destruct (inRange i r) eqn:Hir.
      - rewrite testbit_filterBits by isBitMask.
        f_equal. f_equal.
        clear p H3.
        rewrite N.div_mod with (a := i) (b := id WIDTH) at 1
          by (intro Htmp; inversion Htmp).
        f_equal.
        ** destruct r as [p b]. unfold inRange, rPrefix, rBits, snd in *.
           rewrite N.eqb_eq in Hir.
           subst.
           rewrite N.shiftl_mul_pow2 by nonneg.
           rewrite N.shiftr_div_pow2 by nonneg.
           rewrite N.mul_comm.
           reflexivity.
        ** rewrite N.land_ones by nonneg.
           rewrite H0.
           reflexivity.
      - rewrite andb_false_l. reflexivity.
    + isBitMask.
  * intros. subst. simpl.
    eapply bin_Desc0.
    + apply IHDesc1; intro; reflexivity.
    + apply IHDesc2; intro; reflexivity.
    + assumption.
    + assumption.
    + assumption.
    + reflexivity.
    + reflexivity.
    + solve_f_eq.
  
  intros. revert f' H0. induction H.
  * intros. simpl. subst. 
  induction H.
  * simpl. destruct (p v) eqn: Hpv.
  + eapply Desc0NotNil; auto. apply DescTip. intro. specialize (H i). specialize (H0 i).
    rewrite H in H0. destruct (i =? k) eqn: Hk.
      - rewrite Hpv in H0. auto.
      - auto.
      - auto.
      - rewrite <- H1. apply isSubrange_refl.
    + eapply Desc0Nil. intro. specialize (H0 i). specialize (H i). rewrite H in H0. destruct (i =? k).
      - rewrite Hpv in H0. apply H0.
      - apply H0.
   * simpl. unfold bin.
     specialize (IHDesc1 p (fun i => match f1 i with
                                  | None => None
                                  | Some v => if p v then Some v else None
                                  end) ltac:(intros; auto)).
     specialize (IHDesc2 p (fun i => match f2 i with
                                  | None => None
                                  | Some v => if p v then Some v else None
                                  end) ltac:(intros; auto)).
     simpl. destruct (IMFilter p m1) eqn: Hf1.
     + destruct (IMFilter p m2) eqn: Hf2.
       - eapply Desc0NotNil; eauto. eapply DescBin'; eauto.
          **  
          ** admit.
          ** intro. specialize (H7 i). specialize (H0 i). rewrite H7 in H0. admit.
          ** apply isSubrange_refl.
       - eapply Desc0NotNil; eauto. eapply DescBin; eauto.
          ** admit.   
          ** admit.
          ** intro. specialize (H7 i). specialize (H0 i). 
          ** apply isSubrange_refl.
      - admit.
    
        
(** * Specifying [restrictKeys] *)

(* We can extract the argument to [deferredFix] from the definition of [restrictKeys]. *)

Definition restrictKeys_f {a} :
  (IntMap a -> IntSet -> IntMap a) -> (IntMap a -> IntSet -> IntMap a).
Proof.
  let rhs := eval unfold restrictKeys in (@restrictKeys a) in
  match rhs with context[ deferredFix2 ?f ] => exact f end.
Defined.


Definition restrictKeys_body {a} := restrictKeys_f (@restrictKeys a).

Lemma restrictKeys_eq {a} (m : IntMap a) s :
  restrictKeys m s = restrictKeys_body m s.
Proof.
  enough (@restrictKeys a = restrictKeys_body) by congruence.
  apply deferredFix2_eq.
Qed.

Definition restrictBitMapToRange r bm :=
  let p := rPrefix r in
  let msk := rMask r in
    N.land (N.land bm (N.lxor (bitmapOf p - 1)%N (N.ones 64%N)))
           (N.lor (bitmapOf (N.lor p (N.lor msk (msk - 1))))
           (bitmapOf (N.lor p (N.lor msk (msk - 1))) - 1)%N).

Lemma bin_Desc0:
  forall a (m1 : IntMap a) r1 f1 m2 r2 f2 p msk r f,
    Desc0 m1 r1 f1 ->
    Desc0 m2 r2 f2 ->
    (0 < rBits r)%N ->

    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = rPrefix r ->
    msk = rMask r ->
    (forall i, f i = oro (f1 i) (f2 i)) ->
    Desc0 (bin p msk m1 m2) r f.
Admitted.

Ltac point_to_inRange_Map :=
  lazymatch goal with
    | [ HD : IntSetProofs.Desc ?s ?r ?f, Hf : ?f ?i = true |- _ ]
      => apply (IntSetProofs.Desc_inside HD) in Hf
    | [ H : bitmapInRange ?r ?bm ?i = true |- _ ]
      => apply bitmapInRange_inside in H
    | [ HD : Desc ?m ?r ?f, Hf : ?f ?i = Some _ |- _ ]
      => apply (Desc_inside HD) in Hf
  end.

Ltac solve_f_eq_disjoint_Map :=
  solve_f_eq;
  repeat point_to_inRange_Map;
  repeat saturate_inRange;
  try inRange_disjoint. (* Only try this, so that we see wher we are stuck. *)


Program Fixpoint restrictKeys_Desc
  a (m1 : IntMap a) r1 f1 s2 r2 f2 f
  { measure (size_nat m1 + Data.IntSet.Internal.size_nat s2) } :
  Desc m1 r1 f1 ->
  IntSetProofs.Desc s2 r2 f2 ->
  (forall i, f i = if f2 i then f1 i else None) ->
  Desc0 (restrictKeys m1 s2) r1 f
  := fun HD1 HD2 Hf => _.
Next Obligation.
  rewrite restrictKeys_eq.
  unfold restrictKeys_body, restrictKeys_f.
  unfoldMethods.

  destruct HD1.
  * (* m1 is a Tip *)
    subst.
    erewrite IntSetProofs.member_Desc by eassumption.
    destruct (f2 k) eqn: Hf2.
    + eapply Desc0NotNil; try (apply isSubrange_refl); try (intro; reflexivity).
      eapply DescTip; try reflexivity.
      intro i.
      rewrite Hf H; clear Hf H.
      destruct (N.eqb_spec i k).
      - subst. rewrite Hf2. reflexivity.
      - destruct (f2 i); reflexivity.
    + apply Desc0Nil.
      intro i.
      rewrite Hf H; clear Hf H.
      destruct (N.eqb_spec i k).
      - subst. rewrite Hf2. reflexivity.
      - destruct (f2 i); reflexivity.

  * (* m1 is a Bin *)
    inversion HD2.
    + (* s2 is a Tip *)
      clear restrictKeys_Desc. subst.
      set (m := Bin (rPrefix r) (rMask r) m1 m2) in *.
      admit.
    + (* s2 is also a Bin *)
      subst.
      set (m := Bin (rPrefix r) (rMask r) m1 m2) in *.
      set (s := IntSet.Internal.Bin (rPrefix r2) (rMask r2) s1 s0) in *.
      rewrite -> !shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r)).
      ++ (* s2 is smaller than m1 *)
        apply nomatch_zero_smaller; try assumption; intros.
        - (* s2 is disjoint of s1 *)
          apply Desc0Nil.
          solve_f_eq_disjoint_Map.

        - (* s2 is part of the left half of m1 *)
          eapply Desc0_subRange.
          eapply restrictKeys_Desc; clear restrictKeys_Desc; try eassumption.
          ** subst m s. simpl. omega.
          ** solve_f_eq_disjoint_Map.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
        - (* s2 is part of the right half of m1 *)
          eapply Desc0_subRange.
          eapply restrictKeys_Desc; clear restrictKeys_Desc; try eassumption.
          ** subst m s. simpl. omega.
          ** solve_f_eq_disjoint_Map.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.

      ++ (* s2 is not smaller than m1 *)
        destruct (N.ltb_spec (rBits r) (rBits r2)).
        -- (* s2 is smaller than m1 *)
          apply nomatch_zero_smaller; try assumption; intros.
          - (* m1 is disjoint of s2 *)
            apply Desc0Nil.
            solve_f_eq_disjoint_Map.
          - (* s1 is part of the left half of s2 *)
            eapply Desc0_subRange.
            eapply restrictKeys_Desc; clear restrictKeys_Desc; try eassumption.
            ** subst m s. simpl. omega.
            ** eapply DescBin; try beassumption; reflexivity.
            ** solve_f_eq_disjoint_Map.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.

          - (* s1 is part of the right half of s2 *)

            eapply Desc0_subRange.
            eapply restrictKeys_Desc; clear restrictKeys_Desc; try eassumption.
            ** subst s m. simpl. omega.
            ** eapply DescBin; try beassumption; reflexivity.
            ** solve_f_eq_disjoint_Map.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.

        -- (* s1 and s2 are the same size *)
          apply same_size_compare; try Nomega; intros.
          - subst.
            eapply bin_Desc0; try assumption; try reflexivity.
            ** eapply restrictKeys_Desc.
               --- subst s m. simpl. omega.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ** eapply restrictKeys_Desc.
               --- subst s m. simpl. omega.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.
            ** solve_f_eq_disjoint_Map.
          - apply Desc0Nil.
            solve_f_eq_disjoint_Map.
Admitted.

Lemma restrictKeys_Sem:
  forall a (m1 : IntMap a) f1 s2 f2,
  Sem m1 f1 ->
  IntSetProofs.Sem s2 f2 ->
  Sem (restrictKeys m1 s2) (fun i => if f2 i then f1 i else None).
Proof.
  intros.
  destruct H; [|destruct H0].
  * rewrite restrictKeys_eq.
    apply SemNil. solve_f_eq.
  * replace (restrictKeys s IntSet.Internal.Nil) with (@Nil a) by (rewrite restrictKeys_eq; destruct s; reflexivity).
    apply SemNil. solve_f_eq.
  * eapply Desc0_Sem. eapply restrictKeys_Desc; try eauto.
Qed.

Lemma restrictKeys_WF:
  forall a (m1 : IntMap a) s2, WF m1 -> IntSetProofs.WF s2 -> WF (restrictKeys m1 s2).
Proof.
  intros.
  destruct H, H0.
  eexists. apply restrictKeys_Sem; eassumption.
Qed.



(** Verification of [map] **)


Definition IMMap {a b} (f : a -> b) (s : IntMap a):=
  Data.IntMap.Internal.map f s.


Lemma map_Desc: forall a b (s: IntMap a) f1 (f2: a -> b) r,
    Desc s r f1 -> Desc (IMMap f2 s) r (fun i => match (f1 i) with
                                             | Some x => Some (f2 x)
                                             | None => None
                                             end).
Proof.
  intros. induction H.
  * simpl. eapply DescTip.
    - intro i. specialize (H i). rewrite H. destruct (i =? k); reflexivity.
    - apply H0.
  * simpl. eapply DescBin; auto. intro i. simpl. specialize (H6 i).
    rewrite H6. unfold oro. destruct (f1 i) eqn: Hf; reflexivity.
Qed.

Lemma map_Sem: forall a b (s: IntMap a) f1 (f2: a -> b),
    Sem s f1 -> Sem (IMMap f2 s) (fun i => match (f1 i) with
                                             | Some x => Some (f2 x)
                                             | None => None
                                             end). 
Proof.
  intros. induction H.
  - apply SemNil. intros i0. specialize (H i0). rewrite H. reflexivity.
  - eapply DescSem. eapply map_Desc. apply HD. 
Qed.

(** Verification of [mapWithKey] **)

Definition IMMapWithKey {a b} (f: Key -> a -> b) (s: IntMap a) :=
  Data.IntMap.Internal.mapWithKey f s.

Lemma mapWithKey_Desc: forall a b (s: IntMap a) r f (fmap : Key -> a -> b),
    Desc s r f -> Desc (IMMapWithKey fmap s) r (fun i => match (f i) with
                                                  | Some x => Some (fmap i x)
                                                  | None => None
                                                  end).
Proof.
  intros. induction H.
  * simpl. eapply DescTip; auto.
    - intro i. specialize (H i). rewrite H. destruct (i =? k) eqn: Hik.
      + apply Neqb_ok in Hik. rewrite Hik. reflexivity.
      + reflexivity.
  * simpl. eapply DescBin; auto. intro i. simpl. specialize (H6 i).
    rewrite H6. unfold oro. destruct (f1 i) eqn: Hf; reflexivity.
Qed.

Lemma mapWithKey_Sem: forall a b (s: IntMap a) f (fmap: Key -> a -> b),
    Sem s f -> Sem (IMMapWithKey fmap s) (fun i => match (f i) with
                                             | Some x => Some (fmap i x)
                                             | None => None
                                             end). 
Proof.
  intros. induction H.
  - apply SemNil. intros i. specialize (H i). rewrite H. reflexivity.
  - eapply DescSem. eapply mapWithKey_Desc. apply HD.
Qed.

Fixpoint sem_for_lists {a: Type} (l : list (Key * a)) (i : Key) :=
  match l with
  | nil => None
  | (x,y) :: t => if i == x then Some y else sem_for_lists t i
  end.


Lemma mapKeys_Desc: forall a (fmap : Key -> Key) (s: IntMap a) r f,
    Desc s r f ->
    Desc (mapKeys fmap s) r (fun i => (sem_for_lists (rev (foldrWithKey (fun k v t => ((fmap k), v) :: t) nil s)) i)).
Proof.
  intros.
  unfold mapKeys. simpl. 
Admitted.

(* Verification of [lookupMin] *)

Lemma empty_no_elts : forall {a}  (m: IntMap a),
      (forall i, sem m i = None) <-> empty = m.
Proof.
  intros. split; intros.
  * induction m; auto.
    + simpl in H. unfold oro in H.
      assert (forall i, sem m2 i = None). {admit.}
      assert (forall i, sem m3 i = None). {admit.}
     intuition. symmetry in H2. rewrite H2. symmetry in H3. rewrite H3. unfold empty.                                                     admit.
    + simpl in H. specialize (H k). unfold "==" in H. unfoldMethods. rewrite N.eqb_refl in H. discriminate. 
  * unfold empty in H. rewrite <-  H. simpl. reflexivity.
Admitted.

Definition go {a} := fix go (arg_2__ : IntMap a) : option (Key * a) :=
        match arg_2__ with
        | Bin _ _ l' _ => go l'
        | Tip k v => Some (k, v)
        | Nil => None
        end.

Lemma goL_Desc:
  forall {a} (s : IntMap a) r f,
    Desc s r f -> match go s with
                 | None => (forall i, sem s i = None)
                 | Some (k, v) => sem s k = Some v /\ (forall i v1, sem s i = Some v1 -> (k <= i))
                 end.
Proof.
  intros. destruct (go s) eqn: Hg.
  * 
  Search mask. Admitted.
  
Print lookupMin.

Lemma lookupMin_Desc:
  forall {a} (s : IntMap a) r f,
    Desc s r f ->
    match lookupMin s with
    | None => (forall i, sem s i = None)
    | Some (k, v) => sem s k = Some v /\ (forall i v1, sem s i = Some v1 -> (k <= i))
    end.
Proof.
  intros. induction H.
  * simpl. unfoldMethods. rewrite N.eqb_refl. split.
    + reflexivity.
    + intros. destruct (i =? k) eqn: Hik.
      - apply Neqb_ok in Hik. subst. move: (N.le_refl k) => H2. intuition.
      - discriminate.
  * simpl. unfoldMethods. destruct (msk <? 0) eqn: Hm.
    + destruct msk; discriminate.
    + fold (@go a). move: (goL_Desc m1 r1 f1 H) => H7. destruct (go m1) eqn: Hg.
      - destruct p0. destruct H7. split.
        ** unfold oro. rewrite H7. reflexivity.
        ** unfold oro. intros i v1. destruct (sem m1 i) eqn: Hs.
          ++ specialize (H8 i v1). rewrite Hs in H8. auto. 
          ++  admit.
      - destruct (lookupMin m2) in IHDesc2.
        ** destruct p0. subst.
        ** intro. specialize (H7 i). unfold oro. rewrite H7. rewrite IHDesc2. reflexivity.
Admitted.







