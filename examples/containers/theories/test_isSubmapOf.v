(** Test file: isSubmapOfBy_Desc truth analysis.

    VERDICT: isSubmapOfBy_Desc and isSubmapOfBy_Desc1 are TRUE.

    The helper isSubmapOfBy_Bin is FALSE (see isSubmapOfBy_Bin_false in IntMapProofs.v),
    but the top-level theorem is correctly stated: with Desc well-formedness hypotheses,
    isSubmapOfBy correctly characterizes semantic submap containment.
*)

Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Bool.Bool.

From Coq Require Import ssreflect ssrbool ssrfun.

Require Import DyadicIntervals.
Require Import BitUtils.

Require Import GHC.Base.
Require Import GHC.Num.
Require Import IntSetProofs.
Require Import Data.IntSet.Internal.
Require Import Data.IntMap.Internal.
Require Import IntMapProofs.

Import GHC.Base.

Set Bullet Behavior "Strict Subproofs".

(** Part 1: Computational verification *)

Eval compute in (isSubmapOfBy (fun (_ _ : N) => true) (Tip 1%N 42%N) (Tip 1%N 42%N)).
(* = true *)

Eval compute in (isSubmapOfBy (fun (_ _ : N) => true) (@Nil N) (Tip 1%N 42%N)).
(* = true *)

Eval compute in (isSubmapOfBy (fun (_ _ : N) => true) (Tip 1%N 42%N) (Bin 0%N 1%N (Tip 0%N 10%N) (Tip 1%N 42%N))).
(* = true *)

(* ILL-FORMED: Bin 0 1 (Tip 1 42) Nil — Nil child violates Desc *)
Eval compute in (isSubmapOfBy (fun (_ _ : N) => true) (Tip 1%N 42%N) (Bin 0%N 1%N (Tip 1%N 42%N) (@Nil N))).
(* = false *)

Eval compute in (isSubmapOfBy (fun (_ _ : N) => true)
  (Bin 0%N 1%N (Tip 0%N 10%N) (Tip 1%N 42%N))
  (Bin 0%N 2%N (Bin 0%N 1%N (Tip 0%N 10%N) (Tip 1%N 42%N)) (Tip 2%N 99%N))).
(* = true *)


(** Part 2: Helper lemmas *)

(** Analogue of IntSetProofs.pointwise_iff for IntMap's option-valued semantics *)
Lemma pointwise_iff_map :
  forall {a} (pred : a -> a -> bool) (f1 f1' f2 f2' : N -> option a),
  (forall i, f1 i = f1' i) ->
  (forall i, f2 i = f2' i) ->
  ((forall i v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ pred v1 v2 = true) <->
   (forall i v1, f1' i = Some v1 -> exists v2, f2' i = Some v2 /\ pred v1 v2 = true)).
Proof.
  intros a pred0 f1 f1' f2 f2' Hf1 Hf2.
  split; intros Hall i v1 Hfi.
  - rewrite <- Hf1 in Hfi. destruct (Hall i v1 Hfi) as [v2 [Hv2 Hp]].
    exists v2. rewrite <- Hf2. auto.
  - rewrite Hf1 in Hfi. destruct (Hall i v1 Hfi) as [v2 [Hv2 Hp]].
    exists v2. rewrite Hf2. auto.
Qed.

(** Disjoint ranges => semantic containment is vacuously false *)
Lemma isSubmapOfBy_disjoint_map {a} (pred : a -> a -> bool) :
  forall (s1 : IntMap a) r1 f1 s2 r2 f2,
  rangeDisjoint r1 r2 = true ->
  IntMapProofs.Desc s1 r1 f1 -> IntMapProofs.Desc s2 r2 f2 ->
  (forall i v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ pred v1 v2 = true) <-> False.
Proof.
  intros ??? ??? Hdis HD1 HD2.
  split; [| tauto].
  intro Hall.
  destruct (IntMapProofs.Desc_some_f HD1) as [i [v1 Hi]].
  destruct (Hall i v1 Hi) as [v2 [Hv2 _]].
  eapply rangeDisjoint_inRange_false_false with (i := i).
  - eassumption.
  - eapply IntMapProofs.Desc_inside; eassumption.
  - eapply IntMapProofs.Desc_inside; eassumption.
Qed.

(** Larger range => larger tree cannot be a semantic submap.
    if all keys of s1 are also in s2 (with any values), and r1 is broader
    than r2, we get a contradiction because s1 has keys in both halves
    of r1 but r2 can only cover one half. *)
Lemma larger_submap_false {a} (pred : a -> a -> bool) :
  forall (s1 : IntMap a) r1 f1 s2 r2 f2,
  (rBits r2 < rBits r1)%N ->
  IntMapProofs.Desc s1 r1 f1 -> IntMapProofs.Desc s2 r2 f2 ->
  (forall i v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ pred v1 v2 = true) ->
  False.
Proof.
  intros s1 r1 f1 s2 r2 f2 Hsmaller HD1 HD2 Hall.
  (* Weaken: derive that every key in f1 is in range of r2 *)
  assert (Hrange : forall i v, f1 i = Some v -> inRange i r2 = true).
  { intros i v Hi.
    destruct (Hall i v Hi) as [v2 [Hv2 _]].
    eapply IntMapProofs.Desc_inside; eassumption. }
  (* Use destruct to get clean hypotheses *)
  destruct HD1 as [a0 k v r1' f1' Hf1_tip Hr1_eq | a0 m1 r1_l f1_l m2 r1_r f1_r p msk r1' f1' HD1_l HD1_r Hbits Hsub_l Hsub_r Hp Hmsk Hf1_oro].
  - (* Tip: rBits r1 = 0, rBits r2 < 0, impossible *)
    subst. simpl in Hsmaller. lia.
  - (* Bin: s1 = Bin p msk m1 m2 *)
    subst.
    (* Get keys from both children *)
    destruct (IntMapProofs.Desc_some_f HD1_l) as [i1 [v1 Hi1]].
    destruct (IntMapProofs.Desc_some_f HD1_r) as [i2 [v2 Hi2]].
    (* i1 is in left half of r1, i2 is in right half *)
    assert (Hi1_l : inRange i1 (halfRange r1' false) = true).
    { eapply inRange_isSubrange_true; [eassumption | eapply IntMapProofs.Desc_inside; eassumption]. }
    assert (Hi2_r : inRange i2 (halfRange r1' true) = true).
    { eapply inRange_isSubrange_true; [eassumption | eapply IntMapProofs.Desc_inside; eassumption]. }
    (* f1' contains both keys *)
    assert (Hf1_i1 : f1' i1 = Some v1).
    { rewrite Hf1_oro. rewrite Hi1. reflexivity. }
    assert (Hf1_i2 : f1' i2 = Some v2).
    { rewrite Hf1_oro.
      assert (inRange i2 (halfRange r1' false) = false).
      { eapply rangeDisjoint_inRange_false.
        - rewrite rangeDisjoint_sym. apply halves_disj. assumption.
        - assumption. }
      rewrite (IntMapProofs.Desc_outside HD1_l).
      2: { eapply inRange_isSubrange_false; eassumption. }
      simpl. exact Hi2. }
    (* Both i1 and i2 are in range of r2 *)
    assert (Hi1_r2 : inRange i1 r2 = true) by (eapply Hrange; eassumption).
    assert (Hi2_r2 : inRange i2 r2 = true) by (eapply Hrange; eassumption).
    (* r2 has rBits < rBits r1', so rBits r2 <= rBits (halfRange r1' h) *)
    assert (rBits r2 <= rBits (halfRange r1' false))%N
      by (rewrite rBits_halfRange; lia).
    assert (rBits r2 <= rBits (halfRange r1' true))%N
      by (rewrite rBits_halfRange; lia).
    (* r2 must be a subrange of both halves — contradiction *)
    assert (isSubrange r2 (halfRange r1' false) = true).
    { apply inRange_both_smaller_subRange with (i := i1); assumption. }
    assert (isSubrange r2 (halfRange r1' true) = true).
    { apply inRange_both_smaller_subRange with (i := i2); assumption. }
    (* r2 is a subrange of both halves, which are disjoint -> contradiction *)
    exfalso.
    eapply rangeDisjoint_isSubrange_false_false.
    + apply halves_disj. exact Hbits.
    + exact H1.
    + exact H2.
Qed.

(** Part 3: Main theorem - isSubmapOfBy_Desc1

    Proof by well-founded induction on (size_nat s1 + size_nat s2),
    following the structure of IntSetProofs.isSubsetOf_Desc.

    We use destruct on the Desc hypotheses rather than inversion_Desc,
    and carefully name all hypotheses to avoid depending on auto-generated names. *)

(** A tactic to get i into range r given Desc *)
Ltac assert_inRange_of_Some HD Hsome :=
  let HirN := fresh "Hir" in
  assert (HirN : inRange _ _ = true) by (eapply IntMapProofs.Desc_inside; [exact HD | exact Hsome]).

Program Fixpoint isSubmapOfBy_Desc1 {a} (pred : a -> a -> bool)
  (s1 : IntMap a) r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  IntMapProofs.Desc s1 r1 f1 ->
  IntMapProofs.Desc s2 r2 f2 ->
  isSubmapOfBy pred s1 s2 = true <->
  (forall i v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ pred v1 v2 = true) := _.
Next Obligation.
  revert isSubmapOfBy_Desc1 H H0.
  intros IH HD1 HD2.
  destruct HD1 as
    [ a1 k1 v1 r1_ f1_ Hf1_sem Hr1_eq
    | a1 s1_l r1_l f1_l s1_r r1_r f1_r p1 m1 r1_ f1_
      HD1_l HD1_r Hbits1 Hsub1_l Hsub1_r Hp1 Hm1 Hf1_oro ];
  destruct HD2 as
    [ a2 k2 v2 r2_ f2_ Hf2_sem Hr2_eq
    | a2 s2_l r2_l f2_l s2_r r2_r f2_r p2 m2 r2_ f2_
      HD2_l HD2_r Hbits2 Hsub2_l Hsub2_r Hp2 Hm2 Hf2_oro ];
  subst.

  * (* Tip / Tip *)
    simpl. unfoldMethods.
    destruct (N.eqb_spec k1 k2).
    + (* k1 = k2 *)
      subst.
      split.
      -- intros Hpred i w1 Hfi.
         rewrite Hf1_sem in Hfi. destruct (N.eqb_spec i k2); [| discriminate].
         subst. inversion Hfi; subst.
         exists v2. rewrite Hf2_sem. rewrite N.eqb_refl. auto.
      -- intros Hall.
         assert (Hfk : f1_ k2 = Some v1) by (rewrite Hf1_sem; rewrite N.eqb_refl; reflexivity).
         destruct (Hall k2 v1 Hfk) as [w2 [Hw2 Hp]].
         rewrite Hf2_sem in Hw2. rewrite N.eqb_refl in Hw2.
         inversion Hw2; subst. exact Hp.
    + (* k1 <> k2 *)
      split.
      -- discriminate.
      -- intros Hall. exfalso.
         assert (Hfk : f1_ k1 = Some v1) by (rewrite Hf1_sem; rewrite N.eqb_refl; reflexivity).
         destruct (Hall k1 v1 Hfk) as [w2 [Hw2 _]].
         rewrite Hf2_sem in Hw2. destruct (N.eqb_spec k1 k2); [congruence | discriminate].

  * (* Tip / Bin *)
    (* isSubmapOfBy pred (Tip k1 v1) (Bin p2 m2 s2_l s2_r) computes to:
       match lookup k1 (Bin p2 m2 s2_l s2_r) with Some y => pred v1 y | None => false end *)
    change (isSubmapOfBy pred (Tip k1 v1) (Bin (rPrefix r2_) (rMask r2_) s2_l s2_r))
      with (match lookup k1 (Bin (rPrefix r2_) (rMask r2_) s2_l s2_r)
            with Some y => pred v1 y | None => false end).
    assert (HD2_bin : IntMapProofs.Desc (Bin (rPrefix r2_) (rMask r2_) s2_l s2_r) r2_ f2_)
      by (eapply IntMapProofs.DescBin; try eassumption; reflexivity).
    rewrite (IntMapProofs.lookup_Desc HD2_bin).
    split.
    + intros Hlook i w1 Hfi.
      rewrite Hf1_sem in Hfi.
      destruct (N.eqb_spec i k1); [| discriminate].
      subst. inversion Hfi; subst.
      destruct (f2_ k1) as [y|] eqn:Hf2k; [| discriminate].
      exists y. auto.
    + intros Hall.
      assert (Hfk : f1_ k1 = Some v1) by (rewrite Hf1_sem; rewrite N.eqb_refl; reflexivity).
      destruct (Hall k1 v1 Hfk) as [w2 [Hw2 Hp]].
      rewrite Hw2. exact Hp.

  * (* Bin / Tip *)
    simpl.
    split.
    + discriminate.
    + intros Hall. exfalso.
      (* Bin has keys in both halves, Tip has one key: contradiction *)
      destruct (IntMapProofs.Desc_some_f HD1_l) as [i1 [w1 Hi1]].
      destruct (IntMapProofs.Desc_some_f HD1_r) as [i2 [w2 Hi2]].
      (* Both keys map into f2_ *)
      assert (Hf_i1 : f1_ i1 = Some w1) by (rewrite Hf1_oro; rewrite Hi1; reflexivity).
      assert (Hf_i2 : f1_ i2 = Some w2).
      { rewrite Hf1_oro.
        assert (inRange i2 (halfRange r1_ true) = true)
          by (eapply inRange_isSubrange_true; [eassumption | eapply IntMapProofs.Desc_inside; eassumption]).
        assert (inRange i2 (halfRange r1_ false) = false)
          by (eapply rangeDisjoint_inRange_false;
              [rewrite rangeDisjoint_sym; apply halves_disj; assumption | assumption]).
        rewrite (IntMapProofs.Desc_outside HD1_l).
        2:{ eapply inRange_isSubrange_false; eassumption. }
        simpl. exact Hi2. }
      destruct (Hall i1 w1 Hf_i1) as [u1 [Hu1 _]].
      destruct (Hall i2 w2 Hf_i2) as [u2 [Hu2 _]].
      (* f2_ is a Tip: f2_ i = if i =? k2 then Some v2 else None *)
      rewrite Hf2_sem in Hu1. rewrite Hf2_sem in Hu2.
      destruct (N.eqb_spec i1 k2); [| discriminate].
      destruct (N.eqb_spec i2 k2); [| discriminate].
      subst i1 i2.
      (* k2 is in both halves of r1_, contradiction *)
      assert (Hir_k2_l : inRange k2 (halfRange r1_ false) = true).
      { eapply inRange_isSubrange_true; [exact Hsub1_l |].
        eapply IntMapProofs.Desc_inside; [exact HD1_l | exact Hi1]. }
      assert (Hir_k2_r : inRange k2 (halfRange r1_ true) = true).
      { eapply inRange_isSubrange_true; [exact Hsub1_r |].
        eapply IntMapProofs.Desc_inside; [exact HD1_r | exact Hi2]. }
      eapply rangeDisjoint_inRange_false_false.
      { apply halves_disj. exact Hbits1. }
      { exact Hir_k2_l. }
      { exact Hir_k2_r. }

  * (* Bin / Bin *)
    assert (HD1_bin : IntMapProofs.Desc (Bin (rPrefix r1_) (rMask r1_) s1_l s1_r) r1_ f1_)
      by (eapply IntMapProofs.DescBin; eassumption || reflexivity).
    assert (HD2_bin : IntMapProofs.Desc (Bin (rPrefix r2_) (rMask r2_) s2_l s2_r) r2_ f2_)
      by (eapply IntMapProofs.DescBin; eassumption || reflexivity).
    (* Unfold just the top-level isSubmapOfBy application *)
    rewrite /isSubmapOfBy -/isSubmapOfBy.
    rewrite -> !shorter_spec by assumption.
    destruct (N.ltb_spec (rBits r2_) (rBits r1_)).
    + (* s1 has broader range than s2 *)
      split.
      -- discriminate.
      -- intros Hall. exfalso.
         eapply larger_submap_false with (pred := pred)
           (s1 := Bin (rPrefix r1_) (rMask r1_) s1_l s1_r)
           (s2 := Bin (rPrefix r2_) (rMask r2_) s2_l s2_r);
           [eassumption | exact HD1_bin | exact HD2_bin | exact Hall].
    + destruct (N.ltb_spec (rBits r1_) (rBits r2_)).
      -- (* s2 has broader range *)
         match goal with [ |- ((?x && ?y) = true) <-> ?z ] =>
           enough (Htmp : (if x then y else false) = true <-> z)
           by (destruct x; try rewrite andb_true_iff; intuition congruence)
         end.
         match goal with [ |- context [match_ ?x ?y ?z] ] =>
           replace (match_ x y z) with (negb (nomatch x y z))
             by (unfold nomatch, match_; unfoldMethods; rewrite negb_involutive; reflexivity)
         end.
         rewrite if_negb.
         apply nomatch_zero_smaller; try assumption.
         ++ (* r1_ disjoint from r2_ *)
            intro Hdisj.
            rewrite isSubmapOfBy_disjoint_map;
              [ intuition discriminate | eassumption | exact HD1_bin | exact HD2_bin ].
         ++ (* r1_ in the left half of r2_: recurse with whole s1 and s2_l *)
            intros Hsub_l Hnsub_r.
            etransitivity; [eapply IH with (f2 := f2_l)|].
            ** simpl. lia.
            ** exact HD1_bin.
            ** eassumption.
            ** (* Reduce: all keys of f1_ in f2_l <-> all keys of f1_ in f2_ *)
               split; intros Hall i w1 Hfi.
               +++ (* -> : f1_ ⊆ f2_l implies f1_ ⊆ f2_ *)
                   destruct (Hall i w1 Hfi) as [w2 [Hw2 Hp]].
                   exists w2. split; [| assumption].
                   assert (Hf2r_none : f2_r i = None).
                   { eapply IntMapProofs.Desc_outside; [exact HD2_r |].
                     eapply inRange_isSubrange_false; [eassumption |].
                     eapply rangeDisjoint_inRange_false;
                       [apply halves_disj; assumption |].
                     eapply inRange_isSubrange_true; [eassumption |].
                     eapply IntMapProofs.Desc_inside; eassumption. }
                   rewrite Hf2_oro. rewrite Hf2r_none.
                   rewrite IntMapProofs.oro_None_r. exact Hw2.
               +++ (* <- : f1_ ⊆ f2_ implies f1_ ⊆ f2_l *)
                   assert (Hir : inRange i r1_ = true)
                     by (eapply IntMapProofs.Desc_inside; [exact HD1_bin | exact Hfi]).
                   destruct (Hall i w1 Hfi) as [w2 [Hw2 Hp]].
                   assert (Hf2r_none : f2_r i = None).
                   { eapply IntMapProofs.Desc_outside; [exact HD2_r |].
                     eapply inRange_isSubrange_false; [eassumption |].
                     eapply rangeDisjoint_inRange_false;
                       [apply halves_disj; assumption |].
                     eapply inRange_isSubrange_true; [eassumption | exact Hir]. }
                   rewrite Hf2_oro in Hw2. rewrite Hf2r_none in Hw2.
                   rewrite IntMapProofs.oro_None_r in Hw2.
                   exists w2. auto.
         ++ (* r1_ in the right half of r2_ *)
            intros Hnsub_l Hsub_r.
            etransitivity; [eapply IH with (f2 := f2_r)|].
            ** simpl. lia.
            ** exact HD1_bin.
            ** eassumption.
            ** split; intros Hall i w1 Hfi.
               +++ (* -> : f1_ ⊆ f2_r implies f1_ ⊆ f2_ *)
                   destruct (Hall i w1 Hfi) as [w2 [Hw2 Hp]].
                   exists w2. split; [| assumption].
                   assert (Hf2l_none : f2_l i = None).
                   { eapply IntMapProofs.Desc_outside; [exact HD2_l |].
                     eapply inRange_isSubrange_false; [eassumption |].
                     eapply rangeDisjoint_inRange_false;
                       [rewrite rangeDisjoint_sym; apply halves_disj; assumption |].
                     eapply inRange_isSubrange_true; [eassumption |].
                     eapply IntMapProofs.Desc_inside; eassumption. }
                   rewrite Hf2_oro. rewrite Hf2l_none. simpl. exact Hw2.
               +++ (* <- : f1_ ⊆ f2_ implies f1_ ⊆ f2_r *)
                   assert (Hir : inRange i r1_ = true)
                     by (eapply IntMapProofs.Desc_inside; [exact HD1_bin | exact Hfi]).
                   destruct (Hall i w1 Hfi) as [w2 [Hw2 Hp]].
                   assert (Hf2l_none : f2_l i = None).
                   { eapply IntMapProofs.Desc_outside; [exact HD2_l |].
                     eapply inRange_isSubrange_false; [eassumption |].
                     eapply rangeDisjoint_inRange_false;
                       [rewrite rangeDisjoint_sym; apply halves_disj; assumption |].
                     eapply inRange_isSubrange_true; [eassumption | exact Hir]. }
                   rewrite Hf2_oro in Hw2. rewrite Hf2l_none in Hw2. simpl in Hw2.
                   exists w2. auto.

      -- (* same size *)
         unfoldMethods.
         destruct (N.eqb_spec (rPrefix r1_) (rPrefix r2_)).
         ++ (* same prefix => same range, recurse on both halves *)
            replace r2_ with r1_ in * by (apply rPrefix_rBits_range_eq; lia). clear e.
            (* Get the IH equivalences for both halves *)
            assert (IH_l : isSubmapOfBy pred s1_l s2_l = true <->
              (forall i v1, f1_l i = Some v1 -> exists v2, f2_l i = Some v2 /\ pred v1 v2 = true)).
            { eapply IH; [simpl; lia | exact HD1_l | exact HD2_l]. }
            assert (IH_r : isSubmapOfBy pred s1_r s2_r = true <->
              (forall i v1, f1_r i = Some v1 -> exists v2, f2_r i = Some v2 /\ pred v1 v2 = true)).
            { eapply IH; [simpl; lia | exact HD1_r | exact HD2_r]. }
            (* After simpl, the nested isSubmapOfBy calls are expanded.
               Reconstruct: the goal is about the expanded form of
               (rPrefix r1_ =? rPrefix r1_) && (isSubmapOfBy_l && isSubmapOfBy_r).
               Since rPrefix r1_ =? rPrefix r1_ = true (by N.eqb_refl),
               this reduces to isSubmapOfBy_l && isSubmapOfBy_r = true. *)
            (* The simpl'd LHS has the form:
               (N.eqb (rPrefix r1_) (rPrefix r1_) && (X && Y)) = true
               where X = expanded isSubmapOfBy pred s1_l s2_l
               and Y = expanded isSubmapOfBy pred s1_r s2_r.
               Use change to fold back. *)
            change ((isSubmapOfBy pred s1_l s2_l && isSubmapOfBy pred s1_r s2_r) = true <->
              (forall i v1, f1_ i = Some v1 -> exists v2, f2_ i = Some v2 /\ pred v1 v2 = true))
              || (* if change fails, try: *)
              (unfoldMethods; rewrite N.eqb_refl; simpl;
               change ((isSubmapOfBy pred s1_l s2_l && isSubmapOfBy pred s1_r s2_r) = true <->
                 (forall i v1, f1_ i = Some v1 -> exists v2, f2_ i = Some v2 /\ pred v1 v2 = true))).
            rewrite andb_true_iff.
            rewrite IH_l. rewrite IH_r.
            split.
            ** (* forward: both halves -> whole *)
               intros [Hall_l Hall_r] i w1 Hfi.
               rewrite Hf1_oro in Hfi.
               destruct (IntMapProofs.oro_Some _ _ _ _ Hfi) as [Hl | Hr].
               --- (* i in left child *)
                   destruct (Hall_l i w1 Hl) as [w2 [Hw2 Hp]].
                   exists w2. split; [| assumption].
                   rewrite Hf2_oro. rewrite Hw2. reflexivity.
               --- (* i in right child: Hr : f1_r i = Some w1 *)
                   destruct (Hall_r i w1 Hr) as [w2 [Hw2 Hp]].
                   exists w2. split; [| assumption].
                   (* Show f2_l i = None using range disjointness *)
                   assert (Hir_r : inRange i r1_r = true)
                     by (eapply IntMapProofs.Desc_inside; eassumption).
                   assert (Hir_rt : inRange i (halfRange r1_ true) = true)
                     by (eapply inRange_isSubrange_true; [exact Hsub1_r | exact Hir_r]).
                   assert (Hir_lf : inRange i (halfRange r1_ false) = false)
                     by (eapply rangeDisjoint_inRange_false;
                         [rewrite rangeDisjoint_sym; apply halves_disj; exact Hbits1 | exact Hir_rt]).
                   assert (Hf2l_none : f2_l i = None)
                     by (eapply IntMapProofs.Desc_outside; [exact HD2_l |];
                         eapply inRange_isSubrange_false; [exact Hsub2_l | exact Hir_lf]).
                   rewrite Hf2_oro. rewrite Hf2l_none. simpl. exact Hw2.
            ** (* reverse: whole -> both halves *)
               intros Hall.
               split.
               --- (* left half *)
                   intros i w1 Hfi.
                   assert (Hf_i : f1_ i = Some w1)
                     by (rewrite Hf1_oro; rewrite Hfi; reflexivity).
                   destruct (Hall i w1 Hf_i) as [w2 [Hw2 Hp]].
                   assert (Hir_1l : inRange i r1_l = true)
                     by (eapply IntMapProofs.Desc_inside; [exact HD1_l | exact Hfi]).
                   assert (Hir_lf : inRange i (halfRange r1_ false) = true)
                     by (eapply inRange_isSubrange_true; [exact Hsub1_l | exact Hir_1l]).
                   assert (Hir_rt : inRange i (halfRange r1_ true) = false)
                     by (eapply rangeDisjoint_inRange_false;
                         [apply halves_disj; exact Hbits1 | exact Hir_lf]).
                   assert (Hf2r_none : f2_r i = None)
                     by (eapply IntMapProofs.Desc_outside; [exact HD2_r |];
                         eapply inRange_isSubrange_false; [exact Hsub2_r | exact Hir_rt]).
                   rewrite Hf2_oro in Hw2. rewrite Hf2r_none in Hw2.
                   rewrite IntMapProofs.oro_None_r in Hw2.
                   exists w2. auto.
               --- (* right half *)
                   intros i w1 Hfi.
                   assert (Hir_1r : inRange i r1_r = true)
                     by (eapply IntMapProofs.Desc_inside; [exact HD1_r | exact Hfi]).
                   assert (Hir_rt : inRange i (halfRange r1_ true) = true)
                     by (eapply inRange_isSubrange_true; [exact Hsub1_r | exact Hir_1r]).
                   assert (Hir_lf : inRange i (halfRange r1_ false) = false)
                     by (eapply rangeDisjoint_inRange_false;
                         [rewrite rangeDisjoint_sym; apply halves_disj; exact Hbits1 | exact Hir_rt]).
                   assert (Hf1l_none : f1_l i = None)
                     by (eapply IntMapProofs.Desc_outside; [exact HD1_l |];
                         eapply inRange_isSubrange_false; [exact Hsub1_l | exact Hir_lf]).
                   assert (Hf_i : f1_ i = Some w1)
                     by (rewrite Hf1_oro; rewrite Hf1l_none; simpl; exact Hfi).
                   destruct (Hall i w1 Hf_i) as [w2 [Hw2 Hp]].
                   assert (Hf2l_none : f2_l i = None)
                     by (eapply IntMapProofs.Desc_outside; [exact HD2_l |];
                         eapply inRange_isSubrange_false; [exact Hsub2_l | exact Hir_lf]).
                   rewrite Hf2_oro in Hw2. rewrite Hf2l_none in Hw2. simpl in Hw2.
                   exists w2. auto.
         ++ (* different prefix, same size => disjoint *)
            rewrite isSubmapOfBy_disjoint_map;
              [ intuition discriminate
              | apply different_prefix_same_bits_disjoint; try eassumption; lia
              | exact HD1_bin
              | exact HD2_bin ].
Qed.


(** isSubmapOfBy_Desc: Program Fixpoint version, same statement, proved via isSubmapOfBy_Desc1 *)
Program Fixpoint isSubmapOfBy_Desc {a} (f : a -> a -> bool)
  (s1 : IntMap a) r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  IntMapProofs.Desc s1 r1 f1 ->
  IntMapProofs.Desc s2 r2 f2 ->
  isSubmapOfBy f s1 s2 = true <->
  (forall i v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ f v1 v2 = true) := _.
Next Obligation.
  intros. eapply isSubmapOfBy_Desc1; eassumption.
Qed.
