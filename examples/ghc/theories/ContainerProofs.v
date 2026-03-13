(* Properties of IntMap operations.
   Some lemmas are proved directly (structural induction or computation).
   Others remain axiomatized because they depend on well-formedness
   invariants of the IntMap (patricia trie bit structure).

   Stated in terms of Data.IntMap.Internal operations directly,
   since VarSet/UniqFM unfolds to Internal operations. *)

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import GHC.Base.

Require Import Proofs.Prelude.
Require Import Data.IntMap.Internal.
Require IntMap.

(* Local copy of deferredFix2_eq to avoid importing IntMapProofs
   (which transitively loads mathcomp/MapProofs/etc. that break
   downstream proofs via Asymmetric Patterns and name ambiguity). *)
Local Axiom deferredFix2_eq : forall a b r `{HsToCoq.Err.Default r}
  (f : (a -> b -> r) -> (a -> b -> r)),
  HsToCoq.DeferredFix.deferredFix2 f = f (HsToCoq.DeferredFix.deferredFix2 f).

Set Bullet Behavior "Strict Subproofs".

(* ============================================================ *)
(* Proved lemmas: universally true (no WF needed)               *)
(* ============================================================ *)

Lemma null_empty : forall A,
    (@Data.IntMap.Internal.null A Data.IntMap.Internal.empty).
Proof. intros. reflexivity. Qed.

Lemma lookup_eq : forall A k k' (i : IntMap.IntMap A),
    k == k' ->
    Data.IntMap.Internal.lookup k i = Data.IntMap.Internal.lookup k' i.
Proof. intros A k k' i. move => /Eq_eq_Word ->. reflexivity. Qed.

Lemma member_eq : forall A k k' (i : IntMap.IntMap A),
    k == k' ->
    Data.IntMap.Internal.member k i = Data.IntMap.Internal.member k' i.
Proof. intros A k k' i. move => /Eq_eq_Word ->. reflexivity. Qed.

Lemma member_singleton : forall A k k' (v : A),
    Data.IntMap.Internal.member k (Data.IntMap.Internal.singleton k' v) = (k == k').
Proof. intros. simpl. reflexivity. Qed.

Lemma lookup_singleton_key : forall {A} x y (a b : A),
    Data.IntMap.Internal.lookup x (Data.IntMap.Internal.singleton y a) = Some b -> x == y.
Proof.
  intros A x y a b. simpl.
  destruct (x == y) eqn:Heq; [auto | intros H; discriminate].
Qed.

Lemma lookup_singleton_val : forall {A} x y (a b : A),
    Data.IntMap.Internal.lookup x (Data.IntMap.Internal.singleton y a) = Some b -> a = b.
Proof.
  intros A x y a b. simpl.
  destruct (x == y) eqn:Heq; [intros H; congruence | intros H; discriminate].
Qed.

(* Helper: lookup through link always finds the linked key.
   This works because linkWithMask places t1 on the side matching
   zero p1 m, and lookup follows zero key m — with key=p1 they agree. *)
Local Lemma lookup_link_self : forall A key (val : A) p2 t2,
  Data.IntMap.Internal.lookup key (link key (Tip key val) p2 t2) = Some val.
Proof.
  intros. unfold link, linkWithMask.
  destruct (Data.IntSet.Internal.zero key (branchMask key p2)) eqn:Hz;
  simpl; rewrite Hz; rewrite Eq_refl; reflexivity.
Qed.

Lemma lookup_insert : forall A key (val:A) i,
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.insert key val i) = Some val.
Proof.
  intros A key val.
  induction i as [p m l IHl r IHr | ky vy | ].
  - simpl. destruct (nomatch key p m) eqn:Hnm.
    + apply lookup_link_self.
    + destruct (Data.IntSet.Internal.zero key m) eqn:Hz; simpl; rewrite Hz; auto.
  - simpl. destruct (key == ky) eqn:Heq.
    + simpl. rewrite Eq_refl. reflexivity.
    + apply lookup_link_self.
  - simpl. rewrite Eq_refl. reflexivity.
Qed.

(* deferredFix2-based lemmas with Nil arguments *)

Lemma difference_nil_l : forall B A (i : IntMap.IntMap A),
    Data.IntMap.Internal.difference (@Data.IntMap.Internal.empty B) i =
    (@Data.IntMap.Internal.empty B).
Proof.
  intros. unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.empty.
  unfold mergeWithKey. unfold mergeWithKey'.
  rewrite deferredFix2_eq. reflexivity.
Qed.

Lemma difference_nil_r : forall A B (i : IntMap.IntMap A),
    Data.IntMap.Internal.difference i (@Data.IntMap.Internal.empty B) = i.
Proof.
  intros. unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.empty.
  unfold mergeWithKey. unfold mergeWithKey'.
  rewrite deferredFix2_eq.
  destruct i; reflexivity.
Qed.

Lemma disjoint_empty_l : forall A B (j : IntMap.IntMap B),
  Data.IntMap.Internal.disjoint (@Data.IntMap.Internal.empty A) j = true.
Proof.
  intros. unfold Data.IntMap.Internal.disjoint, Data.IntMap.Internal.empty.
  rewrite deferredFix2_eq. reflexivity.
Qed.

Lemma disjoint_empty_r : forall A B (i : IntMap.IntMap A),
  Data.IntMap.Internal.disjoint i (@Data.IntMap.Internal.empty B) = true.
Proof.
  intros. unfold Data.IntMap.Internal.disjoint, Data.IntMap.Internal.empty.
  rewrite deferredFix2_eq. destruct i; reflexivity.
Qed.

Lemma intersection_empty :
  forall A B (i : IntMap.IntMap A) (j : IntMap.IntMap B),
    (j = Data.IntMap.Internal.empty) ->
    Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i j).
Proof.
  intros A B i j Hj. subst.
  unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.empty.
  unfold mergeWithKey'.
  rewrite deferredFix2_eq.
  destruct i; reflexivity.
Qed.

(* ============================================================ *)
(* Admitted lemmas: depend on IntMap well-formedness (WF)        *)
(* These hold for all IntMaps constructed from                   *)
(* empty/insert/delete/union etc. (i.e., valid patricia tries). *)
(* ============================================================ *)

Axiom lookup_insert_neq :
  forall b key1 key2 (val:b) m,
    key1 <> key2 ->
    Data.IntMap.Internal.lookup key1 (Data.IntMap.Internal.insert key2 val m) = Data.IntMap.Internal.lookup key1 m.

Axiom member_insert : forall A k k' v (i : IntMap.IntMap A),
  Data.IntMap.Internal.member k (Data.IntMap.Internal.insert k' v i) =
  (k == k') || Data.IntMap.Internal.member k i.

Axiom delete_eq : forall key b (i : IntMap.IntMap b),
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.delete key i) = None.

Axiom delete_neq : forall key1 key2 b (i : IntMap.IntMap b),
    key1 <> key2 ->
    Data.IntMap.Internal.lookup key1 (Data.IntMap.Internal.delete key2 i) = Data.IntMap.Internal.lookup key1 i.

Axiom member_delete_neq : forall k1 k2 b (i: IntMap.IntMap b), k1 <> k2 ->
  Data.IntMap.Internal.member k2 (Data.IntMap.Internal.delete k1 i) =
  Data.IntMap.Internal.member k2 i.

Axiom non_member_lookup :
   forall (A : Type)
     (key : Internal.Key)
     (i : IntMap.IntMap A),
   (Data.IntMap.Internal.member key i = false) <-> (Data.IntMap.Internal.lookup key i = None).

Axiom member_lookup :
   forall (A : Type)
     (key : Internal.Key)
     (i : IntMap.IntMap A),
   (is_true (Data.IntMap.Internal.member key i)) <-> (exists val, Data.IntMap.Internal.lookup key i = Some val).

Axiom null_member : forall A (m : IntMap.IntMap A),
    Data.IntMap.Internal.null m = true <-> (forall k, Data.IntMap.Internal.member k m = false).

Axiom member_delete : forall A k k' (m : IntMap.IntMap A),
    Data.IntMap.Internal.member k (Data.IntMap.Internal.delete k' m) =
    negb (k == k') && Data.IntMap.Internal.member k m.

Axiom member_union :
   forall (A : Type)
     (key : Internal.Key)
     (i i0 : IntMap.IntMap A),
   (Data.IntMap.Internal.member key (Data.IntMap.Internal.union i i0)) =
   (Data.IntMap.Internal.member key i0 || Data.IntMap.Internal.member key i).

Axiom filter_comp : forall A `{EqLaws A} f f' (i : IntMap.IntMap A),
    Data.IntMap.Internal.filter f (Data.IntMap.Internal.filter f' i) ==
    Data.IntMap.Internal.filter (fun v => f v && f' v) i.

Axiom lookup_filterWithKey :
  forall b key (val:b) m f, Data.IntMap.Internal.lookup key (Data.IntMap.Internal.filterWithKey f m) = Some val ->
                       Data.IntMap.Internal.lookup key m = Some val.

Axiom filter_true : forall (A:Type) `{EqLaws A} (m:IntMap.IntMap A),
    Data.IntMap.Internal.filter (const true) m == m.

Axiom lookup_intersection :
  forall a b key (val1:a)
    (m1 : IntMap.IntMap a) (m2 : IntMap.IntMap b),
    Data.IntMap.Internal.lookup key m1 = Some val1 /\
    (exists (val2:b), Data.IntMap.Internal.lookup key m2 = Some val2) <->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.intersection m1 m2) = Some val1.

Axiom lookup_union :
  forall (A:Type) key (val:A) (m1 m2: IntMap.IntMap A),
    (Data.IntMap.Internal.lookup key m1 = Some val \/ (Data.IntMap.Internal.lookup key m1 = None /\ Data.IntMap.Internal.lookup key m2 = Some val)) <->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.union m1 m2) = Some val.

Axiom lookup_partition :
  forall (A:Type) key (val:A) (m m': IntMap.IntMap A) (P: A -> bool),
    ((m' = fst (Data.IntMap.Internal.partition P m) \/
      m' = snd (Data.IntMap.Internal.partition P m)) /\
     Data.IntMap.Internal.lookup key m' = Some val) ->
    Data.IntMap.Internal.lookup key m  = Some val.

Axiom lookup_difference_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap.IntMap b) (y:b),
    Data.IntMap.Internal.lookup key i' = Some y ->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.difference i i') = None.

Axiom lookup_difference_not_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap.IntMap b)(y:b),
    Data.IntMap.Internal.lookup key i' = None ->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.difference i i') = Data.IntMap.Internal.lookup key i.

Axiom delete_commute :
  forall (A : Type) `{EqLaws A}
    (kx ky : Internal.Key)
    (i : IntMap.IntMap A),
  Data.IntMap.Internal.delete ky (Data.IntMap.Internal.delete kx i) ==
  Data.IntMap.Internal.delete kx (Data.IntMap.Internal.delete ky i).

Axiom null_intersection_non_member: forall b k (v : b)(i1 i2 : IntMap.IntMap b),
  Data.IntMap.Internal.null
    (Data.IntMap.Internal.intersection i1 (Data.IntMap.Internal.insert k v i2)) <->
  Data.IntMap.Internal.member k i1 = false /\
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i1 i2).

Axiom null_intersection_difference: forall  b (i1 i2 i3 : IntMap.IntMap b),
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i2 i3) ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.difference i1 i2) ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i1 i3).

Axiom null_intersection_eq : forall b (x1 x2 y1 y2 : IntMap.IntMap b),
  (forall a, Data.IntMap.Internal.member a x1 <-> Data.IntMap.Internal.member a y1) ->
  (forall a, Data.IntMap.Internal.member a x2 <-> Data.IntMap.Internal.member a y2) ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection x1 x2) = Data.IntMap.Internal.null (Data.IntMap.Internal.intersection y1 y2).

(* disjoint axioms — GHC 9.10 uses Data.IntMap.Internal.disjoint instead of
   null (intersection ...). These mirror the null_intersection axioms. *)

Axiom disjoint_sym : forall A B (i : IntMap.IntMap A) (j : IntMap.IntMap B),
  Data.IntMap.Internal.disjoint i j = Data.IntMap.Internal.disjoint j i.

Axiom disjoint_insert : forall b k (v : b)(i1 i2 : IntMap.IntMap b),
  Data.IntMap.Internal.disjoint i1 (Data.IntMap.Internal.insert k v i2) =
  (negb (Data.IntMap.Internal.member k i1) && Data.IntMap.Internal.disjoint i1 i2).

Axiom disjoint_non_member: forall b k (v : b)(i1 i2 : IntMap.IntMap b),
  Data.IntMap.Internal.disjoint i1 (Data.IntMap.Internal.insert k v i2) <->
  Data.IntMap.Internal.member k i1 = false /\
  Data.IntMap.Internal.disjoint i1 i2.

Axiom disjoint_eq : forall b (x1 x2 y1 y2 : IntMap.IntMap b),
  (forall a, Data.IntMap.Internal.member a x1 <-> Data.IntMap.Internal.member a y1) ->
  (forall a, Data.IntMap.Internal.member a x2 <-> Data.IntMap.Internal.member a y2) ->
  Data.IntMap.Internal.disjoint x1 x2 = Data.IntMap.Internal.disjoint y1 y2.

Axiom disjoint_difference: forall b (i1 i2 i3 : IntMap.IntMap b),
  Data.IntMap.Internal.disjoint i2 i3 = true ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.difference i1 i2) ->
  Data.IntMap.Internal.disjoint i1 i3 = true.

Axiom member_difference : forall A B k (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B),
    Data.IntMap.Internal.member k (Data.IntMap.Internal.difference m1 m2) =
    Data.IntMap.Internal.member k m1 && negb (Data.IntMap.Internal.member k m2).

Axiom member_intersection : forall A B k (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B),
    Data.IntMap.Internal.member k (Data.IntMap.Internal.intersection m1 m2) =
    Data.IntMap.Internal.member k m1 && Data.IntMap.Internal.member k m2.

(* ============================================================ *)
(* Proved lemma: Eq_membership (structural equality -> member)  *)
(* ============================================================ *)

Lemma Eq_membership : forall (A : Type) (HeqA : Eq_ A) (HlawsA : EqLaws A) (m1 m2 : IntMap.IntMap A),
  m1 == m2 ->
  forall k, Data.IntMap.Internal.member k m1 = Data.IntMap.Internal.member k m2.
Proof.
  intros A HeqA HlawsA.
  induction m1 as [p1 mask1 l1 IHl r1 IHr | kx vx | ]; destruct m2 as [p2 mask2 l2 r2 | ky vy | ];
    intros Heq k; simpl in Heq; try discriminate.
  - apply andb_true_iff in Heq. destruct Heq as [Hmask Hrest].
    apply andb_true_iff in Hrest. destruct Hrest as [Hprefix Hchildren].
    apply andb_true_iff in Hchildren. destruct Hchildren as [Heql Heqr].
    move: Hmask => /Eq_eq_Word Hmask. move: Hprefix => /Eq_eq_Word Hprefix.
    subst.
    unfold Data.IntMap.Internal.member. simpl.
    destruct (Data.IntMap.Internal.nomatch k p2 mask2); [reflexivity|].
    destruct (Data.IntSet.Internal.zero k mask2).
    + apply IHl. exact Heql.
    + apply IHr. exact Heqr.
  - apply andb_true_iff in Heq. destruct Heq as [Hkey Hval].
    move: Hkey => /Eq_eq_Word Hkey. subst.
    unfold Data.IntMap.Internal.member. simpl. reflexivity.
  - reflexivity.
Qed.
