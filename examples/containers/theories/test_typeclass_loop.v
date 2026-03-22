(** Investigation of the typeclass resolution infinite loop that occurs
    when [Require SetProofs] is added to IntSetPropertyProofs.v.

    ROOT CAUSE: SetProofs exports [Global Instance]s parameterized over any
    type [e] with Eq_/Ord/EqLaws/OrdLaws constraints:
      Eq_ (WFSet e), Ord (WFSet e), EqLaws (WFSet e), OrdLaws (WFSet e),
      Semigroup (WFSet e), Monoid (WFSet e)
    When Coq's typeclass resolution tries to solve [Eq_ ?X], it can try
    [Eq_Set_WF] which requires [Ord e], triggering [Ord_Set_WF] which
    requires [Eq_ e], which loops back to [Eq_Set_WF] with WFSet nested
    deeper each time (WFSet (WFSet (WFSet ...))). This diverges.

    FIX: Use [Set Typeclasses Iterative Deepening] with a finite depth
    bound before [Require SetProofs]. This makes the nested WFSet search
    terminate at the depth limit instead of diverging.
*)

(******************************************************************************)
(** Imports — exact copy from IntSetPropertyProofs.v lines 1–41 *)
(******************************************************************************)

(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

(* SSReflect *)
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype.
Set Bullet Behavior "Strict Subproofs".

(* Sortedness *)
Require Import Coq.Sorting.Sorted.

(* Basic Haskell libraries *)
Require Import GHC.Base      Proofs.GHC.Base.
Require Import GHC.List      Proofs.GHC.List.
Require Import GHC.Enum      Proofs.GHC.Enum.
Require Import Data.Foldable Proofs.Data.Foldable.
Require Import Data.OldList  Proofs.Data.OldList.
Require Import Data.Bits     Proofs.Data.Bits.Popcount.

(* Quickcheck *)
Require Import Test.QuickCheck.Property.

(* IntSet library *)
Require Import Data.IntSet.Internal.

(* IntSet proofs *)
Require Import IntSetProperties.
Require Import DyadicIntervals.
Require Import IntSetProofs.

(* Bit manipulation *)
Require Import BitUtils.

(* Working with Haskell *)
Require Import OrdTactic.
Require Import HSUtil IntSetUtil.
Require Import SortedUtil.

(* Set library — needed for toSet definition *)
Require Import Data.Set.Internal.

Notation list    := Coq.Init.Datatypes.list.
Notation seq     := Coq.Lists.List.seq.
Notation reflect := ssrbool.reflect.

(* Sanity check: everything compiles before SetProofs *)
Definition test_before_setproofs := 0.

(******************************************************************************)
(** Phase 1: Import SetProofs with typeclass depth limits *)
(******************************************************************************)

(* The fix: iterative deepening prevents the infinite WFSet nesting loop.
   Depth 3 is sufficient — real instances never need WFSet-nested resolution. *)
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 3.

Require SetProofs.

(* Restore normal resolution for subsequent proofs *)
Unset Typeclasses Iterative Deepening.

(* Sanity check: everything compiles after SetProofs *)
Definition test_after_setproofs := 1.

(******************************************************************************)
(** Phase 2: Verify key lemmas are accessible *)
(******************************************************************************)

Check isSubsetOf_member.
Check @SetProofs.isSubsetOf_spec.
Check @SetProofs.fromList_Desc.

(******************************************************************************)
(** Phase 3: Bridge lemmas connecting IntSet and Set_ via toSet *)
(******************************************************************************)

(* toSet = fromList . toList, converting IntSet to Set_ N.
   We need:
   1. toSet preserves well-formedness (gives Bounded ... None None)
   2. sem (toSet s) k = IntSet.member k s  (semantic bridge) *)

(* Helper: List.elem for N is equivalent to Coq's In when Eq is ==.
   We prove this by induction for EqExact types. *)
Lemma List_elem_In : forall (k : N) (xs : Coq.Init.Datatypes.list N),
  GHC.List.elem k xs = true <-> List.In k xs.
Proof.
  intros k xs. induction xs as [|x xs' IH].
  - simpl. split; intro H; inversion H.
  - simpl. rewrite orb_true_iff.
    split.
    + intros [Heq | Hin].
      * left. symmetry. apply (reflect_iff _ _ (Eq_eq k x)). exact Heq.
      * right. apply IH. exact Hin.
    + intros [Heq | Hin].
      * left. apply (reflect_iff _ _ (Eq_eq k x)). symmetry. exact Heq.
      * right. apply IH. exact Hin.
Qed.

(* Bridge: toSet produces a WF (= Bounded ... None None) set,
   and its semantics match IntSet's member function. *)
Lemma toSet_Bounded_sem : forall (s : IntSet),
  IntSetProofs.WF s ->
  exists s', s' = toSet s /\
    SetProofs.Bounded s' None None /\
    (forall k, SetProofs.sem s' k = Data.IntSet.Internal.member k s).
Proof.
  intros s [f Hsem].
  (* toSet s = fromList (toList s) *)
  unfold toSet, op_z2218U__.
  (* fromList_Desc gives Desc' (fromList (toList s)) None None (fun i => List.elem i (toList s)) *)
  pose proof (SetProofs.fromList_Desc (Data.IntSet.Internal.toList s)) as Hdesc.
  (* Unfold the CPS encoding of Desc' *)
  unfold SetProofs.Desc' in Hdesc.
  (* Apply the continuation to extract Bounded and sem *)
  apply Hdesc. clear Hdesc.
  intros s' Hbounded _ Hsem_eq.
  exists s'. split; [reflexivity|]. split; [exact Hbounded|].
  intros k.
  rewrite Hsem_eq.
  (* Now: List.elem k (toList s) = member k s *)
  (* From IntSetProofs: member_Sem gives member k s = f k *)
  (* From IntSetProofs: toList_In gives f k = true <-> In k (toList s) *)
  (* Goal: List.elem k (toList s) = member k s
     Chain: member k s = f k  (member_Sem)
            f k = true <-> In k (toList s)  (toList_In)
            elem k (toList s) = true <-> In k (toList s)  (List_elem_In)

     Strategy: prove bool equality via chain of iffs *)
  apply Bool.eq_iff_eq_true.
  pose proof (IntSetProofs.member_Sem Hsem (i := k)) as Hmem.
  pose proof (IntSetProofs.toList_In _ _ Hsem k) as Hin.
  split; intro H.
  - apply List_elem_In in H. apply Hin in H. rewrite Hmem. exact H.
  - rewrite Hmem in H. apply Hin in H. apply List_elem_In. exact H.
Qed.

(******************************************************************************)
(** Phase 4: Prove thm_isSubsetOf *)
(******************************************************************************)

Theorem thm_isSubsetOf : toProp prop_isSubsetOf.
Proof.
  rewrite /prop_isSubsetOf /= => s1 WF1 s2 WF2.
  (* Goal: IntSet.isSubsetOf s1 s2 == Set.isSubsetOf (toSet s1) (toSet s2) *)
  apply/Eq_eq.
  (* Goal: IntSet.isSubsetOf s1 s2 = Set.isSubsetOf (toSet s1) (toSet s2) *)
  apply Bool.eq_iff_eq_true.
  (* Get Set_ bounded representations for toSet s1 and toSet s2 *)
  destruct (toSet_Bounded_sem s1 WF1) as [ts1 [Ets1 [Hb1 Hsem1]]].
  destruct (toSet_Bounded_sem s2 WF2) as [ts2 [Ets2 [Hb2 Hsem2]]].
  subst ts1 ts2.
  (* LHS: IntSet.isSubsetOf s1 s2 = true <-> forall k, member k s1 -> member k s2 *)
  (* RHS: Set.isSubsetOf (toSet s1) (toSet s2) = true <-> forall i, sem (toSet s1) i -> sem (toSet s2) i *)
  split; intro H.
  - apply (proj2 (SetProofs.isSubsetOf_spec _ _ _ _ Hb1 Hb2)).
    assert (Hmem : forall k, Data.IntSet.Internal.member k s1 = true ->
                             Data.IntSet.Internal.member k s2 = true).
    { apply (proj1 (isSubsetOf_member s1 s2 WF1 WF2)). exact H. }
    intros i Hi. rewrite Hsem2. apply Hmem. rewrite <- Hsem1. exact Hi.
  - apply (proj2 (isSubsetOf_member s1 s2 WF1 WF2)).
    assert (Hsem_sub : forall i, SetProofs.sem (toSet s1) i = true ->
                                 SetProofs.sem (toSet s2) i = true).
    { apply (proj1 (SetProofs.isSubsetOf_spec _ _ _ _ Hb1 Hb2)). exact H. }
    intros k Hk. rewrite <- Hsem2. apply Hsem_sub. rewrite Hsem1. exact Hk.
Qed.

(******************************************************************************)
(** Summary *)
(******************************************************************************)

(* The typeclass loop is caused by SetProofs exporting Global Instances:
     Eq_ (WFSet e), Ord (WFSet e), EqLaws (WFSet e), OrdLaws (WFSet e), ...
   These create an infinite search cycle: resolving Eq_ ?X can try WFSet e
   which requires Ord e, which tries Ord (WFSet e'), which requires Eq_ e',
   which tries WFSet e'', ad infinitum.

   FIX: Set Typeclasses Iterative Deepening + Set Typeclasses Depth 3
   before Require SetProofs. This bounds the search depth so the nested
   WFSet chain terminates at depth 3 instead of diverging.

   thm_isProperSubsetOf is NOT attempted here because SetProofs has no
   isProperSubsetOf_spec lemma. It would need a similar bridge approach
   once such a spec is proven in SetProofs.v. *)
