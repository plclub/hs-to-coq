(** Formal counterexample: thm_MaskPow2 is FALSE in the Coq model.

    The theorem claims every mask in a WF IntSet is in powersOf2 = fromList [2^0..2^63].
    But the Coq model uses unbounded N, so we can construct a WF IntSet whose Bin mask
    is 2^100, which is NOT in powersOf2.
*)

Set Warnings "-notation-overridden".
From Coq Require Import ssreflect ssrbool ssrfun.
From Coq Require Import NArith Lia.
Set Bullet Behavior "Strict Subproofs".

Require Import GHC.Base      Proofs.GHC.Base.
Require Import GHC.Num.
Require Import GHC.Enum.
Require Import Data.IntSet.Internal.
Require Import IntSetProperties.
Require Import IntSetProofs.
Require Import IntSetUtil.
Require Import DyadicIntervals.
Require Import HSUtil.
Require Import BitUtils.
Require Import Test.QuickCheck.Property.

Import GHC.Base.

(** ** Step 1: Construct a concrete IntSet with a large mask *)

(* Two keys: 0 and 2^100. These differ at bit 100, so the Bin node
   will have rBits = 101 and mask = rMask (0, 101) = 2^(101-1) = 2^100. *)

Definition big_set : IntSet :=
  Bin 0%N (2^100)%N (Tip 0%N 1%N) (Tip (2^100)%N 1%N).

(** ** Step 2: Prove WF big_set *)

(* Ranges for the tree nodes *)
Definition r_top : range := (0%N, 101%N).
Definition r_left : range := (0%N, 6%N).
Definition r_right : range := (2^94, 6)%N.

(* Characteristic functions defined directly as bitmapInRange *)
Definition f_left : N -> bool := bitmapInRange r_left 1.
Definition f_right : N -> bool := bitmapInRange r_right 1.
Definition f_big : N -> bool := fun i => f_left i || f_right i.

(* isBitMask 1: 0 < 1 /\ 1 < 2^64 *)
Lemma isBitMask_1 : isBitMask 1.
Proof. unfold isBitMask, WIDTH. lia. Qed.

(* Desc for left Tip: Tip 0 1 with range (0, 6) *)
Lemma Desc_left : Desc (Tip 0%N 1%N) r_left f_left.
Proof.
  apply DescTip.
  - (* p = rPrefix r_left *) reflexivity.
  - (* rBits r_left = N.log2 WIDTH *) reflexivity.
  - (* forall i, f_left i = bitmapInRange r_left 1 i *) intro i. reflexivity.
  - (* isBitMask 1 *) exact isBitMask_1.
Qed.

(* Desc for right Tip: Tip (2^100) 1 with range (2^94, 6) *)
Lemma Desc_right : Desc (Tip (2^100)%N 1%N) r_right f_right.
Proof.
  apply DescTip.
  - (* p = rPrefix r_right = N.shiftl (2^94) 6 = 2^100 *)
    unfold r_right. simpl. reflexivity.
  - (* rBits r_right = N.log2 WIDTH *) reflexivity.
  - (* forall i, f_right i = bitmapInRange r_right 1 i *) intro i. reflexivity.
  - (* isBitMask 1 *) exact isBitMask_1.
Qed.

(* isSubrange checks *)
Lemma isSubrange_left : isSubrange r_left (halfRange r_top false) = true.
Proof. native_compute. reflexivity. Qed.

Lemma isSubrange_right : isSubrange r_right (halfRange r_top true) = true.
Proof. native_compute. reflexivity. Qed.

(* Full Desc for the Bin node *)
Lemma Desc_big : Desc big_set r_top f_big.
Proof.
  unfold big_set.
  eapply DescBin.
  - exact Desc_left.
  - exact Desc_right.
  - (* 0 < rBits r_top = 101 *) unfold r_top; simpl; lia.
  - exact isSubrange_left.
  - exact isSubrange_right.
  - (* p = rPrefix r_top = 0 *) reflexivity.
  - (* msk = rMask r_top = 2^100 *) reflexivity.
  - (* f_big = f_left || f_right *) intro i. reflexivity.
Qed.

Lemma WF_big_set : WF big_set.
Proof.
  exists f_big. apply (DescSem _ r_top). exact Desc_big.
Qed.

(** ** Step 3: Show prop_MaskPow2 big_set = false *)

(* 2^100 is not in [2^0, ..., 2^63] because 100 > 63 and N.pow 2 is injective *)
Lemma pow2_100_not_in_powers :
  ~ In (2^100)%N
    (Coq.Lists.List.map (fun i : N => (2^i)%N)
       (GHC.Enum.enumFromTo 0%N 63%N)).
Proof.
  intro HIn.
  apply Coq.Lists.List.in_map_iff in HIn.
  destruct HIn as [x [Hpow Hin]].
  (* 2^x = 2^100 implies x = 100 *)
  assert (Hx : x = 100%N) by (apply N.pow_inj_r with (a := 2%N); lia).
  subst x.
  (* 100 is NOT in enumFromTo 0 63 = [0..62]. Contradiction. *)
  (* enumFromTo for N produces map N.of_nat (seq 0 63) = [0,..,62] *)
  (* In reduces to a disjunction of equalities k = 100, all false. *)
  revert Hin.
  vm_compute.
  intuition congruence.
Qed.

Lemma member_pow2_100_powersOf2_false : member (2^100)%N powersOf2 = false.
Proof.
  unfold powersOf2.
  rewrite fromList_member.
  apply negbTE. apply/negP. move/elemP.
  (* flat_map (fun i => [2^i]) xs = map (fun i => 2^i) xs *)
  rewrite flat_map_cons_f.
  exact pow2_100_not_in_powers.
Qed.

Lemma prop_MaskPow2_big_set_false : prop_MaskPow2 big_set = false.
Proof.
  unfold big_set.
  (* prop_MaskPow2 (Bin 0 (2^100) (Tip 0 1) (Tip (2^100) 1))
     = member (2^100) powersOf2 && prop_MaskPow2 (Tip 0 1) && prop_MaskPow2 (Tip (2^100) 1)
     = member (2^100) powersOf2 && true && true *)
  change (prop_MaskPow2 (Bin 0%N (2^100)%N (Tip 0%N 1%N) (Tip (2^100)%N 1%N)))
    with (member (2^100)%N powersOf2 && (prop_MaskPow2 (Tip 0%N 1%N) && prop_MaskPow2 (Tip (2^100)%N 1%N))).
  rewrite member_pow2_100_powersOf2_false. reflexivity.
Qed.

(** ** Step 4: The final theorem -- thm_MaskPow2 is FALSE *)

Theorem thm_MaskPow2_false : ~ (toProp prop_MaskPow2).
Proof.
  (* toProp (IntSet -> bool) unfolds via Testable_fn to:
     forall s, WF s -> is_true (prop_MaskPow2 s) *)
  intro H.
  (* H : forall s, WF s -> is_true (prop_MaskPow2 s) *)
  have := H big_set WF_big_set.
  rewrite prop_MaskPow2_big_set_false.
  done.
Qed.

Print Assumptions thm_MaskPow2_false.
