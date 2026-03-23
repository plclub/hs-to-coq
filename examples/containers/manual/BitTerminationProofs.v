(**

This file contains the justification for the bit-wise recursion in [IntSet] and [IntMap].
This needs to be defined before these modules are used, unfortunately.

There is some duplication between the stuff here and the [IntSetTheories], which
of course imports [IntSet].
*)

Require Import Coq.NArith.NArith.
Require Import Coq.Bool.Bool.
Require Import CTZ.
Require Import Lia.

Lemma lxor_pow2_clearbit:
  forall a i,
  N.testbit a i = true ->
  N.lxor a (2 ^ i)%N = N.clearbit a i.
Proof.
  intros.
  apply N.bits_inj. intro j.
  rewrite N.lxor_spec, N.pow2_bits_eqb, N.clearbit_eqb.
  destruct (N.eqb_spec i j).
  * subst.
    destruct (N.testbit _ _) eqn:?; try reflexivity; congruence.
  * destruct (N.testbit _ _) eqn:?; try reflexivity.
Qed.

Lemma lxor_lowestBitMask:
  forall bm,
  (bm <> 0)%N ->
  N.lxor bm (2^(N_ctz bm))%N = N.clearbit bm (N_ctz bm).
Proof.
  intros.
  apply lxor_pow2_clearbit.
  apply N_bit_ctz.
  lia.
Qed.


Lemma N_bits_impl_le:
  forall a b,
  (forall i, N.testbit a i = true -> N.testbit b i = true) ->
  (a <= b)%N.
Proof.
  intros a b H.
  assert (Heq : N.land a b = a).
  { apply N.bits_inj. intro n.
    rewrite N.land_spec.
    destruct (N.testbit a n) eqn:Ha.
    - rewrite (H _ Ha). reflexivity.
    - rewrite andb_false_l. reflexivity. }
  rewrite <- Heq.
  apply N.land_le_r.
Qed.

Lemma clearbit_le:
  forall a i,
  (N.clearbit a i <= a)%N.
Proof.
  intros.
  apply N_bits_impl_le; intros j H.
  rewrite N.clearbit_eqb in H.
  rewrite andb_true_iff in *.
  intuition.
Qed.

Lemma clearbit_lt:
  forall a i,
  N.testbit a i = true ->
  (N.clearbit a i < a)%N.
Proof.
  intros.
  apply N.le_neq; split.
  * apply clearbit_le.
  * intro.
    apply N.bits_inj_iff in H0. specialize (H0 i).
    rewrite N.clearbit_eqb in H0.
    rewrite N.eqb_refl in H0.
    simpl negb in H0.
    rewrite andb_false_r in H0.
    congruence.
Qed.

Lemma N2nat_inj_lt:
  forall a b : N,
  (N.to_nat a < N.to_nat b) <-> (a < b)%N.
Proof.
  intros.
  lia.
Qed.

(* This lemma is tailored to what we actually have to prove -- up to unfolding. *)
Lemma foldlBits_proof:
  forall a,
  N.eqb a 0 = false ->
  (N.to_nat (N.lxor a (2 ^ CTZ.N_ctz a)) < N.to_nat a).
Proof.
  intros.
  rewrite N.eqb_neq in H.
  apply N2nat_inj_lt.
  rewrite lxor_lowestBitMask by assumption.
  apply clearbit_lt.
  apply CTZ.N_bit_ctz.
  lia.
Qed.

Require Coq.Program.Tactics.

Ltac termination_foldl:=
  Coq.Program.Tactics.program_simpl;
  apply foldlBits_proof;
  assumption.
