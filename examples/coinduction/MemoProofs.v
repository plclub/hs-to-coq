Require Import Coq.NArith.BinNat.
Require Import GHC.Base.
Require Import Psatz.

Require Import Memo.

Set Bullet Behavior "Strict Subproofs".
Open Scope N_scope.

Lemma lookupTrie_eq {a} (t : NatTrie a) n:
  lookupTrie t n =  match t with
    | TrieNode here div2 minus1div2 =>
        if Sumbool.sumbool_of_bool (n =? 0)         then here else
        if Sumbool.sumbool_of_bool (GHC.Real.odd n) then lookupTrie minus1div2 (GHC.Real.div n 2)
                                                    else lookupTrie div2 (GHC.Real.div n 2)
    end.
Proof.
  intros.
  unfold lookupTrie at 1, lookupTrie_func at 1.
  destruct t.
  lazymatch goal with 
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs => 
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.


Program Fixpoint
  memo_spec a (f : N -> a) x {measure x (N.lt)}:
  lookupTrie (mkTrie f) x = f x
  := _.
Next Obligation.
  rewrite lookupTrie_eq.
  simpl.
  repeat destruct (Sumbool.sumbool_of_bool).
  * rewrite N.eqb_eq in *; subst.
    reflexivity.
  * rewrite N.eqb_neq in *.
    rewrite memo_spec by (apply N.div_lt; lia).
    unfold op_z2218U__.
    f_equal.
    unfold Real.odd, Real.even, Real.rem, Real.instance__Integral_Word, fromInteger, Num_Word__ in e0.
    simpl Z.to_N in e0.
    rewrite negb_true_iff in e0.
    apply N.eqb_neq in e0.
    pose proof (N.mod_upper_bound x 2).
    pose proof (N.div_mod' x 2).
    lia.
  * rewrite N.eqb_neq in *.
    rewrite memo_spec by (apply N.div_lt; lia).
    unfold op_z2218U__.
    f_equal.
    unfold Real.odd, Real.even, Real.rem, Real.instance__Integral_Word, fromInteger, Num_Word__ in e0.
    simpl Z.to_N in e0.
    rewrite negb_false_iff in e0.
    apply N.eqb_eq in e0.
    pose proof (N.mod_upper_bound x 2).
    pose proof (N.div_mod' x 2).
    lia.
Qed.
Next Obligation.
  apply Wf.measure_wf.
  apply Coq.NArith.BinNat.N.lt_wf_0.
Qed.

Lemma cachedFib_slowFib:
  forall n, cachedFib n = slowFib n.
Proof. apply memo_spec. Qed.

Time Eval vm_compute in slowFib 25. (* Finished transaction in 2.248 secs *)
Time Eval vm_compute in slowFib 25. (* Finished transaction in 2.233 secs *)
Time Eval vm_compute in cachedFib 25. (* Finished transaction in 2.203 secs *)
Time Eval vm_compute in cachedFib 25. (* Finished transaction in 0. secs *)
Time Eval vm_compute in cachedFib 26. (* Finished transaction in 3.579 secs *)
Time Eval vm_compute in cachedFib 26. (* Finished transaction in 0. secs *)


(* As a digression let us do some actual coinductive proof, and not just
inductive proofs over coinductive datatypes and functions, and look at mapTrie. *)

(* We cannot just prove

CoFixpoint mapTrie_mk_Trie a b (f : a -> b) (g : N -> a):
  mapTrie f (mkTrie g) = mkTrie (f ∘ g).

because equality on coinductive values isn't itself a coinductive
thing. So we have to define co-inductive equality first:
*)

CoInductive EqTrie {a} : NatTrie a -> NatTrie a -> Prop :=
  eqTrie : forall x x' div2 div2' minus1div2 minus1div2',
           x = x' ->
           EqTrie div2 div2' ->
           EqTrie minus1div2 minus1div2' ->
           EqTrie (TrieNode x div2 minus1div2)
                  (TrieNode x' div2' minus1div2').

(* For the proofs it helps to be able to force evaluation
when needed. See the frob function in
http://adam.chlipala.net/cpdt/html/Coinductive.html *)

Definition evalNatTrie {a} (n : NatTrie a) :=
  match n with TrieNode x nt1 nt2 => TrieNode x nt1 nt2 end.

Lemma evalNatTrie_eq {a} (nt : NatTrie a) : evalNatTrie nt = nt.
Proof. intros. destruct nt; reflexivity. Qed.

(* Now for the lemma we care about *)

CoFixpoint mapTrie_mkTrie  a b (f : a -> b) (g : N -> a) (h : N -> b):
  (forall n, f (g n) = h n) -> (* working around the lack of funext *)
  EqTrie (mapTrie f (mkTrie g)) (mkTrie h).
Proof.
  intro H.
  rewrite <- evalNatTrie_eq with (nt := mapTrie f (mkTrie g)).
  rewrite <- evalNatTrie_eq with (nt := mkTrie h).
  apply eqTrie; simpl.
  * apply H.
  * apply mapTrie_mkTrie.
    intro n. apply H.
  * apply mapTrie_mkTrie.
    intro n. apply H.
Qed.

(* And just because we can, the functor laws: *)

CoFixpoint mapTrie_id a (f : a -> a) t:
  (forall x, f x = x) -> (* working around the lack of funext *)
  EqTrie (mapTrie f t) t.
Proof.
  intro H.
  destruct t.
  rewrite <- evalNatTrie_eq with (nt := mapTrie f _).
  apply eqTrie.
  * apply H.
  * apply mapTrie_id. intro n. apply H.
  * apply mapTrie_id. intro n. apply H.
Qed.


CoFixpoint mapTrie_mapTrie  a b c (f : b -> c) (g : a -> b) (h : a -> c) t:
  (forall x, f (g x) = h x) -> (* working around the lack of funext *)
  EqTrie (mapTrie f (mapTrie g t)) (mapTrie h t).
Proof.
  intro H.
  destruct t.
  rewrite <- evalNatTrie_eq with (nt := mapTrie f (mapTrie g _)).
  rewrite <- evalNatTrie_eq with (nt := mapTrie h _).
  apply eqTrie; simpl.
  * apply H.
  * apply mapTrie_mapTrie. intro n. apply H.
  * apply mapTrie_mapTrie. intro n. apply H.
Qed.

(* Finally, we shoud show that EqTrie implies equality *)
Program Fixpoint
  lookupTrie_EqTrie a (t1 t2 : NatTrie a) x {measure x (N.lt)}:
  EqTrie t1 t2 -> lookupTrie t1 x = lookupTrie t2 x
  := _.
Next Obligation.
  destruct H.
  rewrite (lookupTrie_eq _ x).
  rewrite (lookupTrie_eq _ x).
  simpl.
  repeat destruct (Sumbool.sumbool_of_bool).
  * rewrite N.eqb_eq in *; subst.
    reflexivity.
  * rewrite N.eqb_neq in *.
    apply lookupTrie_EqTrie.
    - apply N.div_lt; lia.
    - assumption.
  * rewrite N.eqb_neq in *.
    apply lookupTrie_EqTrie.
    - apply N.div_lt; lia.
    - assumption.
Qed.
Next Obligation.
  apply Wf.measure_wf.
  apply Coq.NArith.BinNat.N.lt_wf_0.
Qed.

