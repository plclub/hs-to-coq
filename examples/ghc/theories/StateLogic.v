Require Import GHC.Base.
Require GHC.Utils.Monad.State.Strict.
Require Data.Traversable.

Set Bullet Behavior "Strict Subproofs".

Module State := GHC.Utils.Monad.State.Strict.

Local Ltac expand_pairs :=
match goal with
  |- context[let (_,_) := ?e in _] =>
  rewrite (surjective_pairing e)
end.

Definition SP {a} {s} (P Q : s -> Prop) (R : a -> Prop) (act : State.State s a) :=
  forall s, P s -> Q (snd (State.runState act s)) /\ R (fst (State.runState act s)).

Definition StateInvariant {a} {s} (P : s -> Prop) (act : State.State s a) :=
  SP P P (fun _ => True) act.

(* GHC 9.10: State monad changed from newtype wrapper to bare function type.
   All StateInvariant lemmas Admitted since proofs need reworking for
   GHC.Utils.Monad.State.Strict. *)

Lemma SP_snd_runState:
  forall {a s} (P P' : s -> Prop) (R : a -> Prop) (act : State.State s a) (x : s),
  SP P P' R act ->
  P x ->
  P' (snd (State.runState act x)).
Proof.
  intros.
  unfold State.runState.
  apply H. assumption.
Qed.

Lemma SP_return:
  forall {a s} (P : s -> Prop) (Q : a -> Prop) (x : a),
  Q x -> SP P P Q (return_ x).
Admitted.

Lemma StateInvariant_return:
  forall {a s} (P : s -> Prop) (x : a),
  StateInvariant P (return_ x).
Admitted.

Lemma SP_put:
  forall {s} (P P' : s -> Prop) x,
  P' x ->
  SP P P' (fun _ => True) (State.put x).
Proof. intros. intros s0 _. unfold State.put. simpl. split; [ apply H | trivial ]. Qed.

Lemma SP_get:
  forall {s} (P : s -> Prop),
  SP P P P State.get.
Proof. intros. intros s0 H. unfold State.get. simpl. split; assumption. Qed.

Lemma SP_bind:
  forall {a b s} P P' P'' R R' (act1 : State.State s a) (act2 : a -> State.State s b),
  SP P P' R act1 ->
  (forall x, R x -> SP P' P'' R' (act2 x)) ->
  SP P P'' R' (act1 >>= act2).
Admitted.

Lemma StateInvariant_bind:
  forall {a b s} P (act1 : State.State s a) (act2 : a -> State.State s b),
  StateInvariant P act1 ->
  (forall x, StateInvariant P (act2 x)) ->
  StateInvariant P (act1 >>= act2).
Admitted.

Lemma StateInvariant_bind_return:
  forall {a b s} P (act1 : State.State s a) (f : a -> b),
  StateInvariant P act1 ->
  StateInvariant P (act1 >>= (fun x => return_ (f x))).
Admitted.

Lemma StateInvariant_liftA2:
  forall {a b c s} P (f : a -> b -> c) (act1 : State.State s a) (act2 : State.State s b),
  StateInvariant P act1 ->
  StateInvariant P act2 ->
  StateInvariant P (liftA2 f act1 act2).
Admitted.

Lemma StateInvariant_mapM:
  forall {a b s} P (act : a -> State.State s b) (xs : list a),
  (forall x, In x xs -> StateInvariant P (act x)) ->
  StateInvariant P (Traversable.mapM act xs).
Admitted.

Lemma StateInvariant_forM:
  forall {a b s} P (act : a -> State.State s b) (xs : list a),
  (forall x, In x xs -> StateInvariant P (act x)) ->
  StateInvariant P (Traversable.forM xs act).
Admitted.

Definition RevStateInvariant {a} {s} (P : s -> Prop) (act : State.State s a)  (R : a -> Prop) :=
  forall s, P (snd (State.runState act s)) -> P s /\ R (fst (State.runState act s)).

Lemma RevStateInvariant_runState {a} {s} (P : s -> Prop)  (act : State.State s a)  (R : a -> Prop)(s0 : s) :
  RevStateInvariant P act R ->
  P (snd (State.runState act s0)) ->
  R (fst (State.runState act s0)).
Proof. unfold State.runState in *. intros. apply H. apply H0. Qed.

Lemma RevStateInvariant_return {a} {s} (P : s -> Prop) (x : a)  (R : a -> Prop):
  R x ->
  RevStateInvariant P (return_ x) R.
Admitted.

Lemma RevStateInvariant_bind {a b} {s} (P : s -> Prop)
    (act1 : State.State s a) (act2 : a -> State.State s b)
    (Q : a -> Prop) (R : b -> Prop):
  RevStateInvariant P (act1) Q ->
  (forall x,  RevStateInvariant P (act2 x) (fun x' => Q x -> R x')) ->
  RevStateInvariant P (act1 >>= act2) R.
Admitted.

Lemma RevStateInvariant_impl {a} {s} (P : s -> Prop)
    (act1 : State.State s a) (R Q : a -> Prop):
  RevStateInvariant P act1 R ->
  (forall x, R x -> Q x) ->
  RevStateInvariant P act1 Q.
Proof.
  intros Hact1 Himpl.
  split.
  * apply Hact1. apply H.
  * apply Himpl. apply Hact1. apply H.
Qed.

Lemma RevStateInvariant_bind_return {a b} {s} (P : s -> Prop)
    (act1 : State.State s a) (f : a -> b)
    (R : b -> Prop):
  RevStateInvariant P act1 (fun x => R (f x)) ->
  RevStateInvariant P (act1 >>= (fun x => return_ (f x))) R.
Admitted.

Lemma RevStateInvariant_liftA2:
  forall {a b c s} P (f : a -> b -> c) (act1 : State.State s a) (act2 : State.State s b) R1 R2 (R3 : c -> Prop),
  RevStateInvariant P act1 R1 ->
  RevStateInvariant P act2 R2 ->
  (forall x y, R1 x -> R2 y -> R3 (f x y)) ->
  RevStateInvariant P (liftA2 f act1 act2) R3.
Admitted.

Lemma RevStateInvariant_mapM2:
  forall {a b s} P (act : a -> State.State s b) (xs : list a) R,
  (forall x, In x xs -> RevStateInvariant P (act x) (R x)) ->
  RevStateInvariant P (Traversable.mapM act xs) (Forall2 R xs).
Admitted.

Lemma RevStateInvariant_forM2:
  forall {a b s} P (act : a -> State.State s b) (xs : list a) R,
  (forall x, In x xs -> RevStateInvariant P (act x) (R x)) ->
  RevStateInvariant P (Traversable.forM xs act) (Forall2 R xs).
Admitted.

Lemma Forall2_const_Forall:
  forall {a b} R (xs : list a) (ys : list b),
  Forall2 (fun _ => R) xs ys -> Forall R ys.
Proof.
  intros. induction H.
  * constructor.
  * constructor; assumption.
Qed.

Lemma Forall2_and:
  forall {a b} P Q (xs : list a) (ys : list b),
  Forall2 (fun x y => P x y /\ Q x y) xs ys -> (Forall2 P xs ys /\ Forall2 Q xs ys).
Proof.
  intros. induction H.
  * constructor; constructor.
  * constructor; constructor; intuition.
Qed.

Lemma Forall2_eq:
  forall {a b c} (f : a -> c) (g : b -> c) (xs : list a) (ys : list b),
  Forall2 (fun x y => f x = g y) xs ys -> List.map f xs = List.map g ys.
Proof.
  intros. induction H.
  * reflexivity.
  * simpl. f_equal; assumption.
Qed.

Lemma RevStateInvariant_forM:
  forall {a b s} P (act : a -> State.State s b) (xs : list a) R,
  (forall x, In x xs -> RevStateInvariant P (act x) R) ->
  RevStateInvariant P (Traversable.forM xs act) (Forall R).
Proof.
  intros.
  eapply RevStateInvariant_impl.
  * apply RevStateInvariant_forM2.
    apply H.
  * apply Forall2_const_Forall.
Qed.
