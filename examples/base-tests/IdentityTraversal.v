(* Issue 228: exercise only public, inferred dictionaries from the compiled base.
   This file is shared unchanged by Coq 8.20 and Rocq 9.0. *)
Require Import Data.Functor.Identity.
Require Data.Foldable.
Require Data.Ord.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Tuple.

(* Bound typeclass search so missing shared instances fail promptly. *)
Set Typeclasses Depth 10.

Lemma solo_fmap {A B : Type} (f : A -> B) (x : A) :
  GHC.Base.fmap f (GHC.Tuple.MkSolo x) = GHC.Tuple.MkSolo (f x).
Proof. reflexivity. Qed.

Lemma solo_down_foldr {A B : Type} (f : A -> B -> B) (z : B) (x : A) :
  Data.Foldable.foldr f z (GHC.Tuple.MkSolo x) = f x z /\
  Data.Foldable.foldr f z (Data.Ord.Mk_Down x) = f x z.
Proof. split; reflexivity. Qed.

Lemma solo_down_traverse
    {F : Type -> Type} `{GHC.Base.Applicative F}
    {A B : Type} (f : A -> F B) (x : A) :
  Data.Traversable.traverse f (GHC.Tuple.MkSolo x) =
    GHC.Base.fmap GHC.Tuple.MkSolo (f x) /\
  Data.Traversable.traverse f (Data.Ord.Mk_Down x) =
    GHC.Base.fmap Data.Ord.Mk_Down (f x).
Proof. split; reflexivity. Qed.

Lemma solo_down_mapAccumL
    {S A B : Type} (step : S -> A -> S * B)
    (st st' : S) (x : A) (y : B) :
  step st x = (st', y) ->
  Data.Traversable.mapAccumL step st (GHC.Tuple.MkSolo x) =
    (st', GHC.Tuple.MkSolo y) /\
  Data.Traversable.mapAccumL step st (Data.Ord.Mk_Down x) =
    (st', Data.Ord.Mk_Down y).
Proof.
  intro Hstep.
  change ((let '(s, b) := step st x in (s, GHC.Tuple.MkSolo b)) =
            (st', GHC.Tuple.MkSolo y) /\
          (let '(s, b) := step st x in (s, Data.Ord.Mk_Down b)) =
            (st', Data.Ord.Mk_Down y)).
  rewrite Hstep. split; reflexivity.
Qed.

(* Test both successful effects and short-circuiting, then state/value order. *)
Example solo_down_computes :
  Data.Traversable.traverse (fun x : nat => Some (S x))
    (GHC.Tuple.MkSolo 7) = Some (GHC.Tuple.MkSolo 8) /\
  Data.Traversable.traverse (fun _ : nat => @None nat)
    (Data.Ord.Mk_Down 7) = None /\
  Data.Traversable.mapAccumL
    (fun st x : nat => (S st, Nat.add st x)) 3 (GHC.Tuple.MkSolo 7) =
    (4, GHC.Tuple.MkSolo 10) /\
  Data.Traversable.mapAccumL
    (fun st x : nat => (S st, Nat.add st x)) 3 (Data.Ord.Mk_Down 7) =
    (4, Data.Ord.Mk_Down 10).
Proof. repeat split; reflexivity. Qed.

Lemma identity_traverse
    {F : Type -> Type} `{GHC.Base.Applicative F}
    {A B : Type} (f : A -> F B) (x : A) :
  Data.Traversable.traverse f (Mk_Identity x) =
  GHC.Base.fmap Mk_Identity (f x).
Proof. reflexivity. Qed.

Lemma identity_mapAccumL
    {S A B : Type} (step : S -> A -> S * B)
    (st st' : S) (x : A) (y : B) :
  step st x = (st', y) ->
  Data.Traversable.mapAccumL step st (Mk_Identity x) =
  (st', Mk_Identity y).
Proof.
  intro Hstep.
  change ((let '(s, b) := step st x in (s, Mk_Identity b)) =
          (st', Mk_Identity y)).
  rewrite Hstep. reflexivity.
Qed.

(* A concrete reduction also checks state/value order and a changed state. *)
Example identity_mapAccumL_computes :
  Data.Traversable.mapAccumL
    (fun st x : nat => (S st, Nat.add st x)) 3 (Mk_Identity 7) =
  (4, Mk_Identity 10).
Proof. reflexivity. Qed.

(* Audit the actual production instances, not a locally supplied dictionary. *)
Print Assumptions GHC.Base.Functor__Solo.
Print Assumptions Data.Foldable.Foldable__Solo.
Print Assumptions Data.Foldable.Foldable__Down.
Print Assumptions Data.Traversable.Traversable__Solo.
Print Assumptions Data.Traversable.Traversable__Down.
Print Assumptions Data.Traversable.Traversable__Identity.

(* The runner requires all fourteen transitive reports to be closed. *)
Print Assumptions solo_fmap.
Print Assumptions solo_down_foldr.
Print Assumptions solo_down_traverse.
Print Assumptions solo_down_mapAccumL.
Print Assumptions solo_down_computes.
Print Assumptions identity_traverse.
Print Assumptions identity_mapAccumL.
Print Assumptions identity_mapAccumL_computes.
