(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Coq.Lists.List.
Require Import Omega.
Require Import Wellfounded.

(* Converted imports: *)

Require Data.Foldable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Err.
Require HsToCoq.Err.
Require List.
Require Nat.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Heap a b : Type :=
  | Empty : Heap a b
  | Node : a -> b -> list (Heap a b) -> Heap a b.

Arguments Empty {_} {_}.

Arguments Node {_} {_} _ _ _.

(* Converted value declarations: *)

(* Skipping all instances of class `GHC.Base.Eq_', including
   `Data.Graph.Inductive.Internal.Heap.Eq___Heap' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Graph.Inductive.Internal.Heap.Show__Heap' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Graph.Inductive.Internal.Heap.Read__Heap' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Data.Graph.Inductive.Internal.Heap.NFData__Heap' *)

(* Skipping definition `Data.Graph.Inductive.Internal.Heap.prettyHeap' *)

(* Skipping definition `Data.Graph.Inductive.Internal.Heap.printPrettyHeap' *)

Definition empty {a : Type} {b : Type} : Heap a b :=
  Empty.

Definition unit {a : Type} {b : Type} : a -> b -> Heap a b :=
  fun key val => Node key val nil.

Definition merge {a : Type} {b : Type} `{GHC.Base.Ord a}
   : Heap a b -> Heap a b -> Heap a b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | h, Empty => h
    | Empty, h => h
    | (Node key1 val1 hs as h), (Node key2 val2 hs' as h') =>
        if key1 GHC.Base.< key2 : bool then Node key1 val1 (cons h' hs) else
        Node key2 val2 (cons h hs')
    end.

Definition insert {a : Type} {b : Type} `{GHC.Base.Ord a}
   : (a * b)%type -> Heap a b -> Heap a b :=
  fun '(pair key val) => merge (unit key val).

Fixpoint mergeAll {a : Type} {b : Type} `{GHC.Base.Ord a} (arg_0__
                    : list (Heap a b)) : Heap a b
  := match arg_0__ with
     | nil => Empty
     | cons h nil => h
     | cons h (cons h' hs) => merge (merge h h') (mergeAll hs)
     end.

Definition isEmpty {a : Type} {b : Type} : Heap a b -> bool :=
  fun arg_0__ => match arg_0__ with | Empty => true | _ => false end.

Definition findMin {a} {b} `{HsToCoq.Err.Default (a * b)} : Heap a b -> a * b :=
  fun arg_0__ =>
    match arg_0__ with
    | Empty => GHC.Err.error (GHC.Base.hs_string__ "Heap.findMin: empty heap")
    | Node key val _ => pair key val
    end.

Definition deleteMin {a : Type} {b : Type} `{GHC.Base.Ord a}
   : Heap a b -> Heap a b :=
  fun arg_0__ =>
    match arg_0__ with
    | Empty => Empty
    | Node _ _ hs => mergeAll hs
    end.

Definition splitMin {a} {b} `{GHC.Base.Ord a} `{HsToCoq.Err.Default (a * b *
                                                                     Heap a b)}
   : Heap a b -> a * b * Heap a b :=
  fun arg_0__ =>
    match arg_0__ with
    | Empty => GHC.Err.error (GHC.Base.hs_string__ "Heap.splitMin: empty heap")
    | Node key val hs => pair (pair key val) (mergeAll hs)
    end.

Definition build {a : Type} {b : Type} `{GHC.Base.Ord a}
   : list (a * b)%type -> Heap a b :=
  Data.Foldable.foldr insert Empty.

Fixpoint size {a} {b} (h : Heap a b)
  := match h with
     | Empty => 0
     | Node _ _ l => 1 + List.fold_right plus 0 (List.map (fun x => size x) l)
     end.

Lemma merge_size {a} {b} `{GHC.Base.Ord a} (h1 h2 : Heap a b) : size (merge h1
                                                                            h2) =
  Nat.add (size h1) (size h2).
Proof.
intros. generalize dependent h2. induction h1; intros; simpl.
  - destruct h2; reflexivity.
  - destruct h2; simpl. omega. destruct (_GHC.Base.<_ a0 a1 ) eqn : ?; simpl; omega.
 
Qed.

Lemma mergeAll_size {a} {b} `{GHC.Base.Ord a} (l : list (Heap a b)) : size
  (mergeAll l) =
  List.fold_right plus 0 (List.map (fun x => size x) l).
Proof.
  intros. induction l using (well_founded_induction
                       (wf_inverse_image _ nat _ (@length _)
                          PeanoNat.Nat.lt_wf_0)).
  destruct l.
  - reflexivity.
  - destruct l.
    + simpl. omega.
    + simpl. repeat(rewrite merge_size). rewrite plus_assoc. rewrite H1. reflexivity. simpl. omega.
Qed.

Lemma deleteMin_size {a} {b} `{GHC.Base.Ord a} (h : Heap a b) : h <> Empty ->
  size (deleteMin h) + 1 = size h.
Proof.
  intros. unfold deleteMin. destruct h. contradiction. rewrite mergeAll_size.
  unfold size. simpl. omega.
Qed.

Lemma toList_termination {a} {b} `{GHC.Base.Ord a} (h : Heap a b) : Empty <>
  h ->
  size (deleteMin h) < size h.
Proof.
  intros. assert (A: h <> Empty) by auto; apply deleteMin_size in A; omega.
Qed.

Program Fixpoint toList {a} {b} `{GHC.Base.Ord a} `{HsToCoq.Err.Default (a * b)}
                        (arg_0__ : Heap a b) {measure (size arg_0__)} : list (a * b)
  := match arg_0__ with
     | Empty => nil
     | h => let 'pair x r := pair (findMin h) (deleteMin h) in cons x (toList r)
     end.
Solve Obligations with ((Tactics.program_simpl; apply toList_termination; auto)).

Definition heapsort {a} `{GHC.Base.Ord a} `{HsToCoq.Err.Default (a * a)}
   : list a -> list a :=
  GHC.Base.map Data.Tuple.fst GHC.Base.∘
  (toList GHC.Base.∘ (build GHC.Base.∘ GHC.Base.map (fun x => pair x x))).

(* External variables:
     Type bool cons false list nil op_ze__ op_zl__ op_zlzg__ op_zp__ op_zt__ pair
     plus true Data.Foldable.foldr Data.Tuple.fst GHC.Base.Ord GHC.Base.map
     GHC.Base.op_z2218U__ GHC.Base.op_zl__ GHC.Err.error HsToCoq.Err.Default
     List.fold_right List.map Nat.add
*)
