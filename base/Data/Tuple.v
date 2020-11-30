(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require GHC.Tuple.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition fst {a : Type} {b : Type} : GHC.Tuple.pair_type a b -> a :=
  fun '(pair x _) => x.

Definition snd {a : Type} {b : Type} : GHC.Tuple.pair_type a b -> b :=
  fun '(pair _ y) => y.

Definition curry {a : Type} {b : Type} {c : Type}
   : (GHC.Tuple.pair_type a b -> c) -> a -> b -> c :=
  fun f x y => f (pair x y).

Definition uncurry {a : Type} {b : Type} {c : Type}
   : (a -> b -> c) -> GHC.Tuple.pair_type a b -> c :=
  fun f p => f (fst p) (snd p).

Definition swap {a : Type} {b : Type}
   : GHC.Tuple.pair_type a b -> GHC.Tuple.pair_type b a :=
  fun '(pair a b) => pair b a.

(* External variables:
     Type pair GHC.Tuple.pair_type
*)
