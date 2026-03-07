(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.ZArith.BinInt.
Require Data.IntSet.Internal.
Require GHC.Base.
Require GHC.Enum.

(* Converted type declarations: *)

Inductive EnumSet (a : Type) : Type :=
  | Mk_EnumSet : Data.IntSet.Internal.IntSet -> EnumSet a.

#[global] Definition BitArray :=
  GHC.Num.Integer.Integer%type.

Arguments Mk_EnumSet {_} _.

(* Converted value declarations: *)

Instance Semigroup__EnumSet
   : forall {k} {a}, GHC.Base.Semigroup (EnumSet a : Type).
Proof.
Admitted.

Instance Monoid__EnumSet : forall {k} {a}, GHC.Base.Monoid (EnumSet a : Type).
Proof.
Admitted.

(* Skipping all instances of class `Binary.Binary', including
   `EnumSet.Binary__EnumSet' *)

Axiom member : forall {a : Type},
               forall `{GHC.Enum.Enum a}, a -> EnumSet a -> bool.

Axiom insert : forall {a : Type},
               forall `{GHC.Enum.Enum a}, a -> EnumSet a -> EnumSet a.

Axiom delete : forall {a : Type},
               forall `{GHC.Enum.Enum a}, a -> EnumSet a -> EnumSet a.

Axiom toList : forall {a : Type},
               forall `{GHC.Enum.Enum a}, EnumSet a -> list a.

Axiom fromList : forall {a : Type},
                 forall `{GHC.Enum.Enum a}, list a -> EnumSet a.

Axiom empty : forall {k : Type}, forall {a : k}, EnumSet a.

Axiom difference : forall {k : Type},
                   forall {a : k}, EnumSet a -> EnumSet a -> EnumSet a.

Axiom enumSetToBitArray : forall {a}, EnumSet a -> BitArray.

Axiom bitArrayToEnumSet : forall {a}, BitArray -> EnumSet a.

#[global] Definition fromEnumN {a} `{GHC.Enum.Enum a} (e : a) :=
  Coq.ZArith.BinInt.Z.to_N (GHC.Enum.fromEnum e).

#[global] Definition toEnumN {a} `{GHC.Enum.Enum a} n : a :=
  GHC.Enum.toEnum (Coq.ZArith.BinInt.Z.of_N n).

(* External variables:
     Type bool list Coq.ZArith.BinInt.Z.of_N Coq.ZArith.BinInt.Z.to_N
     Data.IntSet.Internal.IntSet GHC.Base.Monoid GHC.Base.Semigroup GHC.Enum.Enum
     GHC.Enum.fromEnum GHC.Enum.toEnum GHC.Num.Integer.Integer
*)
