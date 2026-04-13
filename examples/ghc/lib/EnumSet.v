(* Default settings (from HsToRocq.Rocq.Preamble) *)

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
Require GHC.Enum.
Require GHC.Num.

(* Converted type declarations: *)

Inductive EnumSet (a : Type) : Type :=
  | Mk_EnumSet : Data.IntSet.Internal.IntSet -> EnumSet a.

#[global] Definition BitArray :=
  GHC.Num.Integer%type.

Arguments Mk_EnumSet {_} _.

(* Converted value declarations: *)

(* Skipping instance `EnumSet.Semigroup__EnumSet' of class
   `GHC.Base.Semigroup' *)

(* Skipping instance `EnumSet.Monoid__EnumSet' of class `GHC.Base.Monoid' *)

(* Skipping all instances of class `Binary.Binary', including
   `EnumSet.Binary__EnumSet' *)

Axiom member : forall {a : Type},
               forall `{GHC.Enum.Enum a}, a -> EnumSet a -> bool.

(* Skipping definition `EnumSet.insert' *)

(* Skipping definition `EnumSet.delete' *)

Axiom toList : forall {a : Type},
               forall `{GHC.Enum.Enum a}, EnumSet a -> list a.

Axiom fromList : forall {a : Type},
                 forall `{GHC.Enum.Enum a}, list a -> EnumSet a.

(* Skipping definition `EnumSet.empty' *)

(* Skipping definition `EnumSet.difference' *)

Axiom enumSetToBitArray : forall {a}, EnumSet a -> BitArray.

Axiom bitArrayToEnumSet : forall {a}, BitArray -> EnumSet a.

#[global] Definition fromEnumN {a} `{GHC.Enum.Enum a} (e : a) :=
  Coq.ZArith.BinInt.Z.to_N (GHC.Enum.fromEnum e).

#[global] Definition toEnumN {a} `{GHC.Enum.Enum a} n : a :=
  GHC.Enum.toEnum (Coq.ZArith.BinInt.Z.of_N n).

(* External variables:
     Type bool list Coq.ZArith.BinInt.Z.of_N Coq.ZArith.BinInt.Z.to_N
     Data.IntSet.Internal.IntSet GHC.Enum.Enum GHC.Enum.fromEnum GHC.Enum.toEnum
     GHC.Num.Integer
*)
