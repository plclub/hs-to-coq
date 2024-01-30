(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.

(* Converted type declarations: *)

Inductive Void : Type :=.

(* Converted value declarations: *)

(* Skipping all instances of class `GHC.Ix.Ix', including
   `Data.Void.Ix__Void' *)

(* Skipping all instances of class `GHC.Exception.Type.Exception', including
   `Data.Void.Exception__Void' *)

#[local] Definition Semigroup__Void_op_zlzlzgzg__ : Void -> Void -> Void :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | a, _ => a end.

#[global]
Program Instance Semigroup__Void : GHC.Base.Semigroup Void :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Void_op_zlzlzgzg__ |}.

#[global] Definition absurd {a : Type} : Void -> a :=
  fun a => match a with end.

#[global] Definition vacuous {f : Type -> Type} {a : Type} `{GHC.Base.Functor f}
   : f Void -> f a :=
  GHC.Base.fmap absurd.

(* External variables:
     Type GHC.Base.Functor GHC.Base.Semigroup GHC.Base.fmap GHC.Base.op_zlzlzgzg____
*)
