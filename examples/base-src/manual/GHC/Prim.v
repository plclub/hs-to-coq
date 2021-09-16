Require Import HsToCoq.Unpeel.
Require Import GHC.Types.

Definition arrow  := (fun (x y :Type) => x -> y).

Definition seq {A} {B} (a : A) (b:B) := b.

(* Coq has no levity polymorphism, so map everything to Type *)
Definition TYPE (_ : RuntimeRep) := Type.

Class Coercible a b := { coerce : a -> b }.

Instance Coercible_Unpeel
  a b c
  {U1 : Unpeel a c}
  {U2 : Unpeel b c}
  : Coercible a b :=
  { coerce x := @repeel b c U2 (@unpeel a c U1 x) }.
