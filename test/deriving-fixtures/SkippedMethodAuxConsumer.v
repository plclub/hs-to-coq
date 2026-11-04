Require Import DerivingRetainedAux EnumAuxRuntime GHC.Enum.

Definition inferredFromEnum : E -> Boxed := GHC.Enum.fromEnum.

(* This original method still translates, but needs neither Enum helper. *)
Example surviving_method_computes : inferredFromEnum B = BoxInt 1.
Proof. reflexivity. Qed.

Print Assumptions surviving_method_computes.
