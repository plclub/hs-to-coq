Require Import DerivingRetainedAux EnumAuxRuntime GHC.Enum.

Definition inferredEnumerate : E -> list E := GHC.Enum.enumerate.

(* Both stock helpers must survive: tag2con maps the tags and maxtag supplies B. *)
Example retained_helpers_compute : inferredEnumerate A = cons A (cons B nil).
Proof. reflexivity. Qed.

Print Assumptions retained_helpers_compute.
