Require Import DerivingRetainedAux EnumAuxRuntime GHC.Enum.

Definition inferredEnumerate : E -> list E := GHC.Enum.enumerate.

Example renamed_method_edit_computes : inferredEnumerate A = cons B nil.
Proof. reflexivity. Qed.

Print Assumptions renamed_method_edit_computes.
