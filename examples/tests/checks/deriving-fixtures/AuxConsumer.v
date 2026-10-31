Require Import DerivingAux.

Definition inferredKeep : Wrapped -> Wrapped := keep.

Example retained_instance_computes :
  inferredKeep (MkWrapped true) = MkWrapped true.
Proof. reflexivity. Qed.

Example same_module_use_computes :
  useKept (MkWrapped false) = MkWrapped false.
Proof. reflexivity. Qed.
