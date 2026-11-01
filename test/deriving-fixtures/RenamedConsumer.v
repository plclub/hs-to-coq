Require Import Recovered.

Definition inferredKeep : Wrapped -> Wrapped := keep.

Example renamed_instance_computes :
  inferredKeep (MkWrapped true) = MkWrapped true.
Proof. reflexivity. Qed.

Example renamed_same_module_use_computes :
  useKept (MkWrapped false) = MkWrapped false.
Proof. reflexivity. Qed.
