Require Import DerivingInline.

Definition inferredKeep : Wrapped -> Wrapped := keep.

Example inline_instance_computes :
  inferredKeep (MkWrapped true) = MkWrapped true.
Proof. reflexivity. Qed.

Example inline_same_module_use_computes :
  useKept (MkWrapped false) = MkWrapped false.
Proof. reflexivity. Qed.
