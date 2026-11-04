Require Import DerivingModuleSkip.

Definition inferredKeep : Wrapped -> Wrapped := keep.

Example module_skip_retains_instance :
  inferredKeep (MkWrapped true) = MkWrapped true.
Proof. reflexivity. Qed.

Example module_skip_retains_same_module_use :
  useKept (MkWrapped false) = MkWrapped false.
Proof. reflexivity. Qed.
