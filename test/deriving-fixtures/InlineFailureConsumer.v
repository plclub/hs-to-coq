Require Import DerivingInlineFailure.

Definition inferredKeep : Wrapped -> Wrapped := keep.

Example permissive_inline_failure_retains_instance :
  inferredKeep (MkWrapped true) = MkWrapped true.
Proof. reflexivity. Qed.

Example permissive_inline_failure_retains_use :
  useKept (MkWrapped false) = MkWrapped false.
Proof. reflexivity. Qed.
