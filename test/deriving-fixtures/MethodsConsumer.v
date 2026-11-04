Require Import DerivingMethods.

Definition inferredInline : Inline -> Inline := keep.
Definition inferredStandalone : Standalone -> Standalone := keep.
Definition inferredNested : Nested -> Nested := keep.

Example inline_method_skip_computes :
  inferredInline (MkInline true) = MkInline true.
Proof. reflexivity. Qed.

Example standalone_method_skip_computes :
  inferredStandalone (MkStandalone false) = MkStandalone false.
Proof. reflexivity. Qed.

Example explicit_method_skip_computes : keep true = true.
Proof. reflexivity. Qed.

Example dependent_derivations_compute :
  inferredNested (MkNested (MkStandalone true)) = MkNested (MkStandalone true).
Proof. reflexivity. Qed.

Example same_module_methods_computes :
  useInline (MkInline false) = MkInline false /\
  useStandalone (MkStandalone true) = MkStandalone true /\
  useNested (MkNested (MkStandalone false)) = MkNested (MkStandalone false).
Proof. repeat split; reflexivity. Qed.
