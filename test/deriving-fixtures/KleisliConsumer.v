Require Import DerivingKleisli GHC.Base.

Definition inferredMap : Kleisli option bool bool -> Kleisli option bool bool :=
  fmap negb.

Example kleisli_derived_fmap_computes :
  runKleisli (inferredMap (MkKleisli (fun x => Some x))) true = Some false.
Proof. reflexivity. Qed.

Example kleisli_derived_replace_computes :
  runKleisli (op_zlzd__ false (MkKleisli (fun x : bool => Some x))) true = Some false.
Proof. reflexivity. Qed.

Example kleisli_same_module_use_computes :
  runKleisli (useMap negb (MkKleisli (fun x => Some x))) false = Some true.
Proof. reflexivity. Qed.

Print Assumptions kleisli_derived_fmap_computes.
