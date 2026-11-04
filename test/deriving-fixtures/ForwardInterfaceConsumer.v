Require Import DerivingZClass DerivingAClient.

Definition inferredMethod : bool -> bool := method.

Example explicit_instance_computes : inferredMethod true = true.
Proof. reflexivity. Qed.
