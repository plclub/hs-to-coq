Require Import DerivingRedefinedAux GHC.Enum GHC.Num.

Definition inferredFromEnum : E -> GHC.Num.Int := GHC.Enum.fromEnum.

(* Stock deriving would return 1 for B; the whole-instance edit returns 7. *)
Example redefined_instance_computes : inferredFromEnum B = 7%Z.
Proof. reflexivity. Qed.
