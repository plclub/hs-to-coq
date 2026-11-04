Require Import MethodAux GHC.Enum GHC.Num.

Definition inferredFromEnum : E -> GHC.Num.Int := GHC.Enum.fromEnum.
Definition inferredSucc : E -> E := GHC.Enum.succ.

Example redefined_method_computes : inferredFromEnum B = 7%Z.
Proof. reflexivity. Qed.

Example redefined_succ_computes : inferredSucc A = B.
Proof. reflexivity. Qed.
