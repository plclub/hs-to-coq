Require Import DerivingInlineKinds GHC.Base.

Definition inferredWrapMap : Wrap option bool -> Wrap option bool := fmap negb.

Example higher_kinded_inline_instance_computes :
  getWrap (inferredWrapMap (MkWrap (Some true))) = Some false.
Proof. reflexivity. Qed.

Example polykinded_inline_instance_computes :
  getPhantom (op_zlzlzgzg__
    (MkPhantom (cons true nil) : @Phantom unit (list bool) tt)
    (MkPhantom (cons false nil))) = cons true (cons false nil).
Proof. reflexivity. Qed.

Print Assumptions higher_kinded_inline_instance_computes.
Print Assumptions polykinded_inline_instance_computes.
