Require Import Data.Traversable Data.Functor.Identity.

Example bridge_same_module_identity :
  useIdentity (fun b => Some (negb b)) (Mk_Identity true) =
    Some (Mk_Identity false).
Proof. reflexivity. Qed.

Example bridge_nested_source_class :
  useWrap (fun b => Some (negb b)) (MkWrap (Mk_Identity true)) =
    Some (MkWrap (Mk_Identity false)).
Proof. reflexivity. Qed.

Print Assumptions bridge_nested_source_class.
