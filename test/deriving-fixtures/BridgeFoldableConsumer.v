Require Import Data.Foldable Data.Ord GHC.Tuple.

Definition inferredDown : Down bool -> bool := foldr (fun x _ => x) false.

Example bridge_foldable_down : inferredDown (Mk_Down true) = true.
Proof. reflexivity. Qed.

Example bridge_foldable_same_module :
  useDown (fun x _ => negb x) true (Mk_Down true) = false.
Proof. reflexivity. Qed.

Example bridge_foldable_nested :
  useWrap (fun x _ => negb x) true (MkWrap (Mk_Down true)) = false.
Proof. reflexivity. Qed.

Example bridge_foldable_foldMap :
  foldMap (fun x : bool => cons (negb x) nil) (Mk_Down true) = cons false nil.
Proof. reflexivity. Qed.

Example bridge_foldable_solo :
  useSolo (fun x _ => negb x) true (MkSolo true) = false.
Proof. reflexivity. Qed.

Print Assumptions bridge_foldable_nested.
