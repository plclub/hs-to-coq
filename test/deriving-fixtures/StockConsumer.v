Require Import DerivingForeign DerivingStock.
Require Import Data.Traversable Data.Functor.Identity.

Definition inferredTraversal {a b : Type} (f : a -> Identity b) :
  Foreign a -> Identity (Foreign b) := traverse f.

Example imported_stock_instance_computes :
  inferredTraversal (fun x : bool => Mk_Identity (negb x)) (MkForeign true) =
    Mk_Identity (MkForeign false).
Proof. reflexivity. Qed.

Example same_module_stock_use_computes :
  useTraverse (fun x : bool => Mk_Identity (negb x)) (MkForeign false) =
    Mk_Identity (MkForeign true).
Proof. reflexivity. Qed.
