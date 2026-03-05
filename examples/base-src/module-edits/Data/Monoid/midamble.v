(* Fix implicit arguments for Mk_Ap after redefine *)
Arguments Mk_Ap {_} {_} _.

(* getAp accessor — needed since redefine Inductive doesn't auto-generate it *)
Definition getAp {f : Type -> Type} {a : Type} (x : Ap f a) : f a :=
  let 'Mk_Ap v := x in v.
