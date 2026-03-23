(* Fix implicit arguments for Mk_Ap after redefine *)
Arguments Mk_Ap {_} {_} _.

(* getAp accessor -- needed since redefine Inductive doesn't auto-generate it *)
Definition getAp {f : Type -> Type} {a : Type} (x : Ap f a) : f a :=
  let 'Mk_Ap v := x in v.

(* Eq/Ord for First -- GHC 9.10 derives using dataToTag# *)

Definition eq_First {a} `{GHC.Base.Eq_ a} (x y : First a) : bool :=
  match x, y with
  | Mk_First a1, Mk_First b1 => a1 GHC.Base.== b1
  end.

#[global]
Instance Eq___First {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (First a) :=
  fun _ k => k {|
  GHC.Base.op_zeze____ := eq_First;
  GHC.Base.op_zsze____ := fun x y => negb (eq_First x y) |}.

#[global]
Instance Ord__First {a} `{GHC.Base.Ord a} : GHC.Base.Ord (First a) :=
  GHC.Base.ord_default (fun x y =>
    match x, y with
    | Mk_First a1, Mk_First b1 => GHC.Base.compare a1 b1
    end).

(* Eq/Ord for Last -- GHC 9.10 derives using dataToTag# *)

Definition eq_Last {a} `{GHC.Base.Eq_ a} (x y : Last a) : bool :=
  match x, y with
  | Mk_Last a1, Mk_Last b1 => a1 GHC.Base.== b1
  end.

#[global]
Instance Eq___Last {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Last a) :=
  fun _ k => k {|
  GHC.Base.op_zeze____ := eq_Last;
  GHC.Base.op_zsze____ := fun x y => negb (eq_Last x y) |}.

#[global]
Instance Ord__Last {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Last a) :=
  GHC.Base.ord_default (fun x y =>
    match x, y with
    | Mk_Last a1, Mk_Last b1 => GHC.Base.compare a1 b1
    end).
