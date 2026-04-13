(* Eq/Ord for Either -- GHC 9.10 derives using dataToTag# which hs-to-rocq can't translate *)

Definition eq_Either {a} {b} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b}
  (x y : Either a b) : bool :=
  match x, y with
  | Left a1, Left b1 => a1 GHC.Base.== b1
  | Right a1, Right b1 => a1 GHC.Base.== b1
  | _, _ => false
  end.

Definition compare_Either {a} {b} `{GHC.Base.Ord a} `{GHC.Base.Ord b}
  (x y : Either a b) : comparison :=
  match x, y with
  | Left a1, Left b1 => GHC.Base.compare a1 b1
  | Left _, Right _ => Lt
  | Right _, Left _ => Gt
  | Right a1, Right b1 => GHC.Base.compare a1 b1
  end.

#[global]
Instance Eq___Either {a} {b} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b}
  : GHC.Base.Eq_ (Either a b) := fun _ k => k {|
  GHC.Base.op_zeze____ := eq_Either;
  GHC.Base.op_zsze____ := fun x y => negb (eq_Either x y) |}.

#[global]
Instance Ord__Either {a} {b} `{GHC.Base.Ord a} `{GHC.Base.Ord b}
  : GHC.Base.Ord (Either a b) :=
  GHC.Base.ord_default compare_Either.
