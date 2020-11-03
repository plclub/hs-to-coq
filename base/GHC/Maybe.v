(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Local Definition Eq___option_op_zeze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : option inst_a -> option inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | None, None => true
    | Some a1, Some b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___option_op_zsze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : option inst_a -> option inst_a -> bool :=
  fun x y => negb (Eq___option_op_zeze__ x y).

Program Instance Eq___option {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (option a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___option_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___option_op_zsze__ |}.

Local Definition Ord__option_op_zl__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : option inst_a -> option inst_a -> bool :=
  fun a b =>
    match a with
    | None => match b with | None => false | _ => true end
    | Some a1 => match b with | Some b1 => (a1 GHC.Base.< b1) | _ => false end
    end.

Local Definition Ord__option_op_zlze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : option inst_a -> option inst_a -> bool :=
  fun a b => negb (Ord__option_op_zl__ b a).

Local Definition Ord__option_op_zg__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : option inst_a -> option inst_a -> bool :=
  fun a b => Ord__option_op_zl__ b a.

Local Definition Ord__option_op_zgze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : option inst_a -> option inst_a -> bool :=
  fun a b => negb (Ord__option_op_zl__ a b).

Local Definition Ord__option_compare {inst_a : Type} `{GHC.Base.Ord inst_a}
   : option inst_a -> option inst_a -> comparison :=
  fun a b =>
    match a with
    | None => match b with | None => Eq | _ => Lt end
    | Some a1 => match b with | Some b1 => (GHC.Base.compare a1 b1) | _ => Gt end
    end.

Local Definition Ord__option_max {inst_a : Type} `{GHC.Base.Ord inst_a}
   : option inst_a -> option inst_a -> option inst_a :=
  fun x y => if Ord__option_op_zlze__ x y : bool then y else x.

Local Definition Ord__option_min {inst_a : Type} `{GHC.Base.Ord inst_a}
   : option inst_a -> option inst_a -> option inst_a :=
  fun x y => if Ord__option_op_zlze__ x y : bool then x else y.

Program Instance Ord__option {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Ord (option a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__option_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__option_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__option_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__option_op_zgze__ ;
           GHC.Base.compare__ := Ord__option_compare ;
           GHC.Base.max__ := Ord__option_max ;
           GHC.Base.min__ := Ord__option_min |}.

(* External variables:
     Eq Gt Lt None Some Type bool comparison false negb option true GHC.Base.Eq_
     GHC.Base.Ord GHC.Base.compare GHC.Base.compare__ GHC.Base.max__ GHC.Base.min__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlze____ GHC.Base.op_zsze____
*)
