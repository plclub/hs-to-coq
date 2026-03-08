(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require BasicTypes.
Require BooleanFormula.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Foldable.
Require GHC.Base.
Require Name.
Require SrcLoc.
Require Unique.
Require Core.
Import GHC.Base.Notations.

Parameter Class : Type.
Parameter className : Class -> Name.Name.
Parameter classKey : Class -> Unique.Unique.
Parameter classTyVars : Class -> list Core.TyVar.
Parameter classMethods : Class -> list Core.Id.
Parameter classAllSelIds : Class -> list Core.Id.


Local Definition Eq___Class_op_zeze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.== classKey c2.

Local Definition Eq___Class_op_zsze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base./= classKey c2.

Program Instance Eq___Class : GHC.Base.Eq_ Class := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Class_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Class_op_zsze__ |}.

Local Definition Ord__Class_compare : Class -> Class -> comparison :=
  fun c1 c2 => Unique.nonDetCmpUnique (classKey c1) (classKey c2).

Local Definition Ord__Class_op_zl__ : Class -> Class -> bool :=
  fun c1 c2 => match Ord__Class_compare c1 c2 with | Lt => true | _ => false end.

Local Definition Ord__Class_op_zlze__ : Class -> Class -> bool :=
  fun c1 c2 => match Ord__Class_compare c1 c2 with | Gt => false | _ => true end.

Local Definition Ord__Class_op_zg__ : Class -> Class -> bool :=
  fun c1 c2 => match Ord__Class_compare c1 c2 with | Gt => true | _ => false end.

Local Definition Ord__Class_op_zgze__ : Class -> Class -> bool :=
  fun c1 c2 => match Ord__Class_compare c1 c2 with | Lt => false | _ => true end.

Local Definition Ord__Class_min : Class -> Class -> Class :=
  fun x y => if Ord__Class_op_zlze__ x y : bool then x else y.

Local Definition Ord__Class_max : Class -> Class -> Class :=
  fun x y => if Ord__Class_op_zlze__ x y : bool then y else x.

Program Instance Ord__Class : GHC.Base.Ord Class := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Class_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Class_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Class_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Class_op_zgze__ ;
      GHC.Base.compare__ := Ord__Class_compare ;
      GHC.Base.max__ := Ord__Class_max ;
      GHC.Base.min__ := Ord__Class_min |}.

Definition classArity : Class -> BasicTypes.Arity :=
  fun clas => Coq.Lists.List.length (classTyVars clas).
