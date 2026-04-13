(* Default values *)
Require Import HsToRocq.Err.
#[global] Instance Default__SrcSpan : Default SrcSpan := Build_Default _ (UnhelpfulSpan default).

#[global] Instance Default__RealSrcLoc : Default RealSrcLoc :=
  Build_Default _ (ASrcLoc (@default _ FastString.instance_FastString_Default)
                   HsToRocq.Err.default HsToRocq.Err.default).

#[global] Instance Default__RealSrcSpan : Default RealSrcSpan :=
  Build_Default _ (RealSrcSpan' (@default _ FastString.instance_FastString_Default)
                   HsToRocq.Err.default  HsToRocq.Err.default
                   HsToRocq.Err.default HsToRocq.Err.default).

#[global] Instance Default__BufSpan : Default BufSpan :=
  Build_Default _ (Mk_BufSpan HsToRocq.Err.default HsToRocq.Err.default).

#[global] Instance Default__PsSpan : Default PsSpan :=
  Build_Default _ (Mk_PsSpan HsToRocq.Err.default HsToRocq.Err.default).

#[global] Instance Default__PsLoc : Default PsLoc :=
  Build_Default _ (Mk_PsLoc HsToRocq.Err.default HsToRocq.Err.default).


(* Field accessors for redefined BufSpan *)
Definition bufSpanStart (arg_0__ : BufSpan) : BufPos :=
  let 'Mk_BufSpan bufSpanStart _ := arg_0__ in bufSpanStart.
Definition bufSpanEnd (arg_0__ : BufSpan) : BufPos :=
  let 'Mk_BufSpan _ bufSpanEnd := arg_0__ in bufSpanEnd.

Import GHC.Base.ManualNotations.

Definition Eq__RealSrcLoc_op_zeze : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b =>
    let 'ASrcLoc a1 a2 a3 := a in
    let 'ASrcLoc b1 b2 b3 := b in
    andb (andb (a1 GHC.Base.== b1) (a2 GHC.Base.== b2)) (a3 GHC.Base.== b3).

#[global]
Program Instance Eq__RealSrcLoc : GHC.Base.Eq_ RealSrcLoc :=
  fun _ k => k {|
    GHC.Base.op_zeze____ := Eq__RealSrcLoc_op_zeze ;
    GHC.Base.op_zsze____ := fun a b => negb (Eq__RealSrcLoc_op_zeze a b)
  |}.

Definition Ord__RealSrcLoc_compare : RealSrcLoc -> RealSrcLoc -> comparison :=
  fun a b =>
    let 'ASrcLoc a1 a2 a3 := a in
    let 'ASrcLoc b1 b2 b3 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => Lt
    | Eq =>
        match (GHC.Base.compare a2 b2) with
        | Lt => Lt
        | Eq => GHC.Base.compare a3 b3
        | Gt => Gt
        end
    | Gt => Gt
    end.

Definition Ord__RealSrcLoc_op_zl : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b => Ord__RealSrcLoc_compare a b GHC.Base.== Lt.

#[global]
Program Instance Ord__RealSrcLoc : GHC.Base.Ord RealSrcLoc :=
  fun _ k => k {|
    GHC.Base.op_zl____ := fun a b => Ord__RealSrcLoc_compare a b GHC.Base.== Lt ;
    GHC.Base.op_zlze____ := fun a b => Ord__RealSrcLoc_compare a b GHC.Base./= Gt ;
    GHC.Base.op_zg____ := fun a b => Ord__RealSrcLoc_compare a b GHC.Base.== Gt ;
    GHC.Base.op_zgze____ := fun a b => Ord__RealSrcLoc_compare a b GHC.Base./= Lt ;
    GHC.Base.compare__ := Ord__RealSrcLoc_compare ;
    GHC.Base.max__ := fun a b => if Ord__RealSrcLoc_compare a b GHC.Base./= Gt : bool then b else a ;
    GHC.Base.min__ := fun a b => if Ord__RealSrcLoc_compare a b GHC.Base./= Gt : bool then a else b
  |}.

Definition Eq__RealSrcSpan_op_zeze : RealSrcSpan -> RealSrcSpan -> bool :=
  fun a b =>
    let 'RealSrcSpan' fa la ca la2 ca2 := a in
    let 'RealSrcSpan' fb lb cb lb2 cb2 := b in
    andb (andb (andb (andb (fa GHC.Base.== fb) (la GHC.Base.== lb)) (ca GHC.Base.== cb))
               (la2 GHC.Base.== lb2)) (ca2 GHC.Base.== cb2).

#[global]
Program Instance Eq__RealSrcSpan : GHC.Base.Eq_ RealSrcSpan :=
  fun _ k => k {|
    GHC.Base.op_zeze____ := Eq__RealSrcSpan_op_zeze ;
    GHC.Base.op_zsze____ := fun a b => negb (Eq__RealSrcSpan_op_zeze a b)
  |}.
