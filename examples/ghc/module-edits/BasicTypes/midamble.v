Require HsToCoq.Err.

Instance Default__SourceText : HsToCoq.Err.Default SourceText :=
  HsToCoq.Err.Build_Default _ NoSourceText.

(* Eq instance needed by Ord__IntWithInf *)
Definition Eq__IntWithInf_op_zeze : IntWithInf -> IntWithInf -> bool :=
  fun a b =>
    match a, b with
    | Int x, Int y => x GHC.Base.== y
    | Infinity, Infinity => true
    | _, _ => false
    end.

#[global]
Instance Eq__IntWithInf : GHC.Base.Eq_ IntWithInf :=
  fun _ k => k {|
    GHC.Base.op_zeze____ := Eq__IntWithInf_op_zeze ;
    GHC.Base.op_zsze____ := fun a b => negb (Eq__IntWithInf_op_zeze a b)
  |}.
Instance Default__FixityDirection : HsToCoq.Err.Default FixityDirection :=
  HsToCoq.Err.Build_Default _ InfixL.

Instance Default__OverlapMode : HsToCoq.Err.Default OverlapMode :=
  HsToCoq.Err.Build_Default _ (NoOverlap HsToCoq.Err.default).
Instance Default__OverlapFlag : HsToCoq.Err.Default OverlapFlag :=
  HsToCoq.Err.Build_Default _ (Mk_OverlapFlag HsToCoq.Err.default HsToCoq.Err.default).
Instance Default__Fixity : HsToCoq.Err.Default Fixity :=
  HsToCoq.Err.Build_Default _ (Mk_Fixity HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
Instance Default__InlinePragma : HsToCoq.Err.Default InlinePragma :=
  HsToCoq.Err.Build_Default _ (Mk_InlinePragma HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
