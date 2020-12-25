Require HsToCoq.Err.

Instance Default__OverlapMode : HsToCoq.Err.Default OverlapMode :=
  HsToCoq.Err.Build_Default _ (NoOverlap HsToCoq.Err.default).
Instance Default__OverlapFlag : HsToCoq.Err.Default OverlapFlag :=
  HsToCoq.Err.Build_Default _ (Mk_OverlapFlag HsToCoq.Err.default HsToCoq.Err.default).
Instance Default__Fixity : HsToCoq.Err.Default Fixity :=
  HsToCoq.Err.Build_Default _ (Mk_Fixity HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
Instance Default__InlinePragma : HsToCoq.Err.Default InlinePragma :=
  HsToCoq.Err.Build_Default _ (Mk_InlinePragma HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).
