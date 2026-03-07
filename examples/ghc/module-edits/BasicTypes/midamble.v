Require HsToCoq.Err.

#[global] Instance Default__SourceText : HsToCoq.Err.Default SourceText :=
  HsToCoq.Err.Build_Default _ NoSourceText.

#[global] Instance Default__TyConFlavour {tc} : HsToCoq.Err.Default (TyConFlavour tc) :=
  HsToCoq.Err.Build_Default _ ClassFlavour.
