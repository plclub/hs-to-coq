Require Import HsToRocq.Err.

#[global] Instance Default__FieldSelectors_G : Default FieldSelectors :=
  Build_Default _ Mk_FieldSelectors.
#[global] Instance Default__DuplicateRecordFields_G : Default DuplicateRecordFields :=
  Build_Default _ Mk_DuplicateRecordFields.
#[global] Instance Default__FieldLabel_G : Default FieldLabel :=
  Build_Default _ (Mk_FieldLabel default default default).
