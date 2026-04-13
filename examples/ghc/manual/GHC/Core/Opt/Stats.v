(* Stub module for GHC.Core.Opt.Stats *)
Require HsToRocq.Err.

Axiom SimplCount : Type.
Axiom defaultSimplCount : SimplCount.

#[global] Instance Default__SimplCount : HsToRocq.Err.Default SimplCount :=
  HsToRocq.Err.Build_Default _ defaultSimplCount.
