(* Stub module for GHC.Core.Opt.Stats *)
Require HsToCoq.Err.

Axiom SimplCount : Type.
Axiom defaultSimplCount : SimplCount.

#[global] Instance Default__SimplCount : HsToCoq.Err.Default SimplCount :=
  HsToCoq.Err.Build_Default _ defaultSimplCount.
