Require Import GHC.Prim.

Instance Default_Constant {k} {a : Type} {b : k} `{HsToRocq.Err.Default a} : HsToRocq.Err.Default (Constant a b) := Err.Build_Default _ (Mk_Constant Err.default).

Instance Unpeel_Constant {k} {a : Type} {b : k} : HsToRocq.Unpeel.Unpeel (Constant a b) a :=
  HsToRocq.Unpeel.Build_Unpeel _ _ getConstant Mk_Constant.
