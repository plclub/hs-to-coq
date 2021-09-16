Require Import GHC.Prim.

Instance Default_Constant {k} {a : Type} {b : k} `{HsToCoq.Err.Default a} : HsToCoq.Err.Default (Constant a b) := Err.Build_Default _ (Mk_Constant Err.default).

Instance Unpeel_Constant {k} {a : Type} {b : k} : HsToCoq.Unpeel.Unpeel (Constant a b) a :=
  HsToCoq.Unpeel.Build_Unpeel _ _ getConstant Mk_Constant.
