Require Import GHC.Prim.

Instance Default_Constant {k} {a : Type} {b : k} `{HsToCoq.Err.Default a} : HsToCoq.Err.Default (Constant a b) := Err.Build_Default _ (Mk_Constant Err.default).

Instance Unpeel_Constant {k} {a : Type} {b : k} : Unpeel (Constant a b) a :=
  Build_Unpeel _ _ getConstant Mk_Constant.
