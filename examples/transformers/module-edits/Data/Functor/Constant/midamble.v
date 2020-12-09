Require Import GHC.Prim.
Require GHC.Err.

Instance Default_Constant {k} {a : Type} {b : k} `{GHC.Err.Default a} : GHC.Err.Default (Constant a b) := Err.Build_Default _ (Mk_Constant Err.default).

Instance Unpeel_Constant {k} {a : Type} {b : k} : Unpeel (Constant a b) a :=
  Build_Unpeel _ _ getConstant Mk_Constant.
