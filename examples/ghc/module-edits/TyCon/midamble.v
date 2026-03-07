(* ---- TyCon midamble ----- *)
#[global] Instance Default__AlgTyConFlav : Err.Default AlgTyConFlav :=
  Err.Build_Default _ (VanillaAlgTyCon Err.default).
#[global] Instance Default__RuntimRepInfo : Err.Default RuntimeRepInfo :=
  Err.Build_Default _ NoRRI.



