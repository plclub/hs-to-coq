Instance Unpeel_IgnorePackageFlag : HsToRocq.Unpeel.Unpeel IgnorePackageFlag GHC.Base.String :=
  HsToRocq.Unpeel.Build_Unpeel _ _ (fun x => match x with | IgnorePackage y => y end) IgnorePackage.


#[global] Instance Default__DynFlags
   : HsToRocq.Err.Default DynFlags.
Admitted.
