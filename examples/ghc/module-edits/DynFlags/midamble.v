Instance Unpeel_IgnorePackageFlag : HsToCoq.Unpeel.Unpeel IgnorePackageFlag GHC.Base.String :=
  HsToCoq.Unpeel.Build_Unpeel _ _ (fun x => match x with | IgnorePackage y => y end) IgnorePackage.


Instance Default__DynFlags
   : HsToCoq.Err.Default DynFlags.
Admitted.
