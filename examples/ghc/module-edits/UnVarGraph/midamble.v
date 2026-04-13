#[global] Instance Default_UnVarSet : HsToRocq.Err.Default UnVarSet :=
  HsToRocq.Err.Build_Default _ (Mk_UnVarSet HsToRocq.Err.default).
#[global] Instance Default_UnVarGraph : HsToRocq.Err.Default UnVarGraph :=
  HsToRocq.Err.Build_Default _ (CG (Mk_UnVarSet HsToRocq.Err.default)).

Instance Unpeel_UnVarSet : HsToRocq.Unpeel.Unpeel UnVarSet Data.IntSet.Internal.IntSet :=
  HsToRocq.Unpeel.Build_Unpeel _ _ (fun x => match x with | Mk_UnVarSet y => y end) Mk_UnVarSet.
