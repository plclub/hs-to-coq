Instance Default_UnVarSet : HsToCoq.Err.Default UnVarSet :=
  HsToCoq.Err.Build_Default _ (Mk_UnVarSet HsToCoq.Err.default).
Instance Default_UnVarGraph : HsToCoq.Err.Default UnVarGraph :=
  HsToCoq.Err.Build_Default _ (Mk_UnVarGraph HsToCoq.Err.default).


Instance Unpeel_UnVarSet : HsToCoq.Unpeel.Unpeel UnVarSet Data.IntSet.Internal.IntSet :=
  HsToCoq.Unpeel.Build_Unpeel _ _ (fun x => match x with | Mk_UnVarSet y => y end) Mk_UnVarSet.
Instance Unpeel_UnVarGraph : HsToCoq.Unpeel.Unpeel UnVarGraph (Bag.Bag Gen) :=
  HsToCoq.Unpeel.Build_Unpeel _ _ (fun x => match x with | Mk_UnVarGraph y => y end) Mk_UnVarGraph.
