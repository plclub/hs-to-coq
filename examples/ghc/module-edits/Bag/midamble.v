Require ZArith.BinInt.

#[global] Instance Default_Bag {a} : HsToRocq.Err.Default (Bag a):=
  HsToRocq.Err.Build_Default _ EmptyBag.
