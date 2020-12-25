Require ZArith.BinInt.

Instance Default_Bag {a} : HsToCoq.Err.Default (Bag a):=
  HsToCoq.Err.Build_Default _ EmptyBag.
