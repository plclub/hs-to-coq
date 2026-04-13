Instance Unpeel_Alt (k : Type) (f : k -> Type) (a : k) : HsToRocq.Unpeel.Unpeel (Alt f a) (f a) :=
    HsToRocq.Unpeel.Build_Unpeel _ _ getAlt Mk_Alt.
