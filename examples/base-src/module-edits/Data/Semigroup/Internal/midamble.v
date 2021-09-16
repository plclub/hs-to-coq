Instance Unpeel_Alt (k : Type) (f : k -> Type) (a : k) : HsToCoq.Unpeel.Unpeel (Alt f a) (f a) :=
    HsToCoq.Unpeel.Build_Unpeel _ _ getAlt Mk_Alt.
