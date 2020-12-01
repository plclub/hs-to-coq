Instance Unpeel_Alt (k : Type) (f : k -> Type) (a : k) : GHC.Prim.Unpeel (Alt k f a) (f a) :=
    GHC.Prim.Build_Unpeel _ _ getAlt Mk_Alt.
