Require Import HsToCoq.Err.

Instance Default__OccName : Default OccName := 
    Build_Default _ (Mk_OccName default default).
