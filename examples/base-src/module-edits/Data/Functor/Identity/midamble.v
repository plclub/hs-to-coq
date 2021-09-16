Instance Unpeel_Identity a : HsToCoq.Unpeel.Unpeel (Identity a) a :=
 HsToCoq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_Identity x => x end) Mk_Identity.
