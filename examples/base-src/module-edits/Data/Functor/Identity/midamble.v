Instance Unpeel_Identity a : HsToRocq.Unpeel.Unpeel (Identity a) a :=
 HsToRocq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_Identity x => x end) Mk_Identity.
