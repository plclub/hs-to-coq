(* We should be able to automatically generate these *)

Instance Unpeel_StateR {s}{a} : HsToRocq.Unpeel.Unpeel (StateR s a) (s -> (s * a)%type)
:= HsToRocq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_StateR x => x end) Mk_StateR.
Instance Unpeel_StateL {s}{a} : HsToRocq.Unpeel.Unpeel (StateL s a) (s -> (s * a)%type)
:= HsToRocq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_StateL x => x end) Mk_StateL.
Instance Unpeel_Min {a} : HsToRocq.Unpeel.Unpeel (Min a) (option a)
:= HsToRocq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_Min x => x end) Mk_Min.
Instance Unpeel_Max {a} : HsToRocq.Unpeel.Unpeel (Max a) (option a)
:= HsToRocq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_Max x => x end) Mk_Max.
