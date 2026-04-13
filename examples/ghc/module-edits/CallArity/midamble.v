#[global] Instance Default_CallArityRes : HsToRocq.Err.Default CallArityRes :=
HsToRocq.Err.Build_Default _ (HsToRocq.Err.default, HsToRocq.Err.default).


(* ------------------------- mutual recursion hack -------------------- *)

(* ANTALZ: This looks like a good example of structural mutual recursion *) 
Parameter callArityBind1
   : Core.VarSet ->
     CallArityRes ->
     Core.VarSet -> Core.CoreBind -> (CallArityRes * Core.CoreBind)%type.
