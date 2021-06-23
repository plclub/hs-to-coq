Instance Default_CallArityRes : HsToCoq.Err.Default CallArityRes := 
HsToCoq.Err.Build_Default _ (HsToCoq.Err.default, HsToCoq.Err.default).


(* ------------------------- mutual recursion hack -------------------- *)

(* ANTALZ: This looks like a good example of structural mutual recursion *) 
Parameter callArityBind1
   : Core.VarSet ->
     CallArityRes ->
     Core.VarSet -> Core.CoreBind -> (CallArityRes * Core.CoreBind)%type.
