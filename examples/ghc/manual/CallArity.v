(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require Core.
Require UnVarGraph.

(* Converted type declarations: *)

#[global] Definition CallArityRes :=
  (UnVarGraph.UnVarGraph * Core.VarEnv BasicTypes.Arity)%type%type.

(* Midamble *)

#[global] Instance Default_CallArityRes : HsToRocq.Err.Default CallArityRes :=
HsToRocq.Err.Build_Default _ (HsToRocq.Err.default, HsToRocq.Err.default).


(* ------------------------- mutual recursion hack -------------------- *)

(* ANTALZ: This looks like a good example of structural mutual recursion *) 
Parameter callArityBind1
   : Core.VarSet ->
     CallArityRes ->
     Core.VarSet -> Core.CoreBind -> (CallArityRes * Core.CoreBind)%type.

(* Converted value declarations: *)

Axiom callArityAnalProgram : Core.CoreProgram -> Core.CoreProgram.

Axiom callArityTopLvl : list Core.Var ->
                        Core.VarSet -> list Core.CoreBind -> (CallArityRes * list Core.CoreBind)%type.

Axiom callArityRHS : Core.CoreExpr -> Core.CoreExpr.

Axiom callArityAnal : BasicTypes.Arity ->
                      Core.VarSet -> Core.CoreExpr -> (CallArityRes * Core.CoreExpr)%type.

Axiom isInteresting : Core.Var -> bool.

Axiom interestingBinds : Core.CoreBind -> list Core.Var.

Axiom boringBinds : Core.CoreBind -> Core.VarSet.

Axiom addInterestingBinds : Core.VarSet -> Core.CoreBind -> Core.VarSet.

Axiom callArityBind : Core.VarSet ->
                      CallArityRes ->
                      Core.VarSet -> Core.CoreBind -> (CallArityRes * Core.CoreBind)%type.

Axiom callArityRecEnv : bool ->
                        list (Core.Var * CallArityRes)%type -> CallArityRes -> CallArityRes.

Axiom trimArity : Core.Id -> BasicTypes.Arity -> BasicTypes.Arity.

Axiom emptyArityRes : CallArityRes.

Axiom unitArityRes : Core.Var -> BasicTypes.Arity -> CallArityRes.

Axiom resDelList : list Core.Var -> CallArityRes -> CallArityRes.

Axiom resDel : Core.Var -> CallArityRes -> CallArityRes.

Axiom domRes : CallArityRes -> UnVarGraph.UnVarSet.

Axiom lookupCallArityRes : CallArityRes ->
                           Core.Var -> (BasicTypes.Arity * bool)%type.

Axiom calledWith : CallArityRes -> Core.Var -> UnVarGraph.UnVarSet.

Axiom addCrossCoCalls : UnVarGraph.UnVarSet ->
                        UnVarGraph.UnVarSet -> CallArityRes -> CallArityRes.

Axiom calledMultipleTimes : CallArityRes -> CallArityRes.

Axiom both : CallArityRes -> CallArityRes -> CallArityRes.

Axiom lubRes : CallArityRes -> CallArityRes -> CallArityRes.

Axiom lubArityEnv : Core.VarEnv BasicTypes.Arity ->
                    Core.VarEnv BasicTypes.Arity -> Core.VarEnv BasicTypes.Arity.

Axiom lubRess : list CallArityRes -> CallArityRes.

(* External variables:
     bool list op_zt__ BasicTypes.Arity Core.CoreBind Core.CoreExpr Core.CoreProgram
     Core.Id Core.Var Core.VarEnv Core.VarSet UnVarGraph.UnVarGraph
     UnVarGraph.UnVarSet
*)
