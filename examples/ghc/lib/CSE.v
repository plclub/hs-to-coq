(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require String.
Import String.StringSyntax.

(* Converted imports: *)

Require BasicTypes.
Require Core.
Require Data.Traversable.
Require GHC.Core.Map.Expr.

(* Converted type declarations: *)

Inductive CSEnv : Type :=
  | CS (cs_subst : Core.Subst) (cs_map : GHC.Core.Map.Expr.CoreMap Core.OutExpr)
  (cs_rec_map : GHC.Core.Map.Expr.CoreMap Core.OutExpr)
   : CSEnv.

#[global] Definition cs_map (arg_0__ : CSEnv) :=
  let 'CS _ cs_map _ := arg_0__ in
  cs_map.

#[global] Definition cs_rec_map (arg_0__ : CSEnv) :=
  let 'CS _ _ cs_rec_map := arg_0__ in
  cs_rec_map.

#[global] Definition cs_subst (arg_0__ : CSEnv) :=
  let 'CS cs_subst _ _ := arg_0__ in
  cs_subst.

(* Midamble *)

Require NestedRecursionHelpers.

(* default = emptyCSEnv *)
#[global] Instance Default__CSEnv : HsToRocq.Err.Default CSEnv := {| HsToRocq.Err.default := CS Core.emptySubst GHC.Core.Map.Expr.emptyCoreMap GHC.Core.Map.Expr.emptyCoreMap |}.

(* Converted value declarations: *)

Axiom cseProgram : Core.CoreProgram -> Core.CoreProgram.

Axiom cseBind : BasicTypes.TopLevelFlag ->
                CSEnv -> Core.CoreBind -> (CSEnv * Core.CoreBind)%type.

Axiom cse_bind : BasicTypes.TopLevelFlag ->
                 CSEnv ->
                 CSEnv ->
                 (Core.InId * Core.InExpr)%type ->
                 Core.OutId -> (CSEnv * (Core.OutId * Core.OutExpr)%type)%type.

Axiom delayInlining : BasicTypes.TopLevelFlag -> Core.Id -> Core.Id.

Axiom extendCSEnvWithBinding : CSEnv ->
                               Core.InVar -> Core.OutId -> Core.OutExpr -> bool -> (CSEnv * Core.OutId)%type.

Axiom noCSE : Core.InId -> bool.

Axiom tryForCSE : CSEnv -> Core.InExpr -> Core.OutExpr.

Axiom try_for_cse : CSEnv -> Core.InExpr -> (bool * Core.OutExpr)%type.

Axiom cseOneExpr : Core.InExpr -> Core.OutExpr.

Axiom cseExpr : CSEnv -> Core.InExpr -> Core.OutExpr.

Axiom cseCase : CSEnv ->
                Core.InExpr -> Core.InId -> Core.InType -> list Core.InAlt -> Core.OutExpr.

Axiom combineAlts : list Core.OutAlt -> list Core.OutAlt.

Axiom emptyCSEnv : CSEnv.

Axiom lookupCSEnv : CSEnv -> Core.OutExpr -> option Core.OutExpr.

Axiom extendCSEnv : CSEnv -> Core.OutExpr -> Core.OutExpr -> CSEnv.

Axiom extendCSRecEnv : CSEnv ->
                       Core.OutId -> Core.OutExpr -> Core.OutExpr -> CSEnv.

Axiom lookupCSRecEnv : CSEnv ->
                       Core.OutId -> Core.OutExpr -> option Core.OutExpr.

Axiom csEnvSubst : CSEnv -> Core.Subst.

Axiom lookupSubst : CSEnv -> Core.Id -> Core.OutExpr.

Axiom extendCSSubst : CSEnv -> Core.Id -> Core.CoreExpr -> CSEnv.

Axiom addBinder : CSEnv -> Core.Var -> (CSEnv * Core.Var)%type.

Axiom addBinders : CSEnv -> list Core.Var -> (CSEnv * list Core.Var)%type.

Axiom addRecBinders : forall {f},
                      forall `{Data.Traversable.Traversable f},
                      CSEnv -> f Core.Id -> (CSEnv * f Core.Id)%type.

(* External variables:
     bool list op_zt__ option BasicTypes.TopLevelFlag Core.CoreBind Core.CoreExpr
     Core.CoreProgram Core.Id Core.InAlt Core.InExpr Core.InId Core.InType Core.InVar
     Core.OutAlt Core.OutExpr Core.OutId Core.Subst Core.Var
     Data.Traversable.Traversable GHC.Core.Map.Expr.CoreMap
*)
