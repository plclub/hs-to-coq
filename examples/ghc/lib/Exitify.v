(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require Core.
Require CoreUtils.
Require Data.Bifunctor.
Require Data.Foldable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Utils.Monad.State.Strict.
Require Id.
Require Util.
Import GHC.Base.Notations.

(* Converted type declarations: *)

#[global] Definition ExitifyM :=
  (GHC.Utils.Monad.State.Strict.State (list (Core.JoinId *
                                             Core.CoreExpr)%type))%type.

(* Converted value declarations: *)

Axiom exitifyRec : Core.InScopeSet ->
                   list (Core.Var * Core.CoreExpr)%type -> list Core.CoreBind.

#[global] Definition exitifyProgram : Core.CoreProgram -> Core.CoreProgram :=
  fun binds =>
    let go : Core.InScopeSet -> Core.CoreExpr -> Core.CoreExpr :=
      fix go (arg_0__ : Core.InScopeSet) (arg_1__ : Core.CoreExpr) : Core.CoreExpr
        := match arg_0__, arg_1__ with
           | _, (Core.Mk_Var _ as e) => e
           | _, (Core.Lit _ as e) => e
           | _, (Core.Mk_Type _ as e) => e
           | _, (Core.Mk_Coercion _ as e) => e
           | in_scope, Core.Cast e' c => Core.Cast (go in_scope e') c
           | in_scope, Core.App e1 e2 => Core.App (go in_scope e1) (go in_scope e2)
           | in_scope, Core.Lam v e' =>
               let in_scope' := Core.extendInScopeSet in_scope v in
               Core.Lam v (go in_scope' e')
           | in_scope, Core.Case scrut bndr ty alts =>
               let in_scope1 := Core.extendInScopeSet in_scope bndr in
               let go_alt :=
                 fun '(Core.Mk_Alt dc pats rhs) =>
                   let in_scope' := Core.extendInScopeSetList in_scope1 pats in
                   Core.Mk_Alt dc pats (go in_scope' rhs) in
               Core.Case (go in_scope scrut) bndr ty (GHC.Base.map go_alt alts)
           | in_scope, Core.Let (Core.NonRec bndr rhs) body =>
               let in_scope' := Core.extendInScopeSet in_scope bndr in
               Core.Let (Core.NonRec bndr (go in_scope rhs)) (go in_scope' body)
           | in_scope, Core.Let (Core.Rec pairs) body =>
               let in_scope' := CoreUtils.extendInScopeSetBind in_scope (Core.Rec pairs) in
               let pairs' := Util.mapSnd (go in_scope') pairs in
               let body' := go in_scope' body in
               let is_join_rec :=
                 Data.Foldable.any (Id.isJoinId GHC.Base.∘ Data.Tuple.fst) pairs in
               if is_join_rec : bool then Core.mkLets (exitifyRec in_scope' pairs') body' else
               Core.Let (Core.Rec pairs') body'
           end in
    let in_scope_toplvl :=
      CoreUtils.extendInScopeSetBndrs Core.emptyInScopeSet binds in
    let goTopLvl :=
      fun arg_22__ =>
        match arg_22__ with
        | Core.NonRec v e => Core.NonRec v (go in_scope_toplvl e)
        | Core.Rec pairs =>
            Core.Rec (GHC.Base.map (Data.Bifunctor.second (go in_scope_toplvl)) pairs)
        end in
    GHC.Base.map goTopLvl binds.

Axiom mkExitJoinId : Core.InScopeSet ->
                     AxiomatizedTypes.Type_ -> BasicTypes.JoinArity -> ExitifyM Core.JoinId.

#[global] Definition addExit
   : Core.InScopeSet ->
     BasicTypes.JoinArity -> Core.CoreExpr -> ExitifyM Core.JoinId :=
  fun in_scope join_arity rhs =>
    let ty := CoreUtils.exprType rhs in
    mkExitJoinId in_scope ty join_arity GHC.Base.>>=
    (fun v =>
       GHC.Utils.Monad.State.Strict.get GHC.Base.>>=
       (fun fs =>
          GHC.Utils.Monad.State.Strict.put (cons (pair v rhs) fs) GHC.Base.>>
          GHC.Base.return_ v)).

(* External variables:
     bool cons list op_zt__ pair AxiomatizedTypes.Type_ BasicTypes.JoinArity Core.App
     Core.Case Core.Cast Core.CoreBind Core.CoreExpr Core.CoreProgram Core.InScopeSet
     Core.JoinId Core.Lam Core.Let Core.Lit Core.Mk_Alt Core.Mk_Coercion Core.Mk_Type
     Core.Mk_Var Core.NonRec Core.Rec Core.Var Core.emptyInScopeSet
     Core.extendInScopeSet Core.extendInScopeSetList Core.mkLets CoreUtils.exprType
     CoreUtils.extendInScopeSetBind CoreUtils.extendInScopeSetBndrs
     Data.Bifunctor.second Data.Foldable.any Data.Tuple.fst GHC.Base.map
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.return_
     GHC.Utils.Monad.State.Strict.State GHC.Utils.Monad.State.Strict.get
     GHC.Utils.Monad.State.Strict.put Id.isJoinId Util.mapSnd
*)
