(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Import Core.
Require Import Data.Traversable.
Require Import GHC.Base.
Require GHC.Types.Tickish.
Require Name.
Require UniqSupply.
Require Unique.
Require Util.

(* No type declarations to convert. *)

(* Midamble *)

(* GHC 9.10: Subst is axiomatized in GHC.Core.TyCo.Subst with its own Default instance *)
Require Import GHC.Core.TyCo.Subst.
Require Import AxiomatizedTypes.

(* GHC 9.10: emptySubst is re-exported from GHC.Core.TyCo.Subst *)
Definition emptySubst : GHC.Core.TyCo.Subst.Subst := GHC.Core.TyCo.Subst.emptySubst.

(* GHC 9.10: these are defined in GHC.Core.TyCo.Subst but need Core types *)
Axiom mkEmptySubst : InScopeSet -> GHC.Core.TyCo.Subst.Subst.
Axiom substTyUnchecked : GHC.Core.TyCo.Subst.Subst -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.
Axiom substCo : GHC.Core.TyCo.Subst.Subst -> AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

(* Converted value declarations: *)

Axiom extendIdSubst : GHC.Core.TyCo.Subst.Subst ->
                      Id -> CoreExpr -> GHC.Core.TyCo.Subst.Subst.

Axiom extendIdSubstWithClone : GHC.Core.TyCo.Subst.Subst ->
                               Id -> Id -> GHC.Core.TyCo.Subst.Subst.

Axiom extendIdSubstList : GHC.Core.TyCo.Subst.Subst ->
                          list (Id * CoreExpr)%type -> GHC.Core.TyCo.Subst.Subst.

Axiom extendSubst : GHC.Core.TyCo.Subst.Subst ->
                    Var -> CoreArg -> GHC.Core.TyCo.Subst.Subst.

Axiom extendSubstWithVar : GHC.Core.TyCo.Subst.Subst ->
                           Var -> Var -> GHC.Core.TyCo.Subst.Subst.

Axiom extendSubstList : GHC.Core.TyCo.Subst.Subst ->
                        list (Var * CoreArg)%type -> GHC.Core.TyCo.Subst.Subst.

Axiom lookupIdSubst : forall `{Util.HasDebugCallStack},
                      GHC.Core.TyCo.Subst.Subst -> Id -> CoreExpr.

Axiom lookupIdSubst_maybe : forall `{Util.HasDebugCallStack},
                            GHC.Core.TyCo.Subst.Subst -> Id -> option CoreExpr.

Axiom delBndr : GHC.Core.TyCo.Subst.Subst -> Var -> GHC.Core.TyCo.Subst.Subst.

Axiom delBndrs : GHC.Core.TyCo.Subst.Subst ->
                 list Var -> GHC.Core.TyCo.Subst.Subst.

Axiom mkOpenSubst : InScopeSet ->
                    list (Var * CoreArg)%type -> GHC.Core.TyCo.Subst.Subst.

Axiom substExprSC : forall `{Util.HasDebugCallStack},
                    GHC.Core.TyCo.Subst.Subst -> CoreExpr -> CoreExpr.

Axiom substExpr : forall `{Util.HasDebugCallStack},
                  GHC.Core.TyCo.Subst.Subst -> CoreExpr -> CoreExpr.

Axiom substBindSC : forall `{Util.HasDebugCallStack},
                    GHC.Core.TyCo.Subst.Subst ->
                    CoreBind -> (GHC.Core.TyCo.Subst.Subst * CoreBind)%type.

Axiom substBind : forall `{Util.HasDebugCallStack},
                  GHC.Core.TyCo.Subst.Subst ->
                  CoreBind -> (GHC.Core.TyCo.Subst.Subst * CoreBind)%type.

Axiom deShadowBinds : CoreProgram -> CoreProgram.

Axiom substBndr : GHC.Core.TyCo.Subst.Subst ->
                  Var -> (GHC.Core.TyCo.Subst.Subst * Var)%type.

Axiom substBndrs : forall {f : Type -> Type},
                   forall `{Traversable f},
                   GHC.Core.TyCo.Subst.Subst -> f Var -> (GHC.Core.TyCo.Subst.Subst * f Var)%type.

Axiom substRecBndrs : forall {f : Type -> Type},
                      forall `{Traversable f},
                      GHC.Core.TyCo.Subst.Subst -> f Id -> (GHC.Core.TyCo.Subst.Subst * f Id)%type.

Axiom substIdBndr : String ->
                    GHC.Core.TyCo.Subst.Subst ->
                    GHC.Core.TyCo.Subst.Subst -> Id -> (GHC.Core.TyCo.Subst.Subst * Id)%type.

Axiom cloneIdBndr : GHC.Core.TyCo.Subst.Subst ->
                    UniqSupply.UniqSupply -> Id -> (GHC.Core.TyCo.Subst.Subst * Id)%type.

Axiom cloneIdBndrs : GHC.Core.TyCo.Subst.Subst ->
                     UniqSupply.UniqSupply -> list Id -> (GHC.Core.TyCo.Subst.Subst * list Id)%type.

Axiom cloneBndrs : forall {m : Type -> Type},
                   forall `{UniqSupply.MonadUnique m},
                   GHC.Core.TyCo.Subst.Subst ->
                   list Var -> m (GHC.Core.TyCo.Subst.Subst * list Var)%type.

Axiom cloneBndr : GHC.Core.TyCo.Subst.Subst ->
                  Unique.Unique -> Var -> (GHC.Core.TyCo.Subst.Subst * Var)%type.

Axiom cloneRecIdBndrs : forall {m : Type -> Type},
                        forall `{UniqSupply.MonadUnique m},
                        GHC.Core.TyCo.Subst.Subst ->
                        list Id -> m (GHC.Core.TyCo.Subst.Subst * list Id)%type.

Axiom clone_id : GHC.Core.TyCo.Subst.Subst ->
                 GHC.Core.TyCo.Subst.Subst ->
                 (Id * Unique.Unique)%type -> (GHC.Core.TyCo.Subst.Subst * Id)%type.

Axiom substIdType : GHC.Core.TyCo.Subst.Subst -> Id -> Id.

Axiom substIdInfo : GHC.Core.TyCo.Subst.Subst -> Id -> IdInfo -> option IdInfo.

Axiom substUnfoldingSC : GHC.Core.TyCo.Subst.Subst -> Unfolding -> Unfolding.

Axiom substUnfolding : GHC.Core.TyCo.Subst.Subst -> Unfolding -> Unfolding.

Axiom substIdOcc : GHC.Core.TyCo.Subst.Subst -> Id -> Id.

Axiom substRuleInfo : GHC.Core.TyCo.Subst.Subst -> Id -> RuleInfo -> RuleInfo.

Axiom substRulesForImportedIds : GHC.Core.TyCo.Subst.Subst ->
                                 list CoreRule -> list CoreRule.

Axiom substRule : GHC.Core.TyCo.Subst.Subst ->
                  (Name.Name -> Name.Name) -> CoreRule -> CoreRule.

Axiom substDVarSet : forall `{Util.HasDebugCallStack},
                     GHC.Core.TyCo.Subst.Subst -> DVarSet -> DVarSet.

Axiom substTickish : GHC.Core.TyCo.Subst.Subst ->
                     GHC.Types.Tickish.CoreTickish -> GHC.Types.Tickish.CoreTickish.

(* External variables:
     CoreArg CoreBind CoreExpr CoreProgram CoreRule DVarSet Id IdInfo InScopeSet
     RuleInfo String Traversable Type Unfolding Var list op_zt__ option
     GHC.Core.TyCo.Subst.Subst GHC.Types.Tickish.CoreTickish Name.Name
     UniqSupply.MonadUnique UniqSupply.UniqSupply Unique.Unique
     Util.HasDebugCallStack
*)
