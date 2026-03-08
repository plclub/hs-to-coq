(* Stub module for GHC.Core.Map.Expr *)
Require Core.

Axiom CoreMap : Type -> Type.
Axiom emptyCoreMap : forall {a}, CoreMap a.
Axiom extendCoreMap : forall {a}, CoreMap a -> Core.CoreExpr -> a -> CoreMap a.
Axiom lookupCoreMap : forall {a}, CoreMap a -> Core.CoreExpr -> option a.
Axiom eqCoreExpr : Core.CoreExpr -> Core.CoreExpr -> bool.
