(* Stub module for GHC.Core.TyCo.Subst *)

Require Import HsToCoq.Err.
Require Import AxiomatizedTypes.

Axiom Subst : Type.
#[global] Instance Default__Subst : Default Subst. Admitted.

Axiom emptySubst : Subst.

(* GHC 9.10: functions that use Core types — parameterized to avoid circular deps *)
Axiom mkEmptySubst : forall {InScopeSet_ : Type}, InScopeSet_ -> Subst.
Axiom substTyUnchecked : Subst -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.
Axiom substCo : forall {Coercion_ : Type}, Subst -> Coercion_ -> Coercion_.
