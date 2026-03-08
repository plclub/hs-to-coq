(* GHC 9.10: Subst is axiomatized in GHC.Core.TyCo.Subst with its own Default instance *)
Require Import GHC.Core.TyCo.Subst.
Require Import AxiomatizedTypes.

(* GHC 9.10: emptySubst is re-exported from GHC.Core.TyCo.Subst *)
Definition emptySubst : GHC.Core.TyCo.Subst.Subst := GHC.Core.TyCo.Subst.emptySubst.

(* GHC 9.10: these are defined in GHC.Core.TyCo.Subst but need Core types *)
Axiom mkEmptySubst : InScopeSet -> GHC.Core.TyCo.Subst.Subst.
Axiom substTyUnchecked : GHC.Core.TyCo.Subst.Subst -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.
Axiom substCo : GHC.Core.TyCo.Subst.Subst -> AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.
