(* Stub for GHC.Utils.Outputable — we don't translate the pretty-printing infrastructure.
   Outputable is used as a typeclass constraint in many GHC functions; we define it
   trivially so that dependent code compiles. *)

Require Import GHC.Base.

Class Outputable (a : Type) := {}.

(* Provide a default instance so typeclass resolution always succeeds *)
#[global] Instance Outputable__unit : Outputable unit := {}.

Class OutputableBndr (a : Type) := {}.

Class OutputableP (env : Type) (a : Type) := {}.

(* SDoc is the pretty-printing document type — axiomatized *)
Axiom SDoc : Type.

Axiom braces : SDoc -> SDoc.
