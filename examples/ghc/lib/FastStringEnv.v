(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require FastString.
Require UniqFM.

(* Converted type declarations: *)

Definition FastStringEnv :=
  UniqFM.UniqFM%type.

Definition DFastStringEnv :=
  UniqFM.UniqFM%type.

(* Converted value declarations: *)

Axiom emptyFsEnv : forall {a : Type}, FastStringEnv a.

Axiom unitFsEnv : forall {a : Type},
                  FastString.FastString -> a -> FastStringEnv a.

Axiom extendFsEnv : forall {a : Type},
                    FastStringEnv a -> FastString.FastString -> a -> FastStringEnv a.

Axiom extendFsEnvList : forall {a : Type},
                        FastStringEnv a -> list (FastString.FastString * a)%type -> FastStringEnv a.

Axiom lookupFsEnv : forall {a : Type},
                    FastStringEnv a -> FastString.FastString -> option a.

Axiom alterFsEnv : forall {a : Type},
                   (option a -> option a) ->
                   FastStringEnv a -> FastString.FastString -> FastStringEnv a.

Axiom mkFsEnv : forall {a : Type},
                list (FastString.FastString * a)%type -> FastStringEnv a.

Axiom elemFsEnv : forall {a : Type},
                  FastString.FastString -> FastStringEnv a -> bool.

Axiom plusFsEnv : forall {a : Type},
                  FastStringEnv a -> FastStringEnv a -> FastStringEnv a.

Axiom plusFsEnv_C : forall {a : Type},
                    (a -> a -> a) -> FastStringEnv a -> FastStringEnv a -> FastStringEnv a.

Axiom extendFsEnv_C : forall {a : Type},
                      (a -> a -> a) ->
                      FastStringEnv a -> FastString.FastString -> a -> FastStringEnv a.

Axiom mapFsEnv : forall {elt1 : Type},
                 forall {elt2 : Type},
                 (elt1 -> elt2) -> FastStringEnv elt1 -> FastStringEnv elt2.

Axiom extendFsEnv_Acc : forall {a : Type},
                        forall {b : Type},
                        (a -> b -> b) ->
                        (a -> b) -> FastStringEnv b -> FastString.FastString -> a -> FastStringEnv b.

Axiom extendFsEnvList_C : forall {a : Type},
                          (a -> a -> a) ->
                          FastStringEnv a -> list (FastString.FastString * a)%type -> FastStringEnv a.

Axiom delFromFsEnv : forall {a : Type},
                     FastStringEnv a -> FastString.FastString -> FastStringEnv a.

Axiom delListFromFsEnv : forall {a : Type},
                         FastStringEnv a -> list FastString.FastString -> FastStringEnv a.

Axiom filterFsEnv : forall {elt : Type},
                    (elt -> bool) -> FastStringEnv elt -> FastStringEnv elt.

Axiom lookupFsEnv_NF : forall {a : Type},
                       FastStringEnv a -> FastString.FastString -> a.

Axiom emptyDFsEnv : forall {a : Type}, DFastStringEnv a.

Axiom dFsEnvElts : forall {a : Type}, DFastStringEnv a -> list a.

Axiom mkDFsEnv : forall {a : Type},
                 list (FastString.FastString * a)%type -> DFastStringEnv a.

Axiom lookupDFsEnv : forall {a : Type},
                     DFastStringEnv a -> FastString.FastString -> option a.

(* External variables:
     Type bool list op_zt__ option FastString.FastString UniqFM.UniqFM
*)
