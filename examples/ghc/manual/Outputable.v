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
Axiom colon : SDoc.
Axiom NamePprCtx : Type.

(* GHC 9.10: JoinPointHood moved from BasicTypes to a new GHC.Types.Basic *)
Inductive JoinPointHood : Type :=
  | NotJoinPoint : JoinPointHood
  | JoinPoint : nat -> JoinPointHood.

Require Import HsToCoq.Err.
#[global] Instance Default__JoinPointHood : Default JoinPointHood :=
  Build_Default _ NotJoinPoint.

#[global] Definition isJoinPoint : JoinPointHood -> bool :=
  fun jph => match jph with | JoinPoint _ => true | NotJoinPoint => false end.

#[global] Instance Eq___JoinPointHood : Eq_ JoinPointHood :=
  fun _ k => k (Eq___Dict_Build _
    (fun x y => match x, y with
    | NotJoinPoint, NotJoinPoint => true
    | JoinPoint n, JoinPoint m => Nat.eqb n m
    | _, _ => false
    end)
    (fun x y => match x, y with
    | NotJoinPoint, NotJoinPoint => false
    | JoinPoint n, JoinPoint m => negb (Nat.eqb n m)
    | _, _ => true
    end)).
