(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.

(* Converted type declarations: *)

Record MonadTrans__Dict (t : (Type -> Type) -> Type -> Type) :=
  MonadTrans__Dict_Build {
  lift__ : forall {m : Type -> Type},
  forall {a : Type}, forall `{GHC.Base.Monad m}, m a -> t m a }.

Definition MonadTrans (t : (Type -> Type) -> Type -> Type) :=
  forall r__, (MonadTrans__Dict t -> r__) -> r__.
Existing Class MonadTrans.

Definition lift `{g__0__ : MonadTrans t}
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, m a -> t m a :=
  g__0__ _ (lift__ t).

(* No value declarations to convert. *)

(* External variables:
     Type GHC.Base.Monad
*)
