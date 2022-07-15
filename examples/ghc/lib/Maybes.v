(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Trans.Maybe.
Require Coq.Init.Datatypes.
Require Data.Maybe.
Require GHC.Base.
Require GHC.Err.
Require HsToCoq.Err.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive MaybeErr err val : Type :=
  | Succeeded : val -> MaybeErr err val
  | Failed : err -> MaybeErr err val.

Arguments Succeeded {_} {_} _.

Arguments Failed {_} {_} _.

(* Converted value declarations: *)

Local Definition Functor__MaybeErr_fmap {inst_err}
   : forall {a} {b}, (a -> b) -> MaybeErr inst_err a -> MaybeErr inst_err b :=
  fun {a} {b} =>
    fun f x =>
      match x with
      | Succeeded x => Succeeded (f x)
      | Failed e => Failed e
      end.

Local Definition Functor__MaybeErr_op_zlzd__ {inst_err : Type}
   : forall {a : Type},
     forall {b : Type}, a -> MaybeErr inst_err b -> MaybeErr inst_err a :=
  fun {a : Type} {b : Type} => Functor__MaybeErr_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__MaybeErr {err : Type}
   : GHC.Base.Functor (MaybeErr err) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__MaybeErr_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__MaybeErr_op_zlzd__ |}.

Local Definition Applicative__MaybeErr_op_zlztzg__ {inst_err}
   : forall {a} {b},
     MaybeErr inst_err (a -> b) -> MaybeErr inst_err a -> MaybeErr inst_err b :=
  fun {a} {b} =>
    fun mf mx =>
      match mf with
      | Succeeded f =>
          match mx with
          | Succeeded x => Succeeded (f x)
          | Failed e => Failed e
          end
      | Failed e => Failed e
      end.

Local Definition Applicative__MaybeErr_liftA2 {inst_err : Type}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     MaybeErr inst_err a -> MaybeErr inst_err b -> MaybeErr inst_err c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__MaybeErr_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__MaybeErr_op_ztzg__ {inst_err : Type}
   : forall {a : Type},
     forall {b : Type},
     MaybeErr inst_err a -> MaybeErr inst_err b -> MaybeErr inst_err b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__MaybeErr_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__MaybeErr_pure {inst_err : Type}
   : forall {a : Type}, a -> MaybeErr inst_err a :=
  fun {a : Type} => Succeeded.

Program Instance Applicative__MaybeErr {err : Type}
   : GHC.Base.Applicative (MaybeErr err) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__MaybeErr_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__MaybeErr_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__MaybeErr_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__MaybeErr_pure |}.

Local Definition Monad__MaybeErr_op_zgzgze__ {inst_err : Type}
   : forall {a : Type},
     forall {b : Type},
     MaybeErr inst_err a -> (a -> MaybeErr inst_err b) -> MaybeErr inst_err b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Succeeded v, k => k v
      | Failed e, _ => Failed e
      end.

Local Definition Monad__MaybeErr_op_zgzg__ {inst_err : Type}
   : forall {a : Type},
     forall {b : Type},
     MaybeErr inst_err a -> MaybeErr inst_err b -> MaybeErr inst_err b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__MaybeErr_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__MaybeErr_return_ {inst_err : Type}
   : forall {a : Type}, a -> MaybeErr inst_err a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__MaybeErr {err : Type} : GHC.Base.Monad (MaybeErr err) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__MaybeErr_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} =>
             Monad__MaybeErr_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__MaybeErr_return_ |}.

(* Skipping definition `Maybes.firstJust' *)

(* Skipping definition `Maybes.firstJusts' *)

Definition expectJust {a} `{HsToCoq.Err.Default a}
   : GHC.Base.String -> option a -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Some x => x
    | err, None =>
        GHC.Err.error (Coq.Init.Datatypes.app (GHC.Base.hs_string__ "expectJust ") err)
    end.

Definition whenIsJust {m : Type -> Type} {a : Type} `{GHC.Base.Monad m}
   : option a -> (a -> m unit) -> m unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Some x, f => f x
    | None, _ => GHC.Base.return_ tt
    end.

Definition orElse {a : Type} : option a -> a -> a :=
  GHC.Base.flip Data.Maybe.fromMaybe.

Definition liftMaybeT {m : Type -> Type} {a : Type} `{GHC.Base.Monad m}
   : m a -> Control.Monad.Trans.Maybe.MaybeT m a :=
  fun act => Control.Monad.Trans.Maybe.Mk_MaybeT (GHC.Base.liftM Some act).

(* Skipping definition `Maybes.tryMaybeT' *)

Definition isSuccess {err : Type} {val : Type} : MaybeErr err val -> bool :=
  fun arg_0__ => match arg_0__ with | Succeeded _ => true | Failed _ => false end.

Definition failME {err : Type} {val : Type} : err -> MaybeErr err val :=
  fun e => Failed e.

(* External variables:
     None Some Type bool false option true tt unit Control.Monad.Trans.Maybe.MaybeT
     Control.Monad.Trans.Maybe.Mk_MaybeT Coq.Init.Datatypes.app Data.Maybe.fromMaybe
     GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad GHC.Base.String
     GHC.Base.const GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id
     GHC.Base.liftA2__ GHC.Base.liftM GHC.Base.op_z2218U__ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return_ GHC.Base.return___ GHC.Err.error HsToCoq.Err.Default
*)
