(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Fail.
Require Control.Monad.Signatures.
Require Control.Monad.Trans.Class.
Require Data.Functor.Identity.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive ReaderT {k : Type} (r : Type) (m : k -> Type) (a : k) : Type :=
  | Mk_ReaderT (runReaderT : r -> m a) : ReaderT r m a.

Definition Reader r :=
  (ReaderT r Data.Functor.Identity.Identity)%type.

Arguments Mk_ReaderT {_} {_} {_} {_} _.

Definition runReaderT {k : Type} {r : Type} {m : k -> Type} {a : k} (arg_0__
    : ReaderT r m a) :=
  let 'Mk_ReaderT runReaderT := arg_0__ in
  runReaderT.

(* Converted value declarations: *)

Definition mapReaderT {k1 : Type} {k2 : Type} {m : k2 -> Type} {a : k2} {n
   : k1 -> Type} {b : k1} {r : Type}
   : (m a -> n b) -> ReaderT r m a -> ReaderT r n b :=
  fun f m => Mk_ReaderT (f GHC.Base.∘ runReaderT m).

Local Definition Functor__ReaderT_fmap {inst_m : Type -> Type} {inst_r : Type}
  `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> ReaderT inst_r inst_m a -> ReaderT inst_r inst_m b :=
  fun {a : Type} {b : Type} => fun f => mapReaderT (GHC.Base.fmap f).

Local Definition Functor__ReaderT_op_zlzd__ {inst_m : Type -> Type} {inst_r
   : Type} `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type}, a -> ReaderT inst_r inst_m b -> ReaderT inst_r inst_m a :=
  fun {a : Type} {b : Type} =>
    fun x v => mapReaderT (fun arg_0__ => x GHC.Base.<$ arg_0__) v.

Program Instance Functor__ReaderT {m : Type -> Type} {r : Type}
  `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (ReaderT r m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__ReaderT_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__ReaderT_op_zlzd__ |}.

Local Definition Applicative__ReaderT_op_zlztzg__ {inst_m : Type -> Type}
  {inst_r : Type} `{(GHC.Base.Applicative inst_m)}
   : forall {a : Type},
     forall {b : Type},
     ReaderT inst_r inst_m (a -> b) ->
     ReaderT inst_r inst_m a -> ReaderT inst_r inst_m b :=
  fun {a : Type} {b : Type} =>
    fun f v => Mk_ReaderT (fun r => runReaderT f r GHC.Base.<*> runReaderT v r).

Local Definition Applicative__ReaderT_liftA2 {inst_m : Type -> Type} {inst_r
   : Type} `{(GHC.Base.Applicative inst_m)}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     ReaderT inst_r inst_m a -> ReaderT inst_r inst_m b -> ReaderT inst_r inst_m c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__ReaderT_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__ReaderT_op_ztzg__ {inst_m : Type -> Type} {inst_r
   : Type} `{(GHC.Base.Applicative inst_m)}
   : forall {a : Type},
     forall {b : Type},
     ReaderT inst_r inst_m a -> ReaderT inst_r inst_m b -> ReaderT inst_r inst_m b :=
  fun {a : Type} {b : Type} =>
    fun u v => Mk_ReaderT (fun r => runReaderT u r GHC.Base.*> runReaderT v r).

Definition liftReaderT {k} {m : k -> Type} {r : Type} {a : k}
   : m a -> ReaderT r m a :=
  fun m => Mk_ReaderT (GHC.Base.const m).

Local Definition Applicative__ReaderT_pure {inst_m : Type -> Type} {inst_r
   : Type} `{(GHC.Base.Applicative inst_m)}
   : forall {a : Type}, a -> ReaderT inst_r inst_m a :=
  fun {a : Type} => liftReaderT GHC.Base.∘ GHC.Base.pure.

Program Instance Applicative__ReaderT {m : Type -> Type} {r : Type}
  `{(GHC.Base.Applicative m)}
   : GHC.Base.Applicative (ReaderT r m) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__ReaderT_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__ReaderT_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__ReaderT_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__ReaderT_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Monad.Trans.Reader.Alternative__ReaderT' *)

Local Definition Monad__ReaderT_op_zgzg__ {inst_m : Type -> Type} {inst_r
   : Type} `{(GHC.Base.Monad inst_m)}
   : forall {a : Type},
     forall {b : Type},
     ReaderT inst_r inst_m a -> ReaderT inst_r inst_m b -> ReaderT inst_r inst_m b :=
  fun {a : Type} {b : Type} => _GHC.Base.*>_.

Local Definition Monad__ReaderT_op_zgzgze__ {inst_m : Type -> Type} {inst_r
   : Type} `{(GHC.Base.Monad inst_m)}
   : forall {a : Type},
     forall {b : Type},
     ReaderT inst_r inst_m a ->
     (a -> ReaderT inst_r inst_m b) -> ReaderT inst_r inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m k =>
      Mk_ReaderT (fun r => runReaderT m r GHC.Base.>>= (fun a => runReaderT (k a) r)).

Local Definition Monad__ReaderT_return_ {inst_m : Type -> Type} {inst_r : Type}
  `{(GHC.Base.Monad inst_m)}
   : forall {a : Type}, a -> ReaderT inst_r inst_m a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__ReaderT {m : Type -> Type} {r : Type} `{(GHC.Base.Monad
   m)}
   : GHC.Base.Monad (ReaderT r m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__ReaderT_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} =>
             Monad__ReaderT_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__ReaderT_return_ |}.

Local Definition MonadTrans__ReaderT_lift {inst_r : Type}
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, m a -> ReaderT inst_r m a :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} => liftReaderT.

Program Instance MonadTrans__ReaderT {r : Type}
   : Control.Monad.Trans.Class.MonadTrans (ReaderT r) :=
  fun _ k__ =>
    k__ {| Control.Monad.Trans.Class.lift__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             MonadTrans__ReaderT_lift |}.

Local Definition MonadFail__ReaderT_fail {inst_m : Type -> Type} {inst_r : Type}
  `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a : Type}, GHC.Base.String -> ReaderT inst_r inst_m a :=
  fun {a : Type} =>
    fun msg => Control.Monad.Trans.Class.lift (Control.Monad.Fail.fail msg).

Program Instance MonadFail__ReaderT {m : Type -> Type} {r : Type}
  `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (ReaderT r m) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun {a : Type} =>
             MonadFail__ReaderT_fail |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Control.Monad.Trans.Reader.MonadPlus__ReaderT' *)

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Control.Monad.Trans.Reader.MonadFix__ReaderT' *)

(* Skipping all instances of class `Control.Monad.IO.Class.MonadIO', including
   `Control.Monad.Trans.Reader.MonadIO__ReaderT' *)

(* Skipping all instances of class `Control.Monad.Zip.MonadZip', including
   `Control.Monad.Trans.Reader.MonadZip__ReaderT' *)

Definition reader {m : Type -> Type} {r : Type} {a : Type} `{GHC.Base.Monad m}
   : (r -> a) -> ReaderT r m a :=
  fun f => Mk_ReaderT (GHC.Base.return_ GHC.Base.∘ f).

Definition runReader {r : Type} {a : Type} : Reader r a -> r -> a :=
  fun m => Data.Functor.Identity.runIdentity GHC.Base.∘ runReaderT m.

Definition mapReader {a : Type} {b : Type} {r : Type}
   : (a -> b) -> Reader r a -> Reader r b :=
  fun f =>
    mapReaderT (Data.Functor.Identity.Mk_Identity GHC.Base.∘
                (f GHC.Base.∘ Data.Functor.Identity.runIdentity)).

Definition withReaderT {k : Type} {r' : Type} {r : Type} {m : k -> Type} {a : k}
   : (r' -> r) -> ReaderT r m a -> ReaderT r' m a :=
  fun f m => Mk_ReaderT (runReaderT m GHC.Base.∘ f).

Definition withReader {r' : Type} {r : Type} {a : Type}
   : (r' -> r) -> Reader r a -> Reader r' a :=
  withReaderT.

Definition ask {m : Type -> Type} {r : Type} `{GHC.Base.Monad m}
   : ReaderT r m r :=
  Mk_ReaderT GHC.Base.return_.

Definition local {k : Type} {r : Type} {m : k -> Type} {a : k}
   : (r -> r) -> ReaderT r m a -> ReaderT r m a :=
  withReaderT.

Definition asks {m : Type -> Type} {r : Type} {a : Type} `{GHC.Base.Monad m}
   : (r -> a) -> ReaderT r m a :=
  fun f => Mk_ReaderT (GHC.Base.return_ GHC.Base.∘ f).

Definition liftCallCC {m : Type -> Type} {a : Type} {b : Type} {r : Type}
   : Control.Monad.Signatures.CallCC m a b ->
     Control.Monad.Signatures.CallCC (ReaderT r m) a b :=
  fun callCC f =>
    Mk_ReaderT (fun r =>
                  callCC (fun c =>
                            runReaderT (f (Mk_ReaderT GHC.Base.∘ (GHC.Base.const GHC.Base.∘ c))) r)).

(* Skipping definition `Control.Monad.Trans.Reader.liftCatch' *)

(* External variables:
     Type Control.Monad.Fail.MonadFail Control.Monad.Fail.fail
     Control.Monad.Fail.fail__ Control.Monad.Signatures.CallCC
     Control.Monad.Trans.Class.MonadTrans Control.Monad.Trans.Class.lift
     Control.Monad.Trans.Class.lift__ Data.Functor.Identity.Identity
     Data.Functor.Identity.Mk_Identity Data.Functor.Identity.runIdentity
     GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad GHC.Base.String
     GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.liftA2__
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__
     GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____ GHC.Base.op_ztzg__
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return_
     GHC.Base.return___
*)
