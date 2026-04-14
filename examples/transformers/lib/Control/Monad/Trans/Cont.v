(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Fail.
Require Control.Monad.Trans.Class.
Require Data.Functor.Identity.
Require GHC.Base.
Require GHC.Prim.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive ContT {k : Type} (r : k) (m : k -> Type) (a : Type) : Type :=
  | Mk_ContT (runContT : (a -> m r) -> m r) : ContT r m a.

#[global] Definition Cont r :=
  (ContT r Data.Functor.Identity.Identity)%type.

Arguments Mk_ContT {_} {_} {_} {_} _.

#[global] Definition runContT {k : Type} {r : k} {m : k -> Type} {a : Type}
  (arg_0__ : ContT r m a) :=
  let 'Mk_ContT runContT := arg_0__ in
  runContT.

(* Converted value declarations: *)

#[local] Definition Functor__ContT_fmap {inst_k : Type} {inst_r : inst_k}
  {inst_m : inst_k -> Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> ContT inst_r inst_m a -> ContT inst_r inst_m b :=
  fun {a : Type} {b : Type} =>
    fun f m => Mk_ContT (fun c => runContT m (c GHC.Base.∘ f)).

#[local] Definition Functor__ContT_op_zlzd__ {inst_k : Type} {inst_r : inst_k}
  {inst_m : inst_k -> Type}
   : forall {a : Type},
     forall {b : Type}, a -> ContT inst_r inst_m b -> ContT inst_r inst_m a :=
  fun {a : Type} {b : Type} => Functor__ContT_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__ContT {k : Type} {r : k} {m : k -> Type}
   : GHC.Base.Functor (ContT r m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__ContT_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__ContT_op_zlzd__ |}.

#[local] Definition Applicative__ContT_op_zlztzg__ {inst_k : Type} {inst_r
   : inst_k} {inst_m : inst_k -> Type}
   : forall {a : Type},
     forall {b : Type},
     ContT inst_r inst_m (a -> b) ->
     ContT inst_r inst_m a -> ContT inst_r inst_m b :=
  fun {a : Type} {b : Type} =>
    fun f v =>
      Mk_ContT (fun c => runContT f (fun g => runContT v (c GHC.Base.∘ g))).

#[local] Definition Applicative__ContT_liftA2 {inst_k : Type} {inst_r : inst_k}
  {inst_m : inst_k -> Type}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     ContT inst_r inst_m a -> ContT inst_r inst_m b -> ContT inst_r inst_m c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__ContT_op_zlztzg__ (GHC.Base.fmap f x).

#[local] Definition Applicative__ContT_pure {inst_k : Type} {inst_r : inst_k}
  {inst_m : inst_k -> Type}
   : forall {a : Type}, a -> ContT inst_r inst_m a :=
  fun {a : Type} => fun x => Mk_ContT (GHC.Prim.rightSection GHC.Base.op_zd__ x).

#[global] Definition Applicative__ContT_op_ztzg__ {inst_k} {inst_m
   : inst_k -> Type} {inst_s : inst_k}
   : forall {a} {b},
     ContT inst_s inst_m a -> ContT inst_s inst_m b -> ContT inst_s inst_m b :=
  fun {a} {b} =>
    fun m k =>
      Applicative__ContT_op_zlztzg__ (Applicative__ContT_op_zlztzg__
                                      (Applicative__ContT_pure (fun x y => x)) k) m.

#[global]
Program Instance Applicative__ContT {k : Type} {r : k} {m : k -> Type}
   : GHC.Base.Applicative (ContT r m) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__ContT_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__ContT_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__ContT_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__ContT_pure |}.

#[local] Definition Monad__ContT_op_zgzgze__ {inst_k : Type} {inst_r : inst_k}
  {inst_m : inst_k -> Type}
   : forall {a : Type},
     forall {b : Type},
     ContT inst_r inst_m a ->
     (a -> ContT inst_r inst_m b) -> ContT inst_r inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m k => Mk_ContT (fun c => runContT m (fun x => runContT (k x) c)).

#[local] Definition Monad__ContT_op_zgzg__ {inst_k : Type} {inst_r : inst_k}
  {inst_m : inst_k -> Type}
   : forall {a : Type},
     forall {b : Type},
     ContT inst_r inst_m a -> ContT inst_r inst_m b -> ContT inst_r inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__ContT_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__ContT_return_ {inst_k : Type} {inst_r : inst_k}
  {inst_m : inst_k -> Type}
   : forall {a : Type}, a -> ContT inst_r inst_m a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__ContT {k : Type} {r : k} {m : k -> Type}
   : GHC.Base.Monad (ContT r m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__ContT_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) =>
             Monad__ContT_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__ContT_return_ |}.

#[local] Definition MonadFail__ContT_fail {inst_m : Type -> Type} {inst_r
   : Type} `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a : Type}, GHC.Base.String -> ContT inst_r inst_m a :=
  fun {a : Type} =>
    fun msg => Mk_ContT (fun arg_0__ => Control.Monad.Fail.fail msg).

#[global]
Program Instance MonadFail__ContT {m : Type -> Type} {r : Type}
  `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (ContT r m) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun (a : Type) => MonadFail__ContT_fail |}.

#[local] Definition MonadTrans__ContT_lift {inst_r : Type}
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, m a -> ContT inst_r m a :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    fun m => Mk_ContT (_GHC.Base.>>=_ m).

#[global]
Program Instance MonadTrans__ContT {r : Type}
   : Control.Monad.Trans.Class.MonadTrans (ContT r) :=
  fun _ k__ =>
    k__ {| Control.Monad.Trans.Class.lift__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             MonadTrans__ContT_lift |}.

(* Skipping all instances of class `Control.Monad.IO.Class.MonadIO', including
   `Control.Monad.Trans.Cont.MonadIO__ContT' *)

#[global] Definition cont {a : Type} {r : Type} : ((a -> r) -> r) -> Cont r a :=
  fun f =>
    Mk_ContT (fun c =>
                Data.Functor.Identity.Mk_Identity (f (Data.Functor.Identity.runIdentity
                                                      GHC.Base.∘
                                                      c))).

#[global] Definition runCont {r : Type} {a : Type}
   : Cont r a -> (a -> r) -> r :=
  fun m k =>
    Data.Functor.Identity.runIdentity (runContT m (Data.Functor.Identity.Mk_Identity
                                                   GHC.Base.∘
                                                   k)).

#[global] Definition evalContT {m : Type -> Type} {r : Type} `{GHC.Base.Monad m}
   : ContT r m r -> m r :=
  fun m => runContT m GHC.Base.return_.

#[global] Definition evalCont {r : Type} : Cont r r -> r :=
  fun m => Data.Functor.Identity.runIdentity (evalContT m).

#[global] Definition mapContT {k : Type} {m : k -> Type} {r : k} {a : Type}
   : (m r -> m r) -> ContT r m a -> ContT r m a :=
  fun f m => Mk_ContT (f GHC.Base.∘ runContT m).

#[global] Definition mapCont {r : Type} {a : Type}
   : (r -> r) -> Cont r a -> Cont r a :=
  fun f =>
    mapContT (Data.Functor.Identity.Mk_Identity GHC.Base.∘
              (f GHC.Base.∘ Data.Functor.Identity.runIdentity)).

#[global] Definition withContT {k : Type} {b : Type} {m : k -> Type} {r : k} {a
   : Type}
   : ((b -> m r) -> a -> m r) -> ContT r m a -> ContT r m b :=
  fun f m => Mk_ContT (runContT m GHC.Base.∘ f).

#[global] Definition withCont {b : Type} {r : Type} {a : Type}
   : ((b -> r) -> a -> r) -> Cont r a -> Cont r b :=
  fun f =>
    withContT ((_GHC.Base.∘_ Data.Functor.Identity.Mk_Identity) GHC.Base.∘
               (f GHC.Base.∘ (_GHC.Base.∘_ Data.Functor.Identity.runIdentity))).

#[global] Definition resetT {m : Type -> Type} {r : Type} {r' : Type}
  `{GHC.Base.Monad m}
   : ContT r m r -> ContT r' m r :=
  Control.Monad.Trans.Class.lift GHC.Base.∘ evalContT.

#[global] Definition reset {r : Type} {r' : Type} : Cont r r -> Cont r' r :=
  resetT.

#[global] Definition shiftT {m : Type -> Type} {a : Type} {r : Type}
  `{GHC.Base.Monad m}
   : ((a -> m r) -> ContT r m r) -> ContT r m a :=
  fun f => Mk_ContT (evalContT GHC.Base.∘ f).

#[global] Definition shift {a : Type} {r : Type}
   : ((a -> r) -> Cont r r) -> Cont r a :=
  fun f => shiftT (f GHC.Base.∘ (_GHC.Base.∘_ Data.Functor.Identity.runIdentity)).

#[global] Definition callCC {k : Type} {a : Type} {r : k} {m : k -> Type} {b
   : Type}
   : ((a -> ContT r m b) -> ContT r m a) -> ContT r m a :=
  fun f =>
    Mk_ContT (fun c => runContT (f (fun x => Mk_ContT (fun arg_0__ => c x))) c).

#[global] Definition liftLocal {m : Type -> Type} {r' : Type} {r : Type} {a
   : Type} `{GHC.Base.Monad m}
   : m r' ->
     ((r' -> r') -> m r -> m r) -> (r' -> r') -> ContT r m a -> ContT r m a :=
  fun ask local f m =>
    Mk_ContT (fun c =>
                ask GHC.Base.>>=
                (fun r => local f (runContT m (local (GHC.Base.const r) GHC.Base.∘ c)))).

(* External variables:
     Type Control.Monad.Fail.MonadFail Control.Monad.Fail.fail
     Control.Monad.Fail.fail__ Control.Monad.Trans.Class.MonadTrans
     Control.Monad.Trans.Class.lift Control.Monad.Trans.Class.lift__
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity
     Data.Functor.Identity.runIdentity GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monad GHC.Base.String GHC.Base.const GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.liftA2__ GHC.Base.op_z2218U__ GHC.Base.op_zd__ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____ GHC.Base.op_zlzd____
     GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return_ GHC.Base.return___ GHC.Prim.rightSection
*)
