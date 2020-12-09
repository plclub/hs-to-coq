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
Require Data.Tuple.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive StateT s m a : Type :=
  | Mk_StateT (runStateT : s -> m (a * s)%type) : StateT s m a.

Definition State s :=
  (StateT s Data.Functor.Identity.Identity)%type.

Arguments Mk_StateT {_} {_} {_} _.

Definition runStateT {s} {m} {a} (arg_0__ : StateT s m a) :=
  let 'Mk_StateT runStateT := arg_0__ in
  runStateT.

(* Converted value declarations: *)

Local Definition Functor__StateT_fmap {inst_m : Type -> Type} {inst_s : Type}
  `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> StateT inst_s inst_m a -> StateT inst_s inst_m b :=
  fun {a : Type} {b : Type} =>
    fun f m =>
      Mk_StateT (fun s =>
                   GHC.Base.fmap (fun '(pair a s') => pair (f a) s') (runStateT m s)).

Local Definition Functor__StateT_op_zlzd__ {inst_m : Type -> Type} {inst_s
   : Type} `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type}, a -> StateT inst_s inst_m b -> StateT inst_s inst_m a :=
  fun {a : Type} {b : Type} => Functor__StateT_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__StateT {m : Type -> Type} {s : Type}
  `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (StateT s m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__StateT_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__StateT_op_zlzd__ |}.

Local Definition Applicative__StateT_op_zlztzg__ {inst_m : Type -> Type} {inst_s
   : Type} `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     StateT inst_s inst_m (a -> b) ->
     StateT inst_s inst_m a -> StateT inst_s inst_m b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_StateT mf, Mk_StateT mx =>
          Mk_StateT (fun s =>
                       let cont_2__ arg_3__ :=
                         let 'pair f s' := arg_3__ in
                         let cont_4__ arg_5__ :=
                           let 'pair x s'' := arg_5__ in
                           GHC.Base.return_ (pair (f x) s'') in
                         mx s' GHC.Base.>>= cont_4__ in
                       mf s GHC.Base.>>= cont_2__)
      end.

Local Definition Applicative__StateT_liftA2 {inst_m : Type -> Type} {inst_s
   : Type} `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     StateT inst_s inst_m a -> StateT inst_s inst_m b -> StateT inst_s inst_m c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__StateT_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__StateT_pure {inst_m : Type -> Type} {inst_s
   : Type} `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a : Type}, a -> StateT inst_s inst_m a :=
  fun {a : Type} => fun a => Mk_StateT (fun s => GHC.Base.return_ (pair a s)).

Definition Applicative__StateT_op_ztzg__ {inst_m} {inst_s} `{_
   : GHC.Base.Functor inst_m} `{_ : GHC.Base.Monad inst_m}
   : forall {a} {b},
     StateT inst_s inst_m a -> StateT inst_s inst_m b -> StateT inst_s inst_m b :=
  fun {a} {b} =>
    fun m k =>
      Applicative__StateT_op_zlztzg__ (Applicative__StateT_op_zlztzg__
                                       (Applicative__StateT_pure (fun x y => x)) k) m.

Program Instance Applicative__StateT {m : Type -> Type} {s : Type}
  `{GHC.Base.Functor m} `{GHC.Base.Monad m}
   : GHC.Base.Applicative (StateT s m) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__StateT_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__StateT_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__StateT_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__StateT_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Monad.Trans.State.Lazy.Alternative__StateT' *)

Local Definition Monad__StateT_op_zgzgze__ {inst_m : Type -> Type} {inst_s
   : Type} `{(GHC.Base.Monad inst_m)}
   : forall {a : Type},
     forall {b : Type},
     StateT inst_s inst_m a ->
     (a -> StateT inst_s inst_m b) -> StateT inst_s inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m k =>
      Mk_StateT (fun s =>
                   let cont_0__ arg_1__ := let 'pair a s' := arg_1__ in runStateT (k a) s' in
                   runStateT m s GHC.Base.>>= cont_0__).

Local Definition Monad__StateT_op_zgzg__ {inst_m : Type -> Type} {inst_s : Type}
  `{(GHC.Base.Monad inst_m)}
   : forall {a : Type},
     forall {b : Type},
     StateT inst_s inst_m a -> StateT inst_s inst_m b -> StateT inst_s inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__StateT_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__StateT_return_ {inst_m : Type -> Type} {inst_s : Type}
  `{(GHC.Base.Monad inst_m)}
   : forall {a : Type}, a -> StateT inst_s inst_m a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__StateT {m : Type -> Type} {s : Type} `{(GHC.Base.Monad
   m)}
   : GHC.Base.Monad (StateT s m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__StateT_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} =>
             Monad__StateT_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__StateT_return_ |}.

Local Definition MonadFail__StateT_fail {inst_m : Type -> Type} {inst_s : Type}
  `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a : Type}, GHC.Base.String -> StateT inst_s inst_m a :=
  fun {a : Type} =>
    fun str => Mk_StateT (fun arg_0__ => Control.Monad.Fail.fail str).

Program Instance MonadFail__StateT {m : Type -> Type} {s : Type}
  `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (StateT s m) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun {a : Type} => MonadFail__StateT_fail |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Control.Monad.Trans.State.Lazy.MonadPlus__StateT' *)

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Control.Monad.Trans.State.Lazy.MonadFix__StateT' *)

Local Definition MonadTrans__StateT_lift {inst_s : Type}
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, m a -> StateT inst_s m a :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    fun m =>
      Mk_StateT (fun s => m GHC.Base.>>= (fun a => GHC.Base.return_ (pair a s))).

Program Instance MonadTrans__StateT {s : Type}
   : Control.Monad.Trans.Class.MonadTrans (StateT s) :=
  fun _ k__ =>
    k__ {| Control.Monad.Trans.Class.lift__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             MonadTrans__StateT_lift |}.

(* Skipping all instances of class `Control.Monad.IO.Class.MonadIO', including
   `Control.Monad.Trans.State.Lazy.MonadIO__StateT' *)

Definition state {m : Type -> Type} {s : Type} {a : Type} `{GHC.Base.Monad m}
   : (s -> (a * s)%type) -> StateT s m a :=
  fun f => Mk_StateT (GHC.Base.return_ GHC.Base.∘ f).

Definition runState {s : Type} {a : Type} : State s a -> s -> (a * s)%type :=
  fun m => Data.Functor.Identity.runIdentity GHC.Base.∘ runStateT m.

Definition evalState {s : Type} {a : Type} : State s a -> s -> a :=
  fun m s => Data.Tuple.fst (runState m s).

Definition execState {s : Type} {a : Type} : State s a -> s -> s :=
  fun m s => Data.Tuple.snd (runState m s).

Definition mapStateT {m : Type -> Type} {a : Type} {s : Type} {n : Type -> Type}
  {b : Type}
   : (m (a * s)%type -> n (b * s)%type) -> StateT s m a -> StateT s n b :=
  fun f m => Mk_StateT (f GHC.Base.∘ runStateT m).

Definition mapState {a : Type} {s : Type} {b : Type}
   : ((a * s)%type -> (b * s)%type) -> State s a -> State s b :=
  fun f =>
    mapStateT (Data.Functor.Identity.Mk_Identity GHC.Base.∘
               (f GHC.Base.∘ Data.Functor.Identity.runIdentity)).

Definition withStateT {s : Type} {m : Type -> Type} {a : Type}
   : (s -> s) -> StateT s m a -> StateT s m a :=
  fun f m => Mk_StateT (runStateT m GHC.Base.∘ f).

Definition withState {s : Type} {a : Type}
   : (s -> s) -> State s a -> State s a :=
  withStateT.

Definition evalStateT {m : Type -> Type} {s : Type} {a : Type} `{GHC.Base.Monad
  m}
   : StateT s m a -> s -> m a :=
  fun m s =>
    let cont_0__ arg_1__ := let 'pair a _ := arg_1__ in GHC.Base.return_ a in
    runStateT m s GHC.Base.>>= cont_0__.

Definition execStateT {m : Type -> Type} {s : Type} {a : Type} `{GHC.Base.Monad
  m}
   : StateT s m a -> s -> m s :=
  fun m s =>
    let cont_0__ arg_1__ := let 'pair _ s' := arg_1__ in GHC.Base.return_ s' in
    runStateT m s GHC.Base.>>= cont_0__.

Definition get {m : Type -> Type} {s : Type} `{GHC.Base.Monad m}
   : StateT s m s :=
  state (fun s => pair s s).

Definition put {m : Type -> Type} {s : Type} `{GHC.Base.Monad m}
   : s -> StateT s m unit :=
  fun s => state (fun arg_0__ => pair tt s).

Definition modify {m : Type -> Type} {s : Type} `{GHC.Base.Monad m}
   : (s -> s) -> StateT s m unit :=
  fun f => state (fun s => pair tt (f s)).

Definition modify' {m : Type -> Type} {s : Type} `{GHC.Base.Monad m}
   : (s -> s) -> StateT s m unit :=
  fun f => get GHC.Base.>>= (fun s => put (f s)).

Definition gets {m : Type -> Type} {s : Type} {a : Type} `{GHC.Base.Monad m}
   : (s -> a) -> StateT s m a :=
  fun f => state (fun s => pair (f s) s).

Definition liftCallCC {m : Type -> Type} {a : Type} {s : Type} {b : Type}
   : Control.Monad.Signatures.CallCC m (a * s)%type (b * s)%type ->
     Control.Monad.Signatures.CallCC (StateT s m) a b :=
  fun callCC f =>
    Mk_StateT (fun s =>
                 callCC (fun c =>
                           runStateT (f (fun a => Mk_StateT (fun arg_0__ => c (pair a s)))) s)).

Definition liftCallCC' {m : Type -> Type} {a : Type} {s : Type} {b : Type}
   : Control.Monad.Signatures.CallCC m (a * s)%type (b * s)%type ->
     Control.Monad.Signatures.CallCC (StateT s m) a b :=
  fun callCC f =>
    Mk_StateT (fun s =>
                 callCC (fun c =>
                           runStateT (f (fun a => Mk_StateT (fun s' => c (pair a s')))) s)).

(* Skipping definition `Control.Monad.Trans.State.Lazy.liftCatch' *)

Definition liftListen {m : Type -> Type} {w : Type} {a : Type} {s : Type}
  `{GHC.Base.Monad m}
   : Control.Monad.Signatures.Listen w m (a * s)%type ->
     Control.Monad.Signatures.Listen w (StateT s m) a :=
  fun listen m =>
    Mk_StateT (fun s =>
                 let cont_0__ arg_1__ :=
                   let 'pair (pair a s') w := arg_1__ in
                   GHC.Base.return_ (pair (pair a w) s') in
                 listen (runStateT m s) GHC.Base.>>= cont_0__).

Definition liftPass {m : Type -> Type} {w : Type} {a : Type} {s : Type}
  `{GHC.Base.Monad m}
   : Control.Monad.Signatures.Pass w m (a * s)%type ->
     Control.Monad.Signatures.Pass w (StateT s m) a :=
  fun pass m =>
    Mk_StateT (fun s =>
                 pass (let cont_0__ arg_1__ :=
                         let 'pair (pair a f) s' := arg_1__ in
                         GHC.Base.return_ (pair (pair a s') f) in
                       runStateT m s GHC.Base.>>= cont_0__)).

(* External variables:
     Type op_zt__ pair tt unit Control.Monad.Fail.MonadFail Control.Monad.Fail.fail
     Control.Monad.Fail.fail__ Control.Monad.Signatures.CallCC
     Control.Monad.Signatures.Listen Control.Monad.Signatures.Pass
     Control.Monad.Trans.Class.MonadTrans Control.Monad.Trans.Class.lift__
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity
     Data.Functor.Identity.runIdentity Data.Tuple.fst Data.Tuple.snd
     GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad GHC.Base.String
     GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.liftA2__
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__
     GHC.Base.op_zgzgze____ GHC.Base.op_zlzd____ GHC.Base.op_zlztzg____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return_
     GHC.Base.return___
*)
