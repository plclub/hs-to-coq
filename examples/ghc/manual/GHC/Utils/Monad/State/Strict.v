(* Stub module for GHC.Utils.Monad.State.Strict *)
Require Import GHC.Base.

Definition State (s a : Type) : Type := s -> (a * s)%type.

Definition get {s : Type} : State s s := fun st => (st, st).

Definition put {s : Type} : s -> State s unit := fun st _ => (tt, st).

Definition modify' {s : Type} : (s -> s) -> State s unit :=
  fun f st => (tt, f st).

Definition runState {s a : Type} : State s a -> s -> (a * s)%type :=
  fun m st => m st.

Definition evalState {s a : Type} : State s a -> s -> a :=
  fun m st => fst (m st).

Local Definition Functor__State_fmap {inst_s : Type}
   : forall {a : Type}, forall {b : Type}, (a -> b) -> State inst_s a -> State inst_s b :=
  fun {a : Type} {b : Type} =>
    fun f m => fun s => let '(r, s') := m s in (f r, s').

Local Definition Functor__State_op_zlzd__ {inst_s : Type}
   : forall {a : Type}, forall {b : Type}, a -> State inst_s b -> State inst_s a :=
  fun {a : Type} {b : Type} => Functor__State_fmap ∘ const.

#[global]
Program Instance Functor__State {s : Type} : Functor (State s) :=
  fun _ k__ =>
    k__ {| fmap__ := fun (a : Type) (b : Type) => Functor__State_fmap ;
           op_zlzd____ := fun (a : Type) (b : Type) => Functor__State_op_zlzd__ |}.

Local Definition Applicative__State_pure {inst_s : Type}
   : forall {a : Type}, a -> State inst_s a :=
  fun {a : Type} => fun x => fun s => (x, s).

Local Definition Applicative__State_op_zlztzg__ {inst_s : Type}
   : forall {a : Type}, forall {b : Type}, State inst_s (a -> b) -> State inst_s a -> State inst_s b :=
  fun {a : Type} {b : Type} =>
    fun mf mx => fun s =>
      let '(f, s') := mf s in let '(x, s'') := mx s' in (f x, s'').

Local Definition Applicative__State_liftA2 {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, forall {c : Type}, (a -> b -> c) -> State inst_s a -> State inst_s b -> State inst_s c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f mx my => fun s =>
      let '(x, s') := mx s in let '(y, s'') := my s' in (f x y, s'').

Local Definition Applicative__State_op_ztzg__ {inst_s : Type}
   : forall {a : Type}, forall {b : Type}, State inst_s a -> State inst_s b -> State inst_s b :=
  fun {a : Type} {b : Type} =>
    fun ma mb => fun s =>
      let '(_, s') := ma s in mb s'.

#[global]
Program Instance Applicative__State {s : Type} : Applicative (State s) :=
  fun _ k__ =>
    k__ {| liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__State_liftA2 ;
           op_zlztzg____ := fun (a : Type) (b : Type) => Applicative__State_op_zlztzg__ ;
           op_ztzg____ := fun (a : Type) (b : Type) => Applicative__State_op_ztzg__ ;
           pure__ := fun (a : Type) => Applicative__State_pure |}.

Local Definition Monad__State_op_zgzgze__ {inst_s : Type}
   : forall {a : Type}, forall {b : Type}, State inst_s a -> (a -> State inst_s b) -> State inst_s b :=
  fun {a : Type} {b : Type} =>
    fun m k => fun s => let '(a, s') := m s in k a s'.

Local Definition Monad__State_return_ {inst_s : Type}
   : forall {a : Type}, a -> State inst_s a :=
  fun {a : Type} => pure.

Local Definition Monad__State_op_zgzg__ {inst_s : Type}
   : forall {a : Type}, forall {b : Type}, State inst_s a -> State inst_s b -> State inst_s b :=
  fun {a : Type} {b : Type} => _*>_.

#[global]
Program Instance Monad__State {s : Type} : Monad (State s) :=
  fun _ k__ =>
    k__ {| op_zgzg____ := fun (a : Type) (b : Type) => Monad__State_op_zgzg__ ;
           op_zgzgze____ := fun (a : Type) (b : Type) => Monad__State_op_zgzgze__ ;
           return___ := fun (a : Type) => Monad__State_return_ |}.
