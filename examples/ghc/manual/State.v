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
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive State s a : Type :=
  | Mk_State (runState' : s -> (a * s)%type) : State s a.

Arguments Mk_State {_} {_} _.

#[global] Definition runState' {s} {a} (arg_0__ : State s a) :=
  let 'Mk_State runState' := arg_0__ in
  runState'.

(* Converted value declarations: *)

#[local] Definition Functor__State_fmap {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> State inst_s a -> State inst_s b :=
  fun {a : Type} {b : Type} =>
    fun f m => Mk_State (fun s => let 'pair r s' := runState' m s in pair (f r) s').

#[local] Definition Functor__State_op_zlzd__ {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, a -> State inst_s b -> State inst_s a :=
  fun {a : Type} {b : Type} => Functor__State_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__State {s : Type} : GHC.Base.Functor (State s) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__State_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__State_op_zlzd__ |}.

#[local] Definition Applicative__State_op_zlztzg__ {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, State inst_s (a -> b) -> State inst_s a -> State inst_s b :=
  fun {a : Type} {b : Type} =>
    fun m n =>
      Mk_State (fun s =>
                  let 'pair f s' := runState' m s in
                  let 'pair x s'' := runState' n s' in
                  pair (f x) s'').

#[local] Definition Applicative__State_liftA2 {inst_s : Type}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) -> State inst_s a -> State inst_s b -> State inst_s c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__State_op_zlztzg__ (GHC.Base.fmap f x).

#[local] Definition Applicative__State_op_ztzg__ {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, State inst_s a -> State inst_s b -> State inst_s b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__State_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

#[local] Definition Applicative__State_pure {inst_s : Type}
   : forall {a : Type}, a -> State inst_s a :=
  fun {a : Type} => fun x => Mk_State (fun s => pair x s).

#[global]
Program Instance Applicative__State {s : Type}
   : GHC.Base.Applicative (State s) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__State_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__State_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__State_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__State_pure |}.

#[local] Definition Monad__State_op_zgzgze__ {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, State inst_s a -> (a -> State inst_s b) -> State inst_s b :=
  fun {a : Type} {b : Type} =>
    fun m n =>
      Mk_State (fun s => let 'pair r s' := runState' m s in runState' (n r) s').

#[local] Definition Monad__State_op_zgzg__ {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, State inst_s a -> State inst_s b -> State inst_s b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__State_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__State_return_ {inst_s : Type}
   : forall {a : Type}, a -> State inst_s a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__State {s : Type} : GHC.Base.Monad (State s) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__State_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} =>
             Monad__State_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__State_return_ |}.

#[global] Definition get {s : Type} : State s s :=
  Mk_State (fun s => pair s s).

#[global] Definition gets {s : Type} {a : Type} : (s -> a) -> State s a :=
  fun f => Mk_State (fun s => pair (f s) s).

#[global] Definition put {s : Type} : s -> State s unit :=
  fun s' => Mk_State (fun arg_0__ => pair tt s').

#[global] Definition modify {s : Type} : (s -> s) -> State s unit :=
  fun f => Mk_State (fun s => pair tt (f s)).

#[global] Definition evalState {s : Type} {a : Type} : State s a -> s -> a :=
  fun s i => let 'pair a _ := runState' s i in a.

#[global] Definition execState {s : Type} {a : Type} : State s a -> s -> s :=
  fun s i => let 'pair _ s' := runState' s i in s'.

#[global] Definition runState {s : Type} {a : Type}
   : State s a -> s -> (a * s)%type :=
  fun s i => let 'pair a s' := runState' s i in pair a s'.

(* External variables:
     Type op_zt__ pair tt unit GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Base.return___
*)
