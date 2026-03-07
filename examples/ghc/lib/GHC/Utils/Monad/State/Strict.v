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

#[global] Instance Functor__State {s : Type} : Functor (State s).
Admitted.

#[global] Instance Applicative__State {s : Type} : Applicative (State s).
Admitted.

#[global] Instance Monad__State {s : Type} : Monad (State s).
Admitted.
