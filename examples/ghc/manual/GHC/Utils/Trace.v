(* Stub module for GHC.Utils.Trace — debug tracing is a no-op in Coq *)
Require Import GHC.Base.

Definition pprTrace {a b : Type} : String -> b -> a -> a :=
  fun _ _ x => x.

Definition pprTraceDebug {a b : Type} : String -> b -> a -> a :=
  fun _ _ x => x.

Definition warnPprTrace {a b : Type} : bool -> String -> b -> a -> a :=
  fun _ _ _ x => x.
