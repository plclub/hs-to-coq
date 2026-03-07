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
Require GHC.Num.
Require GHC.Prim.
Require HsToCoq.Err.

(* Converted type declarations: *)

Inductive GhcException : Type :=
  | Signal : GHC.Num.Int -> GhcException
  | UsageError : GHC.Base.String -> GhcException
  | CmdLineError : GHC.Base.String -> GhcException
  | Panic : GHC.Base.String -> GhcException
  | PprPanic : GHC.Base.String -> GHC.Base.String -> GhcException
  | Sorry : GHC.Base.String -> GhcException
  | PprSorry : GHC.Base.String -> GHC.Base.String -> GhcException
  | InstallationError : GHC.Base.String -> GhcException
  | ProgramError : GHC.Base.String -> GhcException
  | PprProgramError : GHC.Base.String -> GHC.Base.String -> GhcException.

(* Converted value declarations: *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Panic.Show__GhcException' *)

(* Skipping definition `Panic.showException' *)

(* Skipping definition `Panic.safeShowException' *)

(* Skipping definition `Panic.showGhcExceptionUnsafe' *)

(* Skipping definition `Panic.showGhcException' *)

Axiom throwGhcException : forall {a} `{HsToCoq.Err.Default a},
                          GhcException -> a.

(* Skipping definition `Panic.throwGhcExceptionIO' *)

(* Skipping definition `Panic.handleGhcException' *)

Axiom pprPanic : forall {a : Type},
                 forall `{GHC.Prim.HasCallStack}, GHC.Base.String -> GHC.Base.String -> a.

Axiom panicDoc : forall {a} `{HsToCoq.Err.Default a},
                 GHC.Base.String -> GHC.Base.String -> a.

Axiom sorryDoc : forall {a} `{HsToCoq.Err.Default a},
                 GHC.Base.String -> GHC.Base.String -> a.

Axiom pgmErrorDoc : forall {a} `{HsToCoq.Err.Default a},
                    GHC.Base.String -> GHC.Base.String -> a.

(* Skipping definition `Panic.tryMost' *)

(* Skipping definition `Panic.signalHandlersRefCount' *)

(* Skipping definition `Panic.withSignalHandlers' *)

(* Skipping definition `Panic.callStackDoc' *)

(* Skipping definition `Panic.prettyCallStackDoc' *)

Axiom assertPprPanic : forall {a : Type},
                       forall `{GHC.Prim.HasCallStack}, GHC.Base.String -> a.

Axiom assertPpr : forall {a : Type},
                  forall `{GHC.Prim.HasCallStack}, bool -> GHC.Base.String -> a -> a.

Axiom assertPprMaybe : forall {a : Type},
                       forall `{GHC.Prim.HasCallStack}, option GHC.Base.String -> a -> a.

Axiom massertPpr : forall {m : Type -> Type},
                   forall `{GHC.Prim.HasCallStack},
                   forall `{GHC.Base.Applicative m}, bool -> GHC.Base.String -> m unit.

Axiom assertPprM : forall {m : Type -> Type},
                   forall `{GHC.Prim.HasCallStack},
                   forall `{GHC.Base.Monad m}, m bool -> GHC.Base.String -> m unit.

Axiom panic : forall {a} `{HsToCoq.Err.Default a}, GHC.Base.String -> a.

Axiom panicStr : forall {a} `{HsToCoq.Err.Default a},
                 GHC.Base.String -> GHC.Base.String -> a.

Inductive panicked {a} : a -> Prop :=
  | PlainPanic `{HsToCoq.Err.Default a} {s} : panicked (panic s)
  | StrPanic `{HsToCoq.Err.Default a} {s} {d} : panicked (panicStr s d).

Axiom pgmError : forall {a} `{HsToCoq.Err.Default a}, GHC.Base.String -> a.

#[global] Definition warnPprTrace
   : forall {a} `{HsToCoq.Err.Default a},
     bool -> GHC.Base.String -> GHC.Num.Integer -> GHC.Base.String -> a -> a :=
  fun {a} {_} b msg i msg2 x => if b then pgmError msg : a else x.

Axiom noString : forall {a}, a -> GHC.Base.String.

Axiom someSDoc : GHC.Base.String.

(* External variables:
     Prop Type bool option unit GHC.Base.Applicative GHC.Base.Monad GHC.Base.String
     GHC.Num.Int GHC.Num.Integer GHC.Prim.HasCallStack HsToCoq.Err.Default
*)
