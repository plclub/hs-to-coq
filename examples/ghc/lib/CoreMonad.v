(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require String.
Import String.StringSyntax.

(* Converted imports: *)

Require DynFlags.
Require GHC.Base.
Require GHC.Char.
Require GHC.Core.Opt.Stats.
Require GHC.Core.Rules.
Require GHC.Runtime.Context.
Require GHC.Unit.External.
Require GHC.Unit.Module.ModGuts.
Require HsToCoq.Err.
Require Module.
Require SrcLoc.
Require UniqSupply.

(* Converted type declarations: *)

Inductive FloatOutSwitches : Type :=
  | Mk_FloatOutSwitches (floatOutLambdas : option nat) (floatOutConstants : bool)
  (floatOutOverSatApps : bool) (floatToTopLevelOnly : bool)
   : FloatOutSwitches.

Inductive CoreWriter : Type :=
  | Mk_CoreWriter (cw_simpl_count : GHC.Core.Opt.Stats.SimplCount) : CoreWriter.

Axiom CoreReader : Type.

Axiom CoreIOEnv : Type -> Type.

Inductive CoreM a : Type :=
  | Mk_CoreM (unCoreM : CoreIOEnv (a * CoreWriter)%type) : CoreM a.

Arguments Mk_CoreM {_} _.

Instance Default__FloatOutSwitches : HsToCoq.Err.Default FloatOutSwitches :=
  HsToCoq.Err.Build_Default _ (Mk_FloatOutSwitches HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__CoreWriter : HsToCoq.Err.Default CoreWriter :=
  HsToCoq.Err.Build_Default _ (Mk_CoreWriter HsToCoq.Err.default).

#[global] Definition floatOutConstants (arg_0__ : FloatOutSwitches) :=
  let 'Mk_FloatOutSwitches _ floatOutConstants _ _ := arg_0__ in
  floatOutConstants.

#[global] Definition floatOutLambdas (arg_0__ : FloatOutSwitches) :=
  let 'Mk_FloatOutSwitches floatOutLambdas _ _ _ := arg_0__ in
  floatOutLambdas.

#[global] Definition floatOutOverSatApps (arg_0__ : FloatOutSwitches) :=
  let 'Mk_FloatOutSwitches _ _ floatOutOverSatApps _ := arg_0__ in
  floatOutOverSatApps.

#[global] Definition floatToTopLevelOnly (arg_0__ : FloatOutSwitches) :=
  let 'Mk_FloatOutSwitches _ _ _ floatToTopLevelOnly := arg_0__ in
  floatToTopLevelOnly.

#[global] Definition cw_simpl_count (arg_0__ : CoreWriter) :=
  let 'Mk_CoreWriter cw_simpl_count := arg_0__ in
  cw_simpl_count.

#[global] Definition unCoreM {a} (arg_0__ : CoreM a) :=
  let 'Mk_CoreM unCoreM := arg_0__ in
  unCoreM.

(* Converted value declarations: *)

Instance Functor__CoreM : GHC.Base.Functor CoreM.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreMonad.Outputable__FloatOutSwitches' *)

Instance Applicative__CoreM : GHC.Base.Applicative CoreM.
Proof.
Admitted.

Instance Monad__CoreM : GHC.Base.Monad CoreM.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `CoreMonad.Alternative__CoreM' *)

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `CoreMonad.MonadPlus__CoreM' *)

Instance MonadUnique__CoreM : UniqSupply.MonadUnique CoreM.
Proof.
Admitted.

(* Skipping all instances of class `Control.Monad.IO.Class.MonadIO', including
   `CoreMonad.MonadIO__CoreM' *)

Instance HasDynFlags__CoreM : DynFlags.HasDynFlags CoreM.
Proof.
Admitted.

Instance HasModule__CoreM : Module.HasModule CoreM.
Proof.
Admitted.

Axiom pprFloatOutSwitches : FloatOutSwitches -> GHC.Base.String.

Axiom emptyWriter : bool -> CoreWriter.

Axiom plusWriter : CoreWriter -> CoreWriter -> CoreWriter.

(* Skipping definition `CoreMonad.runCoreM' *)

Axiom nop : forall {a}, a -> CoreIOEnv (a * CoreWriter)%type.

Axiom read : forall {a}, (CoreReader -> a) -> CoreM a.

Axiom write : CoreWriter -> CoreM unit.

Axiom liftIOEnv : forall {a}, CoreIOEnv a -> CoreM a.

(* Skipping definition `CoreMonad.liftIOWithCount' *)

(* Skipping definition `CoreMonad.getHscEnv' *)

Axiom getHomeRuleBase : CoreM GHC.Core.Rules.RuleBase.

Axiom initRuleEnv : GHC.Unit.Module.ModGuts.ModGuts ->
                    CoreM GHC.Core.Rules.RuleEnv.

Axiom getExternalRuleBase : CoreM GHC.Core.Rules.RuleBase.

Axiom getNamePprCtx : CoreM Outputable.NamePprCtx.

Axiom getSrcSpanM : CoreM SrcLoc.SrcSpan.

Axiom addSimplCount : GHC.Core.Opt.Stats.SimplCount -> CoreM unit.

Axiom getUniqTag : CoreM GHC.Char.Char.

Axiom mapDynFlagsCoreM : forall {a : Type},
                         (DynFlags.DynFlags -> DynFlags.DynFlags) -> CoreM a -> CoreM a.

Axiom dropSimplCount : forall {a : Type}, CoreM a -> CoreM a.

Axiom getInteractiveContext : CoreM GHC.Runtime.Context.InteractiveContext.

(* Skipping definition `CoreMonad.getPackageFamInstEnv' *)

Axiom get_eps : CoreM GHC.Unit.External.ExternalPackageState.

(* Skipping definition `CoreMonad.getAnnotations' *)

(* Skipping definition `CoreMonad.getFirstAnnotations' *)

(* Skipping definition `CoreMonad.msg' *)

Axiom putMsgS : GHC.Base.String -> CoreM unit.

Axiom putMsg : GHC.Base.String -> CoreM unit.

Axiom errorMsg : GHC.Base.String -> CoreM unit.

Axiom fatalErrorMsgS : GHC.Base.String -> CoreM unit.

Axiom fatalErrorMsg : GHC.Base.String -> CoreM unit.

Axiom debugTraceMsgS : GHC.Base.String -> CoreM unit.

Axiom debugTraceMsg : GHC.Base.String -> CoreM unit.

(* External variables:
     Type bool nat op_zt__ option unit DynFlags.DynFlags DynFlags.HasDynFlags
     GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad GHC.Base.String
     GHC.Char.Char GHC.Core.Opt.Stats.SimplCount GHC.Core.Rules.RuleBase
     GHC.Core.Rules.RuleEnv GHC.Runtime.Context.InteractiveContext
     GHC.Unit.External.ExternalPackageState GHC.Unit.Module.ModGuts.ModGuts
     HsToCoq.Err.Build_Default HsToCoq.Err.Default HsToCoq.Err.default
     Module.HasModule Outputable.NamePprCtx SrcLoc.SrcSpan UniqSupply.MonadUnique
*)
