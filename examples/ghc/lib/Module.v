(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Tuple.
Require FastString.
Require GHC.Base.
Require HsToCoq.Unpeel.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Record HasModule__Dict (m : Type -> Type) := HasModule__Dict_Build {
  getModule__ : m GHC.Unit.Types.Module }.

#[global] Definition HasModule (m : Type -> Type) :=
  forall r__, (HasModule__Dict m -> r__) -> r__.
Existing Class HasModule.

#[global] Definition getModule `{g__0__ : HasModule m}
   : m GHC.Unit.Types.Module :=
  g__0__ _ (getModule__ m).

Record ContainsModule__Dict (t : Type) := ContainsModule__Dict_Build {
  extractModule__ : t -> GHC.Unit.Types.Module }.

#[global] Definition ContainsModule (t : Type) :=
  forall r__, (ContainsModule__Dict t -> r__) -> r__.
Existing Class ContainsModule.

#[global] Definition extractModule `{g__0__ : ContainsModule t}
   : t -> GHC.Unit.Types.Module :=
  g__0__ _ (extractModule__ t).

(* Midamble *)

Require Import HsToCoq.Err.
Require Import HsToCoq.Unpeel.

Instance Default__InstalledUnitId : Default InstalledUnitId :=
  Build_Default _ (Mk_InstalledUnitId default ).
Instance Default__DefUnitId : Default DefUnitId :=
  Build_Default _ (Mk_DefUnitId default).
Instance Default__UnitId : Default UnitId :=
  Build_Default _ (DefiniteUnitId default).
Instance Default__ModuleName : Default ModuleName :=
  Build_Default _ (Mk_ModuleName default).
Instance Default__Module : Default Module :=
  Build_Default _ (Mk_Module default default).
Instance Default__NDModule : Default NDModule :=
  Build_Default _ (Mk_NDModule default).
Instance Default__ModLocation : Default ModLocation :=
  Build_Default _ (Mk_ModLocation default default default).

Instance Unpeel_DefUnitId : Unpeel DefUnitId InstalledUnitId :=
  Build_Unpeel _ _ (fun arg_102__ => match arg_102__ with | Mk_DefUnitId fs => fs end) Mk_DefUnitId.
Instance Unpeel_NDModule : Unpeel NDModule Module :=
  Build_Unpeel _ _ (fun arg_142__ => match arg_142__ with | Mk_NDModule mod_ => mod_ end) Mk_NDModule.

(* Converted value declarations: *)

(* Skipping definition `Module.moduleIsDefinite' *)

(* Skipping definition `Module.moduleStableString' *)

(* Skipping definition `Module.stableModuleCmp' *)

(* Skipping definition `Module.getModuleInstantiation' *)

#[global] Definition installedModuleEq
   : GHC.Unit.Types.InstalledModule -> GHC.Unit.Types.Module -> bool :=
  fun imod mod_ => Data.Tuple.fst (getModuleInstantiation mod_) GHC.Base.== imod.

(* Skipping definition `Module.getUnitInstantiations' *)

(* Skipping definition `Module.uninstantiateInstantiatedUnit' *)

(* Skipping definition `Module.uninstantiateInstantiatedModule' *)

(* Skipping definition `Module.isHoleModule' *)

(* Skipping definition `Module.mkHoleModule' *)

Instance Unpeel_ComponentId
   : HsToCoq.Unpeel.Unpeel ComponentId FastString.FastString :=
  HsToCoq.Unpeel.Build_Unpeel _ _ (fun '(Mk_ComponentId fs) => fs) Mk_ComponentId.

(* External variables:
     ComponentId Mk_ComponentId Type bool getModuleInstantiation Data.Tuple.fst
     FastString.FastString GHC.Base.op_zeze__ GHC.Unit.Types.InstalledModule
     GHC.Unit.Types.Module HsToCoq.Unpeel.Build_Unpeel HsToCoq.Unpeel.Unpeel
*)
