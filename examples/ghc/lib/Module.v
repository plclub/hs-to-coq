(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

(* Types that were in GHC.Unit.Module in GHC 8.4 but moved to GHC.Unit.Types in GHC 9.10.
   Since we skip GHC.Unit.Types, we define them here.
   Note: we avoid Require Unique/UniqFM/UniqSet to prevent circular deps. *)

Require FastString.
Require Import Coq.Numbers.BinNums.

Inductive ModuleName : Type :=
  | Mk_ModuleName : FastString.FastString -> ModuleName.

(* Simplified type hierarchy — avoids mutual Inductive with Unique dependency *)
Inductive InstalledUnitId : Type :=
  | Mk_InstalledUnitId (installedUnitIdFS : FastString.FastString)
   : InstalledUnitId.

Inductive DefUnitId : Type :=
  | Mk_DefUnitId (unDefUnitId : InstalledUnitId) : DefUnitId.

Inductive ComponentId : Type :=
  | Mk_ComponentId : FastString.FastString -> ComponentId.

(* Simplified UnitId — IndefUnitId uses N instead of Unique.Unique to break circular dep *)
Inductive IndefUnitId : Type :=
  | Mk_IndefUnitId (indefUnitIdFS : FastString.FastString) (indefUnitIdKey
    : N)
   : IndefUnitId
with Module : Type :=
  | Mk_Module (moduleUnitId : UnitId) (moduleName : ModuleName) : Module
with UnitId : Type :=
  | IndefiniteUnitId : IndefUnitId -> UnitId
  | DefiniteUnitId : DefUnitId -> UnitId.

Definition Unit := UnitId.

Inductive InstalledModule : Type :=
  | Mk_InstalledModule (installedModuleUnitId : InstalledUnitId)
  (installedModuleName : ModuleName)
   : InstalledModule.

Inductive IndefModule : Type :=
  | Mk_IndefModule (indefModuleUnitId : IndefUnitId) (indefModuleName
    : ModuleName)
   : IndefModule.

Inductive NDModule : Type :=
  | Mk_NDModule : Module -> NDModule.

(* Converted imports: *)

Require FastString.
Require HsToCoq.Unpeel.

(* Converted type declarations: *)

Record HasModule__Dict (m : Type -> Type) := HasModule__Dict_Build {
  getModule__ : m Module }.

#[global] Definition HasModule (m : Type -> Type) :=
  forall r__, (HasModule__Dict m -> r__) -> r__.
Existing Class HasModule.

#[global] Definition getModule `{g__0__ : HasModule m} : m Module :=
  g__0__ _ (getModule__ m).

Record ContainsModule__Dict (t : Type) := ContainsModule__Dict_Build {
  extractModule__ : t -> Module }.

#[global] Definition ContainsModule (t : Type) :=
  forall r__, (ContainsModule__Dict t -> r__) -> r__.
Existing Class ContainsModule.

#[global] Definition extractModule `{g__0__ : ContainsModule t} : t -> Module :=
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

Instance Unpeel_DefUnitId : Unpeel DefUnitId InstalledUnitId :=
  Build_Unpeel _ _ (fun arg_102__ => match arg_102__ with | Mk_DefUnitId fs => fs end) Mk_DefUnitId.
Instance Unpeel_NDModule : Unpeel NDModule Module :=
  Build_Unpeel _ _ (fun arg_142__ => match arg_142__ with | Mk_NDModule mod_ => mod_ end) Mk_NDModule.

(* Record accessors for Module *)
Definition moduleUnit (m : Module) : UnitId :=
  match m with | Mk_Module u _ => u end.
Definition moduleName_ (m : Module) : ModuleName :=
  match m with | Mk_Module _ n => n end.

(* Smart constructor *)
Definition mkModule (u : UnitId) (n : ModuleName) : Module := Mk_Module u n.

(* GHC 9.10: various Unit constants — axiomatize *)
Axiom isInteractiveModule : Module -> bool.
Axiom baseUnit : UnitId.
Axiom bignumUnit : UnitId.
Axiom experimentalUnit : UnitId.
Axiom ghcInternalUnit : UnitId.
Axiom mainUnit : UnitId.
Axiom primUnit : UnitId.
Axiom thisGhcUnit : UnitId.

(* Converted value declarations: *)

(* Skipping definition `Module.moduleIsDefinite' *)

(* Skipping definition `Module.moduleStableString' *)

(* Skipping definition `Module.stableModuleCmp' *)

(* Skipping definition `Module.installedModuleEq' *)

(* Skipping definition `Module.getModuleInstantiation' *)

(* Skipping definition `Module.getUnitInstantiations' *)

(* Skipping definition `Module.uninstantiateInstantiatedUnit' *)

(* Skipping definition `Module.uninstantiateInstantiatedModule' *)

(* Skipping definition `Module.isHoleModule' *)

(* Skipping definition `Module.mkHoleModule' *)

Instance Unpeel_ComponentId
   : HsToCoq.Unpeel.Unpeel ComponentId FastString.FastString :=
  HsToCoq.Unpeel.Build_Unpeel _ _ (fun '(Mk_ComponentId fs) => fs) Mk_ComponentId.

(* External variables:
     ComponentId Mk_ComponentId Module Type FastString.FastString
     HsToCoq.Unpeel.Build_Unpeel HsToCoq.Unpeel.Unpeel
*)
