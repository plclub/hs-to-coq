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
