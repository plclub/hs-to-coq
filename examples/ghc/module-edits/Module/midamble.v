Require Import HsToCoq.Err.
Require Import HsToCoq.Unpeel.
Require Import GHC.Base.

#[global] Instance Default__InstalledUnitId : Default InstalledUnitId :=
  Build_Default _ (Mk_InstalledUnitId default ).
#[global] Instance Default__DefUnitId : Default DefUnitId :=
  Build_Default _ (Mk_DefUnitId default).
#[global] Instance Default__UnitId : Default UnitId :=
  Build_Default _ (DefiniteUnitId default).
#[global] Instance Default__ModuleName : Default ModuleName :=
  Build_Default _ (Mk_ModuleName default).
#[global] Instance Default__Module : Default Module :=
  Build_Default _ (Mk_Module default default).
#[global] Instance Default__NDModule : Default NDModule :=
  Build_Default _ (Mk_NDModule default).

Instance Unpeel_DefUnitId : Unpeel DefUnitId InstalledUnitId :=
  Build_Unpeel _ _ (fun arg_102__ => match arg_102__ with | Mk_DefUnitId fs => fs end) Mk_DefUnitId.
Instance Unpeel_NDModule : Unpeel NDModule Module :=
  Build_Unpeel _ _ (fun arg_142__ => match arg_142__ with | Mk_NDModule mod_ => mod_ end) Mk_NDModule.

(* Eq instances for Module types *)
#[global] Instance Eq__InstalledUnitId : Eq_ InstalledUnitId :=
  fun _ k => k {|
    op_zeze____ := fun a b => match a, b with
      | Mk_InstalledUnitId x, Mk_InstalledUnitId y => (x == y)
    end ;
    op_zsze____ := fun a b => match a, b with
      | Mk_InstalledUnitId x, Mk_InstalledUnitId y => (x /= y)
    end
  |}.

#[global] Instance Eq__DefUnitId : Eq_ DefUnitId :=
  fun _ k => k {|
    op_zeze____ := fun a b => match a, b with
      | Mk_DefUnitId x, Mk_DefUnitId y => (x == y)
    end ;
    op_zsze____ := fun a b => match a, b with
      | Mk_DefUnitId x, Mk_DefUnitId y => (x /= y)
    end
  |}.

#[global] Instance Eq__ModuleName : Eq_ ModuleName :=
  fun _ k => k {|
    op_zeze____ := fun a b => match a, b with
      | Mk_ModuleName x, Mk_ModuleName y => (x == y)
    end ;
    op_zsze____ := fun a b => match a, b with
      | Mk_ModuleName x, Mk_ModuleName y => (x /= y)
    end
  |}.

Fixpoint eqUnitId (a b : UnitId) : bool :=
  match a, b with
  | IndefiniteUnitId (Mk_IndefUnitId fs1 _), IndefiniteUnitId (Mk_IndefUnitId fs2 _) =>
      (fs1 == fs2)
  | DefiniteUnitId x, DefiniteUnitId y => (x == y)
  | _, _ => false
  end.

Fixpoint eqModule (a b : Module) : bool :=
  match a, b with
  | Mk_Module u1 n1, Mk_Module u2 n2 =>
      andb (eqUnitId u1 u2) (n1 == n2)
  end.

#[global] Instance Eq__UnitId : Eq_ UnitId :=
  fun _ k => k {|
    op_zeze____ := eqUnitId ;
    op_zsze____ := fun a b => negb (eqUnitId a b)
  |}.

#[global] Instance Eq__Module : Eq_ Module :=
  fun _ k => k {|
    op_zeze____ := eqModule ;
    op_zsze____ := fun a b => negb (eqModule a b)
  |}.

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
