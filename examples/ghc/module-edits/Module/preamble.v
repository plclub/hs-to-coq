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
