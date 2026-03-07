(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require BinNums.
Require FieldLabel.
Require GHC.Base.
Require GHC.Utils.CliOption.
Require HsToCoq.Err.

(* Converted type declarations: *)

#[global] Definition TurnOnFlag :=
  bool%type.

Inductive TrustFlag : Type :=
  | TrustPackage : GHC.Base.String -> TrustFlag
  | DistrustPackage : GHC.Base.String -> TrustFlag.

Inductive RtsOptsEnabled : Type :=
  | RtsOptsNone : RtsOptsEnabled
  | RtsOptsIgnore : RtsOptsEnabled
  | RtsOptsIgnoreAll : RtsOptsEnabled
  | RtsOptsSafeOnly : RtsOptsEnabled
  | RtsOptsAll : RtsOptsEnabled.

Inductive PkgDbRef : Type :=
  | GlobalPkgDb : PkgDbRef
  | UserPkgDb : PkgDbRef
  | PkgDbPath : GHC.Base.String -> PkgDbRef.

Inductive ParMakeCount : Type :=
  | ParMakeThisMany : BinNums.N -> ParMakeCount
  | ParMakeNumProcessors : ParMakeCount
  | ParMakeSemaphore : GHC.Base.String -> ParMakeCount.

Inductive PackageDBFlag : Type :=
  | PackageDB : PkgDbRef -> PackageDBFlag
  | NoUserPackageDB : PackageDBFlag
  | NoGlobalPackageDB : PackageDBFlag
  | ClearPackageDBs : PackageDBFlag.

Inductive PackageArg : Type :=
  | Mk_PackageArg : GHC.Base.String -> PackageArg
  | UnitIdArg : GHC.Unit.Types.Unit -> PackageArg.

Inductive OnOff a : Type := | On : a -> OnOff a | Off : a -> OnOff a.

Inductive ModRenaming : Type :=
  | Mk_ModRenaming (modRenamingWithImplicit : bool) (modRenamings
    : list (Language.Haskell.Syntax.Module.Name.ModuleName *
            Language.Haskell.Syntax.Module.Name.ModuleName)%type)
   : ModRenaming.

Inductive PackageFlag : Type :=
  | ExposePackage : GHC.Base.String -> PackageArg -> ModRenaming -> PackageFlag
  | HidePackage : GHC.Base.String -> PackageFlag.

Inductive LinkerInfo : Type :=
  | GnuLD : list GHC.Utils.CliOption.Option -> LinkerInfo
  | Mold : list GHC.Utils.CliOption.Option -> LinkerInfo
  | GnuGold : list GHC.Utils.CliOption.Option -> LinkerInfo
  | LlvmLLD : list GHC.Utils.CliOption.Option -> LinkerInfo
  | DarwinLD : list GHC.Utils.CliOption.Option -> LinkerInfo
  | SolarisLD : list GHC.Utils.CliOption.Option -> LinkerInfo
  | AixLD : list GHC.Utils.CliOption.Option -> LinkerInfo
  | UnknownLD : LinkerInfo.

Inductive IncludeSpecs : Type :=
  | IncludeSpecs (includePathsQuote : list GHC.Base.String) (includePathsGlobal
    : list GHC.Base.String) (includePathsQuoteImplicit : list GHC.Base.String)
   : IncludeSpecs.

Inductive IgnorePackageFlag : Type :=
  | IgnorePackage : GHC.Base.String -> IgnorePackageFlag.

Inductive GhcMode : Type :=
  | CompManager : GhcMode
  | OneShot : GhcMode
  | MkDepend : GhcMode.

Inductive GhcLink : Type :=
  | NoLink : GhcLink
  | LinkBinary : GhcLink
  | LinkInMemory : GhcLink
  | LinkDynLib : GhcLink
  | LinkStaticLib : GhcLink
  | LinkMergedObj : GhcLink.

Axiom FlushOut : Type.

Inductive DynamicTooState : Type :=
  | DT_Dont : DynamicTooState
  | DT_OK : DynamicTooState
  | DT_Dyn : DynamicTooState.

Inductive DynLibLoader : Type :=
  | Deployable : DynLibLoader
  | SystemDependent : DynLibLoader.

Axiom DynFlags : Type.

Record HasDynFlags__Dict (m : Type -> Type) := HasDynFlags__Dict_Build {
  getDynFlags__ : m DynFlags }.

#[global] Definition HasDynFlags (m : Type -> Type) :=
  forall r__, (HasDynFlags__Dict m -> r__) -> r__.
Existing Class HasDynFlags.

#[global] Definition getDynFlags `{g__0__ : HasDynFlags m} : m DynFlags :=
  g__0__ _ (getDynFlags__ m).

Record ContainsDynFlags__Dict (t : Type) := ContainsDynFlags__Dict_Build {
  extractDynFlags__ : t -> DynFlags }.

#[global] Definition ContainsDynFlags (t : Type) :=
  forall r__, (ContainsDynFlags__Dict t -> r__) -> r__.
Existing Class ContainsDynFlags.

#[global] Definition extractDynFlags `{g__0__ : ContainsDynFlags t}
   : t -> DynFlags :=
  g__0__ _ (extractDynFlags__ t).

Inductive CompilerInfo : Type :=
  | GCC : CompilerInfo
  | Clang : CompilerInfo
  | AppleClang : CompilerInfo
  | AppleClang51 : CompilerInfo
  | Emscripten : CompilerInfo
  | UnknownCC : CompilerInfo.

Arguments On {_} _.

Arguments Off {_} _.

Instance Default__RtsOptsEnabled : HsToCoq.Err.Default RtsOptsEnabled :=
  HsToCoq.Err.Build_Default _ RtsOptsNone.

Instance Default__PkgDbRef : HsToCoq.Err.Default PkgDbRef :=
  HsToCoq.Err.Build_Default _ GlobalPkgDb.

Instance Default__ParMakeCount : HsToCoq.Err.Default ParMakeCount :=
  HsToCoq.Err.Build_Default _ ParMakeNumProcessors.

Instance Default__PackageDBFlag : HsToCoq.Err.Default PackageDBFlag :=
  HsToCoq.Err.Build_Default _ NoUserPackageDB.

Instance Default__ModRenaming : HsToCoq.Err.Default ModRenaming :=
  HsToCoq.Err.Build_Default _ (Mk_ModRenaming HsToCoq.Err.default
                             HsToCoq.Err.default).

Instance Default__LinkerInfo : HsToCoq.Err.Default LinkerInfo :=
  HsToCoq.Err.Build_Default _ UnknownLD.

Instance Default__IncludeSpecs : HsToCoq.Err.Default IncludeSpecs :=
  HsToCoq.Err.Build_Default _ (IncludeSpecs HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__GhcMode : HsToCoq.Err.Default GhcMode :=
  HsToCoq.Err.Build_Default _ CompManager.

Instance Default__GhcLink : HsToCoq.Err.Default GhcLink :=
  HsToCoq.Err.Build_Default _ NoLink.

Instance Default__DynamicTooState : HsToCoq.Err.Default DynamicTooState :=
  HsToCoq.Err.Build_Default _ DT_Dont.

Instance Default__DynLibLoader : HsToCoq.Err.Default DynLibLoader :=
  HsToCoq.Err.Build_Default _ Deployable.

Instance Default__CompilerInfo : HsToCoq.Err.Default CompilerInfo :=
  HsToCoq.Err.Build_Default _ GCC.

#[global] Definition includePathsGlobal (arg_0__ : IncludeSpecs) :=
  let 'IncludeSpecs _ includePathsGlobal _ := arg_0__ in
  includePathsGlobal.

#[global] Definition includePathsQuote (arg_0__ : IncludeSpecs) :=
  let 'IncludeSpecs includePathsQuote _ _ := arg_0__ in
  includePathsQuote.

#[global] Definition includePathsQuoteImplicit (arg_0__ : IncludeSpecs) :=
  let 'IncludeSpecs _ _ includePathsQuoteImplicit := arg_0__ in
  includePathsQuoteImplicit.

(* Midamble *)

Instance Unpeel_IgnorePackageFlag : HsToCoq.Unpeel.Unpeel IgnorePackageFlag GHC.Base.String :=
  HsToCoq.Unpeel.Build_Unpeel _ _ (fun x => match x with | IgnorePackage y => y end) IgnorePackage.


Instance Default__DynFlags
   : HsToCoq.Err.Default DynFlags.
Admitted.

(* Converted value declarations: *)

(* Skipping instance `DynFlags.HasDynFlags__WriterT' of class
   `DynFlags.HasDynFlags' *)

(* Skipping instance `DynFlags.HasDynFlags__ReaderT' of class
   `DynFlags.HasDynFlags' *)

(* Skipping instance `DynFlags.HasDynFlags__MaybeT' of class
   `DynFlags.HasDynFlags' *)

(* Skipping instance `DynFlags.HasDynFlags__ExceptT' of class
   `DynFlags.HasDynFlags' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__OnOff' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__GhcMode' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__PackageArg' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__ModRenaming' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__PackageFlag' *)

(* Skipping definition `DynFlags.initDynFlags' *)

Axiom defaultDynFlags : GHC.Settings.Settings -> DynFlags.

(* Skipping definition `DynFlags.defaultFatalMessager' *)

Axiom defaultFlushOut : FlushOut.

(* Skipping definition `DynFlags.flattenExtensionFlags' *)

Axiom isOneShot : GhcMode -> bool.

Axiom isNoLink : GhcLink -> bool.

Axiom packageFlagsChanged : DynFlags -> DynFlags -> bool.

Axiom positionIndependent : DynFlags -> bool.

Axiom dynamicTooState : DynFlags -> DynamicTooState.

Axiom setDynamicNow : DynFlags -> DynFlags.

Axiom addGlobalInclude : IncludeSpecs -> list GHC.Base.String -> IncludeSpecs.

Axiom addQuoteInclude : IncludeSpecs -> list GHC.Base.String -> IncludeSpecs.

Axiom addImplicitQuoteInclude : IncludeSpecs ->
                                list GHC.Base.String -> IncludeSpecs.

Axiom flattenIncludes : IncludeSpecs -> list GHC.Base.String.

Axiom hasPprDebug : DynFlags -> bool.

Axiom hasNoDebugOutput : DynFlags -> bool.

Axiom hasNoStateHack : DynFlags -> bool.

Axiom hasNoOptCoercion : DynFlags -> bool.

(* Skipping definition `DynFlags.dopt' *)

Axiom dopt_set : DynFlags -> GHC.Driver.Flags.DumpFlag -> DynFlags.

Axiom dopt_unset : DynFlags -> GHC.Driver.Flags.DumpFlag -> DynFlags.

Axiom gopt : GHC.Driver.Flags.GeneralFlag -> DynFlags -> bool.

Axiom gopt_set : DynFlags -> GHC.Driver.Flags.GeneralFlag -> DynFlags.

(* Skipping definition `DynFlags.gopt_unset' *)

(* Skipping definition `DynFlags.wopt' *)

(* Skipping definition `DynFlags.wopt_set' *)

(* Skipping definition `DynFlags.wopt_unset' *)

Axiom wopt_fatal : GHC.Driver.Flags.WarningFlag -> DynFlags -> bool.

Axiom wopt_set_fatal : DynFlags -> GHC.Driver.Flags.WarningFlag -> DynFlags.

Axiom wopt_unset_fatal : DynFlags -> GHC.Driver.Flags.WarningFlag -> DynFlags.

Axiom wopt_set_all_custom : DynFlags -> DynFlags.

Axiom wopt_unset_all_custom : DynFlags -> DynFlags.

Axiom wopt_set_all_fatal_custom : DynFlags -> DynFlags.

Axiom wopt_unset_all_fatal_custom : DynFlags -> DynFlags.

Axiom wopt_set_custom : DynFlags -> BasicTypes.WarningCategory -> DynFlags.

Axiom wopt_unset_custom : DynFlags -> BasicTypes.WarningCategory -> DynFlags.

Axiom wopt_set_fatal_custom : DynFlags ->
                              BasicTypes.WarningCategory -> DynFlags.

Axiom wopt_unset_fatal_custom : DynFlags ->
                                BasicTypes.WarningCategory -> DynFlags.

Axiom wopt_any_custom : DynFlags -> bool.

(* Skipping definition `DynFlags.xopt' *)

(* Skipping definition `DynFlags.xopt_set' *)

(* Skipping definition `DynFlags.xopt_unset' *)

Axiom xopt_set_unlessExplSpec : GHC.LanguageExtensions.Type.Extension ->
                                (DynFlags -> GHC.LanguageExtensions.Type.Extension -> DynFlags) ->
                                DynFlags -> DynFlags.

Axiom xopt_DuplicateRecordFields : DynFlags -> FieldLabel.DuplicateRecordFields.

Axiom xopt_FieldSelectors : DynFlags -> FieldLabel.FieldSelectors.

(* Skipping definition `DynFlags.lang_set' *)

Axiom defaultFlags : GHC.Settings.Settings -> list GHC.Driver.Flags.GeneralFlag.

Axiom validHoleFitDefaults : list GHC.Driver.Flags.GeneralFlag.

Axiom optLevelFlags : list (list BinNums.N * GHC.Driver.Flags.GeneralFlag)%type.

Axiom turnOn : TurnOnFlag.

Axiom turnOff : TurnOnFlag.

(* Skipping definition `DynFlags.default_PIC' *)

(* Skipping definition `DynFlags.languageExtensions' *)

Axiom ways : DynFlags -> GHC.Platform.Ways.Ways.

Axiom targetProfile : DynFlags -> GHC.Platform.Profile.Profile.

Axiom programName : DynFlags -> GHC.Base.String.

Axiom projectVersion : DynFlags -> GHC.Base.String.

Axiom ghcUsagePath : DynFlags -> GHC.Base.String.

Axiom ghciUsagePath : DynFlags -> GHC.Base.String.

Axiom topDir : DynFlags -> GHC.Base.String.

Axiom toolDir : DynFlags -> option GHC.Base.String.

Axiom extraGccViaCFlags : DynFlags -> list GHC.Base.String.

Axiom globalPackageDatabasePath : DynFlags -> GHC.Base.String.

(* Skipping definition `DynFlags.versionedAppDir' *)

Axiom versionedFilePath : GHC.Platform.ArchOS.ArchOS -> GHC.Base.String.

Axiom initSDocContext : DynFlags ->
                        Outputable.PprStyle -> Outputable.SDocContext.

Axiom initDefaultSDocContext : DynFlags -> Outputable.SDocContext.

Axiom initPromotionTickContext : DynFlags -> Outputable.PromotionTickContext.

Axiom isSse4_2Enabled : DynFlags -> bool.

Axiom isAvxEnabled : DynFlags -> bool.

Axiom isAvx2Enabled : DynFlags -> bool.

Axiom isAvx512cdEnabled : DynFlags -> bool.

Axiom isAvx512erEnabled : DynFlags -> bool.

Axiom isAvx512fEnabled : DynFlags -> bool.

Axiom isAvx512pfEnabled : DynFlags -> bool.

Axiom isFmaEnabled : DynFlags -> bool.

Axiom isBmiEnabled : DynFlags -> bool.

Axiom isBmi2Enabled : DynFlags -> bool.

(* External variables:
     Type bool list op_zt__ option BasicTypes.WarningCategory BinNums.N
     FieldLabel.DuplicateRecordFields FieldLabel.FieldSelectors GHC.Base.String
     GHC.Driver.Flags.DumpFlag GHC.Driver.Flags.GeneralFlag
     GHC.Driver.Flags.WarningFlag GHC.LanguageExtensions.Type.Extension
     GHC.Platform.ArchOS.ArchOS GHC.Platform.Profile.Profile GHC.Platform.Ways.Ways
     GHC.Settings.Settings GHC.Unit.Types.Unit GHC.Utils.CliOption.Option
     HsToCoq.Err.Build_Default HsToCoq.Err.Default HsToCoq.Err.default
     Language.Haskell.Syntax.Module.Name.ModuleName Outputable.PprStyle
     Outputable.PromotionTickContext Outputable.SDocContext
*)
