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

Require Coq.Init.Datatypes.
Require GHC.Base.
Require GHC.Builtin.Uniques.
Require GHC.Data.List.Infinite.
Require GHC.Enum.
Require GHC.Num.
Require GHC.Types.Name.Reader.
Require Name.
Require OccName.
Require SrcLoc.
Require Unique.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

#[global] Definition int8X16PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #300.

#[global] Definition int16X8PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #301.

#[global] Definition int32X4PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #302.

#[global] Definition int64X2PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #303.

#[global] Definition int8X32PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #304.

#[global] Definition int16X16PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #305.

#[global] Definition int32X8PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #306.

#[global] Definition int64X4PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #307.

#[global] Definition int8X64PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #308.

#[global] Definition int16X32PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #309.

#[global] Definition int32X16PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #310.

#[global] Definition int64X8PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #311.

#[global] Definition word8X16PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #312.

#[global] Definition word16X8PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #313.

#[global] Definition word32X4PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #314.

#[global] Definition word64X2PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #315.

#[global] Definition word8X32PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #316.

#[global] Definition word16X16PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #317.

#[global] Definition word32X8PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #318.

#[global] Definition word64X4PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #319.

#[global] Definition word8X64PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #320.

#[global] Definition word16X32PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #321.

#[global] Definition word32X16PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #322.

#[global] Definition word64X8PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #323.

#[global] Definition floatX4PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #324.

#[global] Definition doubleX2PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #325.

#[global] Definition floatX8PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #326.

#[global] Definition doubleX4PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #327.

#[global] Definition floatX16PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #328.

#[global] Definition doubleX8PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #329.

Axiom allNameStrings : GHC.Data.List.Infinite.Infinite GHC.Base.String.

#[global] Definition allNameStringList : list GHC.Base.String :=
  GHC.Data.List.Infinite.toList allNameStrings.

#[global] Definition itName : Unique.Unique -> SrcLoc.SrcSpan -> Name.Name :=
  fun uniq loc =>
    Name.mkInternalName uniq (OccName.mkOccNameFS OccName.varName
                              (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "it"))) loc.

#[global] Definition unboundKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #158.

#[global] Definition mkUnboundName : OccName.OccName -> Name.Name :=
  fun occ => Name.mkInternalName unboundKey occ SrcLoc.noSrcSpan.

#[global] Definition isUnboundName : Name.Name -> bool :=
  fun name => Unique.hasKey name unboundKey.

Axiom basicKnownKeyNames : list Name.Name.

Axiom genericTyConNames : list Name.Name.

#[global] Definition mkPrimModule
   : GHC.Data.FastString.FastString -> GHC.Unit.Types.Module :=
  fun m =>
    GHC.Unit.Types.mkModule GHC.Unit.Types.primUnit
    (Language.Haskell.Syntax.Module.Name.mkModuleNameFS m).

#[global] Definition gHC_PRIM : GHC.Unit.Types.Module :=
  mkPrimModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "GHC.Prim")).

#[global] Definition gHC_PRIM_PANIC : GHC.Unit.Types.Module :=
  mkPrimModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                           "GHC.Prim.Panic")).

#[global] Definition gHC_TYPES : GHC.Unit.Types.Module :=
  mkPrimModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "GHC.Types")).

#[global] Definition gHC_MAGIC : GHC.Unit.Types.Module :=
  mkPrimModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "GHC.Magic")).

#[global] Definition gHC_MAGIC_DICT : GHC.Unit.Types.Module :=
  mkPrimModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                           "GHC.Magic.Dict")).

#[global] Definition gHC_CSTRING : GHC.Unit.Types.Module :=
  mkPrimModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "GHC.CString")).

#[global] Definition gHC_CLASSES : GHC.Unit.Types.Module :=
  mkPrimModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "GHC.Classes")).

#[global] Definition gHC_PRIMOPWRAPPERS : GHC.Unit.Types.Module :=
  mkPrimModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                           "GHC.PrimopWrappers")).

#[global] Definition gHC_INTERNAL_TUPLE : GHC.Unit.Types.Module :=
  mkPrimModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "GHC.Tuple")).

#[global] Definition mkBaseModule_
   : Language.Haskell.Syntax.Module.Name.ModuleName -> GHC.Unit.Types.Module :=
  fun m => GHC.Unit.Types.mkModule GHC.Unit.Types.baseUnit m.

#[global] Definition pRELUDE_NAME
   : Language.Haskell.Syntax.Module.Name.ModuleName :=
  Language.Haskell.Syntax.Module.Name.mkModuleNameFS (GHC.Data.FastString.fsLit
                                                      (GHC.Base.hs_string__ "Prelude")).

#[global] Definition pRELUDE : GHC.Unit.Types.Module :=
  mkBaseModule_ pRELUDE_NAME.

#[global] Definition mkBaseModule
   : GHC.Data.FastString.FastString -> GHC.Unit.Types.Module :=
  fun m => mkBaseModule_ (Language.Haskell.Syntax.Module.Name.mkModuleNameFS m).

#[global] Definition dATA_LIST : GHC.Unit.Types.Module :=
  mkBaseModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "Data.List")).

#[global] Definition cONTROL_MONAD_ZIP : GHC.Unit.Types.Module :=
  mkBaseModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                           "Control.Monad.Zip")).

#[global] Definition mkBignumModule
   : GHC.Data.FastString.FastString -> GHC.Unit.Types.Module :=
  fun m =>
    GHC.Unit.Types.mkModule GHC.Unit.Types.bignumUnit
    (Language.Haskell.Syntax.Module.Name.mkModuleNameFS m).

#[global] Definition gHC_INTERNAL_NUM_INTEGER : GHC.Unit.Types.Module :=
  mkBignumModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                             "GHC.Num.Integer")).

#[global] Definition gHC_INTERNAL_NUM_NATURAL : GHC.Unit.Types.Module :=
  mkBignumModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                             "GHC.Num.Natural")).

#[global] Definition gHC_INTERNAL_NUM_BIGNAT : GHC.Unit.Types.Module :=
  mkBignumModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                             "GHC.Num.BigNat")).

#[global] Definition mkGhcInternalModule_
   : Language.Haskell.Syntax.Module.Name.ModuleName -> GHC.Unit.Types.Module :=
  fun m => GHC.Unit.Types.mkModule GHC.Unit.Types.ghcInternalUnit m.

#[global] Definition mkGhcInternalModule
   : GHC.Data.FastString.FastString -> GHC.Unit.Types.Module :=
  fun m =>
    mkGhcInternalModule_ (Language.Haskell.Syntax.Module.Name.mkModuleNameFS m).

#[global] Definition gHC_INTERNAL_BASE : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Base")).

#[global] Definition gHC_INTERNAL_ENUM : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Enum")).

#[global] Definition gHC_INTERNAL_GHCI : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.GHCi")).

#[global] Definition gHC_INTERNAL_GHCI_HELPERS : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.GHCi.Helpers")).

#[global] Definition gHC_INTERNAL_SHOW : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Show")).

#[global] Definition gHC_INTERNAL_READ : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Read")).

#[global] Definition gHC_INTERNAL_NUM : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Num")).

#[global] Definition gHC_INTERNAL_MAYBE : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Maybe")).

#[global] Definition gHC_INTERNAL_LIST : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.List")).

#[global] Definition gHC_INTERNAL_DATA_EITHER : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Data.Either")).

#[global] Definition gHC_INTERNAL_DATA_STRING : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Data.String")).

#[global] Definition gHC_INTERNAL_DATA_FOLDABLE : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Data.Foldable")).

#[global] Definition gHC_INTERNAL_DATA_TRAVERSABLE : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Data.Traversable")).

#[global] Definition gHC_INTERNAL_CONC : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.GHC.Conc")).

#[global] Definition gHC_INTERNAL_IO : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.IO")).

#[global] Definition gHC_INTERNAL_IO_Exception : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.IO.Exception")).

#[global] Definition gHC_INTERNAL_ST : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.ST")).

#[global] Definition gHC_INTERNAL_IX : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Ix")).

#[global] Definition gHC_INTERNAL_STABLE : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Stable")).

#[global] Definition gHC_INTERNAL_PTR : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Ptr")).

#[global] Definition gHC_INTERNAL_ERR : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Err")).

#[global] Definition gHC_INTERNAL_REAL : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Real")).

#[global] Definition gHC_INTERNAL_FLOAT : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Float")).

#[global] Definition gHC_INTERNAL_TOP_HANDLER : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.TopHandler")).

#[global] Definition gHC_INTERNAL_SYSTEM_IO : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.System.IO")).

#[global] Definition gHC_INTERNAL_DYNAMIC : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Data.Dynamic")).

#[global] Definition gHC_INTERNAL_TYPEABLE : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Data.Typeable")).

#[global] Definition gHC_INTERNAL_TYPEABLE_INTERNAL : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Data.Typeable.Internal")).

#[global] Definition gHC_INTERNAL_DATA_DATA : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Data.Data")).

#[global] Definition gHC_INTERNAL_READ_PREC : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Text.ParserCombinators.ReadPrec")).

#[global] Definition gHC_INTERNAL_LEX : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Text.Read.Lex")).

#[global] Definition gHC_INTERNAL_INT : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Int")).

#[global] Definition gHC_INTERNAL_WORD : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Word")).

#[global] Definition gHC_INTERNAL_MONAD : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Control.Monad")).

#[global] Definition gHC_INTERNAL_MONAD_FIX : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Control.Monad.Fix")).

#[global] Definition gHC_INTERNAL_MONAD_FAIL : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Control.Monad.Fail")).

#[global] Definition gHC_INTERNAL_ARROW : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Control.Arrow")).

#[global] Definition gHC_INTERNAL_DESUGAR : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Desugar")).

#[global] Definition gHC_INTERNAL_RANDOM : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.System.Random")).

#[global] Definition gHC_INTERNAL_EXTS : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Exts")).

#[global] Definition gHC_INTERNAL_IS_LIST : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.IsList")).

#[global] Definition gHC_INTERNAL_CONTROL_EXCEPTION_BASE
   : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Control.Exception.Base")).

#[global] Definition gHC_INTERNAL_EXCEPTION_CONTEXT : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Exception.Context")).

#[global] Definition gHC_INTERNAL_GENERICS : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Generics")).

#[global] Definition gHC_INTERNAL_TYPEERROR : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.TypeError")).

#[global] Definition gHC_INTERNAL_TYPELITS : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.TypeLits")).

#[global] Definition gHC_INTERNAL_TYPELITS_INTERNAL : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.TypeLits.Internal")).

#[global] Definition gHC_INTERNAL_TYPENATS : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.TypeNats")).

#[global] Definition gHC_INTERNAL_TYPENATS_INTERNAL : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.TypeNats.Internal")).

#[global] Definition gHC_INTERNAL_DATA_COERCE : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Data.Coerce")).

#[global] Definition gHC_INTERNAL_DEBUG_TRACE : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Debug.Trace")).

#[global] Definition gHC_INTERNAL_UNSAFE_COERCE : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Unsafe.Coerce")).

#[global] Definition gHC_INTERNAL_FOREIGN_C_CONSTPTR : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Foreign.C.ConstPtr")).

#[global] Definition gHC_INTERNAL_SRCLOC : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.SrcLoc")).

#[global] Definition gHC_INTERNAL_STACK : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Stack")).

#[global] Definition gHC_INTERNAL_STACK_TYPES : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Stack.Types")).

#[global] Definition gHC_INTERNAL_STATICPTR : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.StaticPtr")).

#[global] Definition gHC_INTERNAL_STATICPTR_INTERNAL : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.StaticPtr.Internal")).

#[global] Definition gHC_INTERNAL_FINGERPRINT_TYPE : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Fingerprint.Type")).

#[global] Definition gHC_INTERNAL_OVER_LABELS : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.OverloadedLabels")).

#[global] Definition gHC_INTERNAL_RECORDS : GHC.Unit.Types.Module :=
  mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "GHC.Internal.Records")).

#[global] Definition mkExperimentalModule
   : GHC.Data.FastString.FastString -> GHC.Unit.Types.Module :=
  fun m =>
    GHC.Unit.Types.mkModule GHC.Unit.Types.experimentalUnit
    (Language.Haskell.Syntax.Module.Name.mkModuleNameFS m).

#[global] Definition dATA_TUPLE_EXPERIMENTAL : GHC.Unit.Types.Module :=
  mkExperimentalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                   "Data.Tuple.Experimental")).

#[global] Definition dATA_SUM_EXPERIMENTAL : GHC.Unit.Types.Module :=
  mkExperimentalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                   "Data.Sum.Experimental")).

#[global] Definition mkMainModule
   : GHC.Data.FastString.FastString -> GHC.Unit.Types.Module :=
  fun m =>
    GHC.Unit.Types.mkModule GHC.Unit.Types.mainUnit
    (Language.Haskell.Syntax.Module.Name.mkModuleNameFS m).

#[global] Definition rOOT_MAIN : GHC.Unit.Types.Module :=
  mkMainModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ ":Main")).

Axiom mkInteractiveModule : GHC.Base.String -> GHC.Unit.Types.Module.

#[global] Definition mAIN_NAME
   : Language.Haskell.Syntax.Module.Name.ModuleName :=
  Language.Haskell.Syntax.Module.Name.mkModuleNameFS (GHC.Data.FastString.fsLit
                                                      (GHC.Base.hs_string__ "Main")).

#[global] Definition mkThisGhcModule_
   : Language.Haskell.Syntax.Module.Name.ModuleName -> GHC.Unit.Types.Module :=
  fun m => GHC.Unit.Types.mkModule GHC.Unit.Types.thisGhcUnit m.

#[global] Definition mkThisGhcModule
   : GHC.Data.FastString.FastString -> GHC.Unit.Types.Module :=
  fun m =>
    mkThisGhcModule_ (Language.Haskell.Syntax.Module.Name.mkModuleNameFS m).

#[global] Definition mkMainModule_
   : Language.Haskell.Syntax.Module.Name.ModuleName -> GHC.Unit.Types.Module :=
  fun m => GHC.Unit.Types.mkModule GHC.Unit.Types.mainUnit m.

Axiom RdrName : Type.

Axiom main_RDR_Unqual : RdrName.

#[global] Definition eqClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #167.

#[global] Definition mk_known_key_name
   : OccName.NameSpace ->
     GHC.Unit.Types.Module ->
     GHC.Data.FastString.FastString -> Unique.Unique -> Name.Name :=
  fun space modu str unique =>
    Name.mkExternalName unique modu (OccName.mkOccNameFS space str)
    SrcLoc.noSrcSpan.

#[global] Definition varQual
   : GHC.Unit.Types.Module ->
     GHC.Data.FastString.FastString -> Unique.Unique -> Name.Name :=
  fun modu str unique => mk_known_key_name OccName.varName modu str unique.

#[global] Definition eqName : Name.Name :=
  varQual gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "=="))
  eqClassOpKey.

Axiom nameRdrName : Name.Name -> RdrName.

#[global] Definition eq_RDR : RdrName :=
  nameRdrName eqName.

#[global] Definition geClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #168.

#[global] Definition geName : Name.Name :=
  varQual gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ ">="))
  geClassOpKey.

#[global] Definition ge_RDR : RdrName :=
  nameRdrName geName.

Axiom varQual_RDR : GHC.Unit.Types.Module ->
                    GHC.Data.FastString.FastString -> RdrName.

#[global] Definition le_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "<=")).

#[global] Definition lt_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "<")).

#[global] Definition gt_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ ">")).

#[global] Definition compare_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                      "compare")).

#[global] Definition dcQual
   : GHC.Unit.Types.Module ->
     GHC.Data.FastString.FastString -> Unique.Unique -> Name.Name :=
  fun modu str unique => mk_known_key_name OccName.dataName modu str unique.

#[global] Definition ordLTDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #27.

#[global] Definition ordLTDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "LT"))
  ordLTDataConKey.

#[global] Definition ltTag_RDR : RdrName :=
  nameRdrName ordLTDataConName.

#[global] Definition ordEQDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #28.

#[global] Definition ordEQDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "EQ"))
  ordEQDataConKey.

#[global] Definition eqTag_RDR : RdrName :=
  nameRdrName ordEQDataConName.

#[global] Definition ordGTDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #29.

#[global] Definition ordGTDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "GT"))
  ordGTDataConKey.

#[global] Definition gtTag_RDR : RdrName :=
  nameRdrName ordGTDataConName.

#[global] Definition mapIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #121.

#[global] Definition mapName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "map")) mapIdKey.

#[global] Definition map_RDR : RdrName :=
  nameRdrName mapName.

#[global] Definition appendIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #4.

#[global] Definition appendName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "++")) appendIdKey.

#[global] Definition append_RDR : RdrName :=
  nameRdrName appendName.

#[global] Definition foldrIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #6.

#[global] Definition foldrName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "foldr")) foldrIdKey.

#[global] Definition foldr_RDR : RdrName :=
  nameRdrName foldrName.

#[global] Definition buildIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #5.

#[global] Definition buildName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "build")) buildIdKey.

#[global] Definition build_RDR : RdrName :=
  nameRdrName buildName.

#[global] Definition returnMClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #174.

#[global] Definition returnMName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "return")) returnMClassOpKey.

#[global] Definition returnM_RDR : RdrName :=
  nameRdrName returnMName.

#[global] Definition bindMClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #171.

#[global] Definition bindMName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        ">>=")) bindMClassOpKey.

#[global] Definition bindM_RDR : RdrName :=
  nameRdrName bindMName.

#[global] Definition failMClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #176.

#[global] Definition failMName : Name.Name :=
  varQual gHC_INTERNAL_MONAD_FAIL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                              "fail")) failMClassOpKey.

#[global] Definition failM_RDR : RdrName :=
  nameRdrName failMName.

#[global] Definition leftDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #25.

#[global] Definition leftDataConName : Name.Name :=
  dcQual gHC_INTERNAL_DATA_EITHER (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                              "Left")) leftDataConKey.

#[global] Definition left_RDR : RdrName :=
  nameRdrName leftDataConName.

#[global] Definition rightDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #26.

#[global] Definition rightDataConName : Name.Name :=
  dcQual gHC_INTERNAL_DATA_EITHER (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                              "Right")) rightDataConKey.

#[global] Definition right_RDR : RdrName :=
  nameRdrName rightDataConName.

#[global] Definition fromEnum_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "fromEnum")).

#[global] Definition toEnum_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "toEnum")).

#[global] Definition enumFromClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #163.

#[global] Definition enumFromName : Name.Name :=
  varQual gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "enumFrom")) enumFromClassOpKey.

#[global] Definition enumFrom_RDR : RdrName :=
  nameRdrName enumFromName.

#[global] Definition enumFromToClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #165.

#[global] Definition enumFromToName : Name.Name :=
  varQual gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "enumFromTo")) enumFromToClassOpKey.

#[global] Definition enumFromTo_RDR : RdrName :=
  nameRdrName enumFromToName.

#[global] Definition enumFromThenClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #164.

#[global] Definition enumFromThenName : Name.Name :=
  varQual gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "enumFromThen")) enumFromThenClassOpKey.

#[global] Definition enumFromThen_RDR : RdrName :=
  nameRdrName enumFromThenName.

#[global] Definition enumFromThenToClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #166.

#[global] Definition enumFromThenToName : Name.Name :=
  varQual gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "enumFromThenTo")) enumFromThenToClassOpKey.

#[global] Definition enumFromThenTo_RDR : RdrName :=
  nameRdrName enumFromThenToName.

#[global] Definition times_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_NUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "*")).

#[global] Definition plus_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_NUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "+")).

#[global] Definition compose_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            ".")).

#[global] Definition and_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "&&")).

#[global] Definition not_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                      "not")).

#[global] Definition dataToTag_RDR : RdrName :=
  varQual_RDR gHC_MAGIC (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                    "dataToTag#")).

#[global] Definition succ_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "succ")).

#[global] Definition pred_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "pred")).

#[global] Definition minBound_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "minBound")).

#[global] Definition maxBound_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "maxBound")).

#[global] Definition range_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_IX (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                          "range")).

#[global] Definition inRange_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_IX (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                          "inRange")).

#[global] Definition index_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_IX (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                          "index")).

#[global] Definition unsafeIndex_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_IX (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                          "unsafeIndex")).

#[global] Definition unsafeRangeSize_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_IX (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                          "unsafeRangeSize")).

#[global] Definition readList_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "readList")).

#[global] Definition readListDefault_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "readListDefault")).

#[global] Definition readListPrec_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "readListPrec")).

#[global] Definition readListPrecDefault_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "readListPrecDefault")).

#[global] Definition readPrec_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "readPrec")).

#[global] Definition parens_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "parens")).

#[global] Definition choose_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "choose")).

#[global] Definition lexP_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "lexP")).

#[global] Definition expectP_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "expectP")).

#[global] Definition readField_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "readField")).

#[global] Definition readFieldHash_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "readFieldHash")).

#[global] Definition readSymField_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "readSymField")).

Axiom dataQual_RDR : GHC.Unit.Types.Module ->
                     GHC.Data.FastString.FastString -> RdrName.

#[global] Definition punc_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_LEX (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "Punc")).

#[global] Definition ident_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_LEX (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "Ident")).

#[global] Definition symbol_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_LEX (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "Symbol")).

#[global] Definition step_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ_PREC (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "step")).

#[global] Definition alt_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ_PREC (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "+++")).

#[global] Definition reset_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ_PREC (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "reset")).

#[global] Definition prec_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ_PREC (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "prec")).

#[global] Definition pfail_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_READ_PREC (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "pfail")).

#[global] Definition showsPrec_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_SHOW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "showsPrec")).

#[global] Definition shows_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_SHOW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "shows")).

#[global] Definition showString_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_SHOW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "showString")).

#[global] Definition showSpace_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_SHOW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "showSpace")).

#[global] Definition showCommaSpace_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_SHOW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "showCommaSpace")).

#[global] Definition showParen_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_SHOW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "showParen")).

#[global] Definition error_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_ERR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "error")).

#[global] Definition u1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "U1")).

#[global] Definition par1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "Par1")).

#[global] Definition rec1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "Rec1")).

#[global] Definition k1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "K1")).

#[global] Definition m1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "M1")).

#[global] Definition l1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "L1")).

#[global] Definition r1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "R1")).

#[global] Definition prodDataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ ":*:")).

#[global] Definition comp1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "Comp1")).

#[global] Definition fieldQual_RDR
   : GHC.Unit.Types.Module ->
     GHC.Data.FastString.FastString -> GHC.Data.FastString.FastString -> RdrName :=
  fun mod_ con str =>
    GHC.Types.Name.Reader.mkOrig mod_ (OccName.mkOccNameFS (OccName.fieldName con)
                                       str).

#[global] Definition unPar1_RDR : RdrName :=
  fieldQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                       (GHC.Base.hs_string__ "Par1")) (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                                                                  "unPar1")).

#[global] Definition unRec1_RDR : RdrName :=
  fieldQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                       (GHC.Base.hs_string__ "Rec1")) (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                                                                  "unRec1")).

#[global] Definition unK1_RDR : RdrName :=
  fieldQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                       (GHC.Base.hs_string__ "K1")) (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                                                                "unK1")).

#[global] Definition unComp1_RDR : RdrName :=
  fieldQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                       (GHC.Base.hs_string__ "Comp1")) (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                                                                   "unComp1")).

#[global] Definition from_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "from")).

#[global] Definition from1_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "from1")).

#[global] Definition to_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "to")).

#[global] Definition to1_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "to1")).

#[global] Definition datatypeName_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "datatypeName")).

#[global] Definition moduleName_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "moduleName")).

#[global] Definition packageName_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "packageName")).

#[global] Definition isNewtypeName_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "isNewtype")).

#[global] Definition selName_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "selName")).

#[global] Definition conName_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "conName")).

#[global] Definition conFixity_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "conFixity")).

#[global] Definition conIsRecord_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "conIsRecord")).

#[global] Definition prefixDataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "Prefix")).

#[global] Definition infixDataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "Infix")).

#[global] Definition leftAssociativeDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #56.

#[global] Definition leftAssociativeDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "LeftAssociative")) leftAssociativeDataConKey.

#[global] Definition leftAssocDataCon_RDR : RdrName :=
  nameRdrName leftAssociativeDataConName.

#[global] Definition rightAssociativeDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #57.

#[global] Definition rightAssociativeDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "RightAssociative")) rightAssociativeDataConKey.

#[global] Definition rightAssocDataCon_RDR : RdrName :=
  nameRdrName rightAssociativeDataConName.

#[global] Definition notAssociativeDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #58.

#[global] Definition notAssociativeDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "NotAssociative")) notAssociativeDataConKey.

#[global] Definition notAssocDataCon_RDR : RdrName :=
  nameRdrName notAssociativeDataConName.

#[global] Definition uAddrDataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "UAddr")).

#[global] Definition uCharDataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "UChar")).

#[global] Definition uDoubleDataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "UDouble")).

#[global] Definition uFloatDataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "UFloat")).

#[global] Definition uIntDataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "UInt")).

#[global] Definition uWordDataCon_RDR : RdrName :=
  dataQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "UWord")).

#[global] Definition uAddrHash_RDR : RdrName :=
  fieldQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                       (GHC.Base.hs_string__ "UAddr")) (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                                                                   "uAddr#")).

#[global] Definition uCharHash_RDR : RdrName :=
  fieldQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                       (GHC.Base.hs_string__ "UChar")) (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                                                                   "uChar#")).

#[global] Definition uDoubleHash_RDR : RdrName :=
  fieldQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                       (GHC.Base.hs_string__ "UDouble")) (GHC.Data.FastString.fsLit
                                                                          (GHC.Base.hs_string__ "uDouble#")).

#[global] Definition uFloatHash_RDR : RdrName :=
  fieldQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                       (GHC.Base.hs_string__ "UFloat")) (GHC.Data.FastString.fsLit
                                                                         (GHC.Base.hs_string__ "uFloat#")).

#[global] Definition uIntHash_RDR : RdrName :=
  fieldQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                       (GHC.Base.hs_string__ "UInt")) (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                                                                  "uInt#")).

#[global] Definition uWordHash_RDR : RdrName :=
  fieldQual_RDR gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit
                                       (GHC.Base.hs_string__ "UWord")) (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                                                                   "uWord#")).

#[global] Definition fmapClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #173.

#[global] Definition fmapName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "fmap")) fmapClassOpKey.

#[global] Definition fmap_RDR : RdrName :=
  nameRdrName fmapName.

#[global] Definition replace_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "<$")).

#[global] Definition pureAClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #752.

#[global] Definition pureAName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "pure")) pureAClassOpKey.

#[global] Definition pure_RDR : RdrName :=
  nameRdrName pureAName.

#[global] Definition apAClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #751.

#[global] Definition apAName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "<*>")) apAClassOpKey.

#[global] Definition ap_RDR : RdrName :=
  nameRdrName apAName.

#[global] Definition liftA2_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "liftA2")).

#[global] Definition foldable_foldr_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_DATA_FOLDABLE (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "foldr")).

#[global] Definition foldMap_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_DATA_FOLDABLE (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "foldMap")).

#[global] Definition null_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_DATA_FOLDABLE (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "null")).

#[global] Definition all_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_DATA_FOLDABLE (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "all")).

#[global] Definition traverse_RDR : RdrName :=
  varQual_RDR gHC_INTERNAL_DATA_TRAVERSABLE (GHC.Data.FastString.fsLit
                                             (GHC.Base.hs_string__ "traverse")).

#[global] Definition memptyClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #555.

#[global] Definition memptyName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "mempty")) memptyClassOpKey.

#[global] Definition mempty_RDR : RdrName :=
  nameRdrName memptyName.

#[global] Definition mappendClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #556.

#[global] Definition mappendName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "mappend")) mappendClassOpKey.

#[global] Definition mappend_RDR : RdrName :=
  nameRdrName mappendName.

Axiom tcQual_RDR : GHC.Unit.Types.Module ->
                   GHC.Data.FastString.FastString -> RdrName.

Axiom clsQual_RDR : GHC.Unit.Types.Module ->
                    GHC.Data.FastString.FastString -> RdrName.

#[global] Definition wildCardKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #0.

#[global] Definition wildCardName : Name.Name :=
  Name.mkSystemVarName wildCardKey (GHC.Data.FastString.fsLit
                                    (GHC.Base.hs_string__ "wild")).

#[global] Definition runMainKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #102.

#[global] Definition runMainIOName : Name.Name :=
  varQual gHC_INTERNAL_TOP_HANDLER (GHC.Data.FastString.fsLit
                                    (GHC.Base.hs_string__ "runMainIO")) runMainKey.

#[global] Definition runRWKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #107.

#[global] Definition runRWName : Name.Name :=
  varQual gHC_MAGIC (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "runRW#"))
  runRWKey.

#[global] Definition orderingTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #32.

#[global] Definition tcQual
   : GHC.Unit.Types.Module ->
     GHC.Data.FastString.FastString -> Unique.Unique -> Name.Name :=
  fun modu str unique => mk_known_key_name OccName.tcName modu str unique.

#[global] Definition orderingTyConName : Name.Name :=
  tcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "Ordering"))
  orderingTyConKey.

#[global] Definition specTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #185.

#[global] Definition specTyConName : Name.Name :=
  tcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "SPEC"))
  specTyConKey.

#[global] Definition eitherTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #84.

#[global] Definition eitherTyConName : Name.Name :=
  tcQual gHC_INTERNAL_DATA_EITHER (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                              "Either")) eitherTyConKey.

#[global] Definition voidTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #85.

#[global] Definition voidTyConName : Name.Name :=
  tcQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                       "Void")) voidTyConKey.

#[global] Definition v1TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #135.

#[global] Definition v1TyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "V1")) v1TyConKey.

#[global] Definition u1TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #136.

#[global] Definition u1TyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "U1")) u1TyConKey.

#[global] Definition par1TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #137.

#[global] Definition par1TyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "Par1")) par1TyConKey.

#[global] Definition rec1TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #138.

#[global] Definition rec1TyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "Rec1")) rec1TyConKey.

#[global] Definition k1TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #139.

#[global] Definition k1TyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "K1")) k1TyConKey.

#[global] Definition m1TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #140.

#[global] Definition m1TyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "M1")) m1TyConKey.

#[global] Definition sumTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #141.

#[global] Definition sumTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           ":+:")) sumTyConKey.

#[global] Definition prodTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #142.

#[global] Definition prodTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           ":*:")) prodTyConKey.

#[global] Definition compTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #143.

#[global] Definition compTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           ":.:")) compTyConKey.

#[global] Definition rTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #144.

#[global] Definition rTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "R")) rTyConKey.

#[global] Definition dTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #146.

#[global] Definition dTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "D")) dTyConKey.

#[global] Definition cTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #147.

#[global] Definition cTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "C")) cTyConKey.

#[global] Definition sTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #148.

#[global] Definition sTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "S")) sTyConKey.

#[global] Definition rec0TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #149.

#[global] Definition rec0TyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "Rec0")) rec0TyConKey.

#[global] Definition d1TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #151.

#[global] Definition d1TyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "D1")) d1TyConKey.

#[global] Definition c1TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #152.

#[global] Definition c1TyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "C1")) c1TyConKey.

#[global] Definition s1TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #153.

#[global] Definition s1TyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "S1")) s1TyConKey.

#[global] Definition repTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #155.

#[global] Definition repTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "Rep")) repTyConKey.

#[global] Definition rep1TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #156.

#[global] Definition rep1TyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "Rep1")) rep1TyConKey.

#[global] Definition uRecTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #157.

#[global] Definition uRecTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "URec")) uRecTyConKey.

#[global] Definition uAddrTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #158.

#[global] Definition uAddrTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "UAddr")) uAddrTyConKey.

#[global] Definition uCharTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #159.

#[global] Definition uCharTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "UChar")) uCharTyConKey.

#[global] Definition uDoubleTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #160.

#[global] Definition uDoubleTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "UDouble")) uDoubleTyConKey.

#[global] Definition uFloatTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #161.

#[global] Definition uFloatTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "UFloat")) uFloatTyConKey.

#[global] Definition uIntTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #162.

#[global] Definition uIntTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "UInt")) uIntTyConKey.

#[global] Definition uWordTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #163.

#[global] Definition uWordTyConName : Name.Name :=
  tcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "UWord")) uWordTyConKey.

#[global] Definition prefixIDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #54.

#[global] Definition prefixIDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "PrefixI")) prefixIDataConKey.

#[global] Definition infixIDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #55.

#[global] Definition infixIDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "InfixI")) infixIDataConKey.

#[global] Definition sourceUnpackDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #59.

#[global] Definition sourceUnpackDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "SourceUnpack")) sourceUnpackDataConKey.

#[global] Definition sourceNoUnpackDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #60.

#[global] Definition sourceNoUnpackDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "SourceNoUnpack")) sourceNoUnpackDataConKey.

#[global] Definition noSourceUnpackednessDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #61.

#[global] Definition noSourceUnpackednessDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "NoSourceUnpackedness")) noSourceUnpackednessDataConKey.

#[global] Definition sourceLazyDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #62.

#[global] Definition sourceLazyDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "SourceLazy")) sourceLazyDataConKey.

#[global] Definition sourceStrictDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #63.

#[global] Definition sourceStrictDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "SourceStrict")) sourceStrictDataConKey.

#[global] Definition noSourceStrictnessDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #64.

#[global] Definition noSourceStrictnessDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "NoSourceStrictness")) noSourceStrictnessDataConKey.

#[global] Definition decidedLazyDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #65.

#[global] Definition decidedLazyDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "DecidedLazy")) decidedLazyDataConKey.

#[global] Definition decidedStrictDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #66.

#[global] Definition decidedStrictDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "DecidedStrict")) decidedStrictDataConKey.

#[global] Definition decidedUnpackDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #67.

#[global] Definition decidedUnpackDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "DecidedUnpack")) decidedUnpackDataConKey.

#[global] Definition metaDataDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #68.

#[global] Definition metaDataDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "MetaData")) metaDataDataConKey.

#[global] Definition metaConsDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #69.

#[global] Definition metaConsDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "MetaCons")) metaConsDataConKey.

#[global] Definition metaSelDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #70.

#[global] Definition metaSelDataConName : Name.Name :=
  dcQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "MetaSel")) metaSelDataConKey.

#[global] Definition divIntIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #26.

#[global] Definition divIntName : Name.Name :=
  varQual gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "divInt#"))
  divIntIdKey.

#[global] Definition modIntIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #27.

#[global] Definition modIntName : Name.Name :=
  varQual gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "modInt#"))
  modIntIdKey.

#[global] Definition cstringLengthIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #28.

#[global] Definition cstringLengthName : Name.Name :=
  varQual gHC_CSTRING (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "cstringLength#")) cstringLengthIdKey.

#[global] Definition eqStringIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #10.

#[global] Definition eqStringName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "eqString")) eqStringIdKey.

#[global] Definition unpackCStringIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #21.

#[global] Definition unpackCStringName : Name.Name :=
  varQual gHC_CSTRING (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "unpackCString#")) unpackCStringIdKey.

#[global] Definition unpackCStringAppendIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #22.

#[global] Definition unpackCStringAppendName : Name.Name :=
  varQual gHC_CSTRING (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "unpackAppendCString#")) unpackCStringAppendIdKey.

#[global] Definition unpackCStringFoldrIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #23.

#[global] Definition unpackCStringFoldrName : Name.Name :=
  varQual gHC_CSTRING (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "unpackFoldrCString#")) unpackCStringFoldrIdKey.

#[global] Definition unpackCStringUtf8IdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #18.

#[global] Definition unpackCStringUtf8Name : Name.Name :=
  varQual gHC_CSTRING (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "unpackCStringUtf8#")) unpackCStringUtf8IdKey.

#[global] Definition unpackCStringAppendUtf8IdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #19.

#[global] Definition unpackCStringAppendUtf8Name : Name.Name :=
  varQual gHC_CSTRING (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "unpackAppendCStringUtf8#")) unpackCStringAppendUtf8IdKey.

#[global] Definition unpackCStringFoldrUtf8IdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #20.

#[global] Definition unpackCStringFoldrUtf8Name : Name.Name :=
  varQual gHC_CSTRING (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                  "unpackFoldrCStringUtf8#")) unpackCStringFoldrUtf8IdKey.

#[global] Definition inlineIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #120.

#[global] Definition inlineIdName : Name.Name :=
  varQual gHC_MAGIC (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "inline"))
  inlineIdKey.

#[global] Definition clsQual
   : GHC.Unit.Types.Module ->
     GHC.Data.FastString.FastString -> Unique.Unique -> Name.Name :=
  fun modu str unique => mk_known_key_name OccName.clsName modu str unique.

#[global] Definition eqClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #3.

#[global] Definition eqClassName : Name.Name :=
  clsQual gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "Eq"))
  eqClassKey.

#[global] Definition ordClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #12.

#[global] Definition ordClassName : Name.Name :=
  clsQual gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "Ord"))
  ordClassKey.

#[global] Definition functorClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #10.

#[global] Definition functorClassName : Name.Name :=
  clsQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Functor")) functorClassKey.

#[global] Definition monadClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #8.

#[global] Definition monadClassName : Name.Name :=
  clsQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Monad")) monadClassKey.

#[global] Definition thenMClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #172.

#[global] Definition thenMName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        ">>")) thenMClassOpKey.

#[global] Definition monadFailClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #29.

#[global] Definition monadFailClassName : Name.Name :=
  clsQual gHC_INTERNAL_MONAD_FAIL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                              "MonadFail")) monadFailClassKey.

#[global] Definition applicativeClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #34.

#[global] Definition applicativeClassName : Name.Name :=
  clsQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Applicative")) applicativeClassKey.

#[global] Definition thenAClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #753.

#[global] Definition thenAName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "*>")) thenAClassOpKey.

#[global] Definition foldableClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #35.

#[global] Definition foldableClassName : Name.Name :=
  clsQual gHC_INTERNAL_DATA_FOLDABLE (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "Foldable")) foldableClassKey.

#[global] Definition traversableClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #36.

#[global] Definition traversableClassName : Name.Name :=
  clsQual gHC_INTERNAL_DATA_TRAVERSABLE (GHC.Data.FastString.fsLit
                                         (GHC.Base.hs_string__ "Traversable")) traversableClassKey.

#[global] Definition semigroupClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #47.

#[global] Definition semigroupClassName : Name.Name :=
  clsQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Semigroup")) semigroupClassKey.

#[global] Definition sappendClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #554.

#[global] Definition sappendName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "<>")) sappendClassOpKey.

#[global] Definition monoidClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #48.

#[global] Definition monoidClassName : Name.Name :=
  clsQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Monoid")) monoidClassKey.

#[global] Definition mconcatClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #557.

#[global] Definition mconcatName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "mconcat")) mconcatClassOpKey.

#[global] Definition joinMIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #750.

#[global] Definition joinMName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "join")) joinMIdKey.

#[global] Definition alternativeClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #754.

#[global] Definition alternativeClassName : Name.Name :=
  clsQual gHC_INTERNAL_MONAD (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "Alternative")) alternativeClassKey.

#[global] Definition considerAccessibleIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #125.

#[global] Definition considerAccessibleName : Name.Name :=
  varQual gHC_INTERNAL_EXTS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "considerAccessible")) considerAccessibleIdKey.

#[global] Definition dollarIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #123.

#[global] Definition dollarName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "$"))
  dollarIdKey.

#[global] Definition otherwiseIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #43.

#[global] Definition otherwiseIdName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "otherwise")) otherwiseIdKey.

#[global] Definition augmentIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #3.

#[global] Definition augmentName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "augment")) augmentIdKey.

#[global] Definition assertIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #44.

#[global] Definition assertName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "assert")) assertIdKey.

#[global] Definition fromStringClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #186.

#[global] Definition fromStringName : Name.Name :=
  varQual gHC_INTERNAL_DATA_STRING (GHC.Data.FastString.fsLit
                                    (GHC.Base.hs_string__ "fromString")) fromStringClassOpKey.

#[global] Definition numClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #11.

#[global] Definition numClassName : Name.Name :=
  clsQual gHC_INTERNAL_NUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                       "Num")) numClassKey.

#[global] Definition fromIntegerClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #160.

#[global] Definition fromIntegerName : Name.Name :=
  varQual gHC_INTERNAL_NUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                       "fromInteger")) fromIntegerClassOpKey.

#[global] Definition minusClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #161.

#[global] Definition minusName : Name.Name :=
  varQual gHC_INTERNAL_NUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "-"))
  minusClassOpKey.

#[global] Definition negateClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #169.

#[global] Definition negateName : Name.Name :=
  varQual gHC_INTERNAL_NUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                       "negate")) negateClassOpKey.

#[global] Definition bnbVarQual
   : GHC.Base.String -> Unique.Unique -> Name.Name :=
  fun str key =>
    varQual gHC_INTERNAL_NUM_BIGNAT (GHC.Data.FastString.fsLit str) key.

#[global] Definition bnnVarQual
   : GHC.Base.String -> Unique.Unique -> Name.Name :=
  fun str key =>
    varQual gHC_INTERNAL_NUM_NATURAL (GHC.Data.FastString.fsLit str) key.

#[global] Definition bniVarQual
   : GHC.Base.String -> Unique.Unique -> Name.Name :=
  fun str key =>
    varQual gHC_INTERNAL_NUM_INTEGER (GHC.Data.FastString.fsLit str) key.

#[global] Definition bignatEqIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #691.

#[global] Definition bignatEqName : Name.Name :=
  bnbVarQual (GHC.Base.hs_string__ "bigNatEq#") bignatEqIdKey.

#[global] Definition bignatCompareIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #692.

#[global] Definition bignatCompareName : Name.Name :=
  bnbVarQual (GHC.Base.hs_string__ "bigNatCompare") bignatCompareIdKey.

#[global] Definition bignatCompareWordIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #693.

#[global] Definition bignatCompareWordName : Name.Name :=
  bnbVarQual (GHC.Base.hs_string__ "bigNatCompareWord#") bignatCompareWordIdKey.

#[global] Definition naturalToWordIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #650.

#[global] Definition naturalToWordName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalToWord#") naturalToWordIdKey.

#[global] Definition naturalPopCountIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #659.

#[global] Definition naturalPopCountName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalPopCount#") naturalPopCountIdKey.

#[global] Definition naturalShiftRIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #660.

#[global] Definition naturalShiftRName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalShiftR#") naturalShiftRIdKey.

#[global] Definition naturalShiftLIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #661.

#[global] Definition naturalShiftLName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalShiftL#") naturalShiftLIdKey.

#[global] Definition naturalAddIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #662.

#[global] Definition naturalAddName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalAdd") naturalAddIdKey.

#[global] Definition naturalSubIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #663.

#[global] Definition naturalSubName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalSub") naturalSubIdKey.

#[global] Definition naturalSubThrowIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #664.

#[global] Definition naturalSubThrowName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalSubThrow") naturalSubThrowIdKey.

#[global] Definition naturalSubUnsafeIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #665.

#[global] Definition naturalSubUnsafeName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalSubUnsafe") naturalSubUnsafeIdKey.

#[global] Definition naturalMulIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #666.

#[global] Definition naturalMulName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalMul") naturalMulIdKey.

#[global] Definition naturalQuotRemIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #669.

#[global] Definition naturalQuotRemName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalQuotRem#") naturalQuotRemIdKey.

#[global] Definition naturalQuotIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #670.

#[global] Definition naturalQuotName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalQuot") naturalQuotIdKey.

#[global] Definition naturalRemIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #671.

#[global] Definition naturalRemName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalRem") naturalRemIdKey.

#[global] Definition naturalAndIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #672.

#[global] Definition naturalAndName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalAnd") naturalAndIdKey.

#[global] Definition naturalAndNotIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #673.

#[global] Definition naturalAndNotName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalAndNot") naturalAndNotIdKey.

#[global] Definition naturalOrIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #674.

#[global] Definition naturalOrName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalOr") naturalOrIdKey.

#[global] Definition naturalXorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #675.

#[global] Definition naturalXorName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalXor") naturalXorIdKey.

#[global] Definition naturalTestBitIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #676.

#[global] Definition naturalTestBitName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalTestBit#") naturalTestBitIdKey.

#[global] Definition naturalBitIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #677.

#[global] Definition naturalBitName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalBit#") naturalBitIdKey.

#[global] Definition naturalGcdIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #678.

#[global] Definition naturalGcdName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalGcd") naturalGcdIdKey.

#[global] Definition naturalLcmIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #679.

#[global] Definition naturalLcmName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalLcm") naturalLcmIdKey.

#[global] Definition naturalLog2IdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #680.

#[global] Definition naturalLog2Name : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalLog2#") naturalLog2IdKey.

#[global] Definition naturalLogBaseWordIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #681.

#[global] Definition naturalLogBaseWordName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalLogBaseWord#") naturalLogBaseWordIdKey.

#[global] Definition naturalLogBaseIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #682.

#[global] Definition naturalLogBaseName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalLogBase#") naturalLogBaseIdKey.

#[global] Definition naturalPowModIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #683.

#[global] Definition naturalPowModName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalPowMod") naturalPowModIdKey.

#[global] Definition naturalSizeInBaseIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #684.

#[global] Definition naturalSizeInBaseName : Name.Name :=
  bnnVarQual (GHC.Base.hs_string__ "naturalSizeInBase#") naturalSizeInBaseIdKey.

#[global] Definition integerFromNaturalIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #600.

#[global] Definition integerFromNaturalName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerFromNatural") integerFromNaturalIdKey.

#[global] Definition integerToNaturalClampIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #601.

#[global] Definition integerToNaturalClampName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerToNaturalClamp")
  integerToNaturalClampIdKey.

#[global] Definition integerToNaturalThrowIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #602.

#[global] Definition integerToNaturalThrowName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerToNaturalThrow")
  integerToNaturalThrowIdKey.

#[global] Definition integerToNaturalIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #603.

#[global] Definition integerToNaturalName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerToNatural") integerToNaturalIdKey.

#[global] Definition integerToWordIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #604.

#[global] Definition integerToWordName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerToWord#") integerToWordIdKey.

#[global] Definition integerToIntIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #605.

#[global] Definition integerToIntName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerToInt#") integerToIntIdKey.

#[global] Definition integerToWord64IdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #606.

#[global] Definition integerToWord64Name : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerToWord64#") integerToWord64IdKey.

#[global] Definition integerToInt64IdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #607.

#[global] Definition integerToInt64Name : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerToInt64#") integerToInt64IdKey.

#[global] Definition integerFromWordIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #642.

#[global] Definition integerFromWordName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerFromWord#") integerFromWordIdKey.

#[global] Definition integerFromWord64IdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #643.

#[global] Definition integerFromWord64Name : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerFromWord64#") integerFromWord64IdKey.

#[global] Definition integerFromInt64IdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #644.

#[global] Definition integerFromInt64Name : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerFromInt64#") integerFromInt64IdKey.

#[global] Definition integerAddIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #608.

#[global] Definition integerAddName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerAdd") integerAddIdKey.

#[global] Definition integerMulIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #609.

#[global] Definition integerMulName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerMul") integerMulIdKey.

#[global] Definition integerSubIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #610.

#[global] Definition integerSubName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerSub") integerSubIdKey.

#[global] Definition integerNegateIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #611.

#[global] Definition integerNegateName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerNegate") integerNegateIdKey.

#[global] Definition integerAbsIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #618.

#[global] Definition integerAbsName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerAbs") integerAbsIdKey.

#[global] Definition integerPopCountIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #621.

#[global] Definition integerPopCountName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerPopCount#") integerPopCountIdKey.

#[global] Definition integerQuotIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #622.

#[global] Definition integerQuotName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerQuot") integerQuotIdKey.

#[global] Definition integerRemIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #623.

#[global] Definition integerRemName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerRem") integerRemIdKey.

#[global] Definition integerDivIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #624.

#[global] Definition integerDivName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerDiv") integerDivIdKey.

#[global] Definition integerModIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #625.

#[global] Definition integerModName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerMod") integerModIdKey.

#[global] Definition integerDivModIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #626.

#[global] Definition integerDivModName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerDivMod#") integerDivModIdKey.

#[global] Definition integerQuotRemIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #627.

#[global] Definition integerQuotRemName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerQuotRem#") integerQuotRemIdKey.

#[global] Definition integerEncodeFloatIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #630.

#[global] Definition integerEncodeFloatName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerEncodeFloat#") integerEncodeFloatIdKey.

#[global] Definition integerEncodeDoubleIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #631.

#[global] Definition integerEncodeDoubleName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerEncodeDouble#")
  integerEncodeDoubleIdKey.

#[global] Definition integerGcdIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #632.

#[global] Definition integerGcdName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerGcd") integerGcdIdKey.

#[global] Definition integerLcmIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #633.

#[global] Definition integerLcmName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerLcm") integerLcmIdKey.

#[global] Definition integerAndIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #634.

#[global] Definition integerAndName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerAnd") integerAndIdKey.

#[global] Definition integerOrIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #635.

#[global] Definition integerOrName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerOr") integerOrIdKey.

#[global] Definition integerXorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #636.

#[global] Definition integerXorName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerXor") integerXorIdKey.

#[global] Definition integerComplementIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #637.

#[global] Definition integerComplementName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerComplement") integerComplementIdKey.

#[global] Definition integerBitIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #638.

#[global] Definition integerBitName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerBit#") integerBitIdKey.

#[global] Definition integerTestBitIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #639.

#[global] Definition integerTestBitName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerTestBit#") integerTestBitIdKey.

#[global] Definition integerShiftLIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #640.

#[global] Definition integerShiftLName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerShiftL#") integerShiftLIdKey.

#[global] Definition integerShiftRIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #641.

#[global] Definition integerShiftRName : Name.Name :=
  bniVarQual (GHC.Base.hs_string__ "integerShiftR#") integerShiftRIdKey.

#[global] Definition rationalTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #36.

#[global] Definition rationalTyConName : Name.Name :=
  tcQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                       "Rational")) rationalTyConKey.

#[global] Definition ratioTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #35.

#[global] Definition ratioTyConName : Name.Name :=
  tcQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                       "Ratio")) ratioTyConKey.

#[global] Definition ratioDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #11.

#[global] Definition ratioDataConName : Name.Name :=
  dcQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ ":%"))
  ratioDataConKey.

#[global] Definition realClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #14.

#[global] Definition realClassName : Name.Name :=
  clsQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Real")) realClassKey.

#[global] Definition integralClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #7.

#[global] Definition integralClassName : Name.Name :=
  clsQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Integral")) integralClassKey.

#[global] Definition realFracClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #16.

#[global] Definition realFracClassName : Name.Name :=
  clsQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "RealFrac")) realFracClassKey.

#[global] Definition fractionalClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #6.

#[global] Definition fractionalClassName : Name.Name :=
  clsQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Fractional")) fractionalClassKey.

#[global] Definition fromRationalClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #162.

#[global] Definition fromRationalName : Name.Name :=
  varQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "fromRational")) fromRationalClassOpKey.

#[global] Definition toIntegerClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #192.

#[global] Definition toIntegerName : Name.Name :=
  varQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "toInteger")) toIntegerClassOpKey.

#[global] Definition toRationalClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #193.

#[global] Definition toRationalName : Name.Name :=
  varQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "toRational")) toRationalClassOpKey.

#[global] Definition fromIntegralIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #190.

#[global] Definition fromIntegralName : Name.Name :=
  varQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "fromIntegral")) fromIntegralIdKey.

#[global] Definition realToFracIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #191.

#[global] Definition realToFracName : Name.Name :=
  varQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "realToFrac")) realToFracIdKey.

#[global] Definition mkRationalBase2IdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #700.

#[global] Definition mkRationalBase2Name : Name.Name :=
  varQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "mkRationalBase2")) mkRationalBase2IdKey.

#[global] Definition mkRationalBase10IdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #701 : Unique.Unique.

#[global] Definition mkRationalBase10Name : Name.Name :=
  varQual gHC_INTERNAL_REAL (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "mkRationalBase10")) mkRationalBase10IdKey.

#[global] Definition floatingClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #5.

#[global] Definition floatingClassName : Name.Name :=
  clsQual gHC_INTERNAL_FLOAT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "Floating")) floatingClassKey.

#[global] Definition realFloatClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #15.

#[global] Definition realFloatClassName : Name.Name :=
  clsQual gHC_INTERNAL_FLOAT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "RealFloat")) realFloatClassKey.

#[global] Definition integerToFloatIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #128.

#[global] Definition integerToFloatName : Name.Name :=
  varQual gHC_INTERNAL_FLOAT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "integerToFloat#")) integerToFloatIdKey.

#[global] Definition integerToDoubleIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #129.

#[global] Definition integerToDoubleName : Name.Name :=
  varQual gHC_INTERNAL_FLOAT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "integerToDouble#")) integerToDoubleIdKey.

#[global] Definition naturalToFloatIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #130.

#[global] Definition naturalToFloatName : Name.Name :=
  varQual gHC_INTERNAL_FLOAT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "naturalToFloat#")) naturalToFloatIdKey.

#[global] Definition naturalToDoubleIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #131.

#[global] Definition naturalToDoubleName : Name.Name :=
  varQual gHC_INTERNAL_FLOAT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "naturalToDouble#")) naturalToDoubleIdKey.

#[global] Definition rationalToFloatIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #132.

#[global] Definition rationalToFloatName : Name.Name :=
  varQual gHC_INTERNAL_FLOAT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "rationalToFloat")) rationalToFloatIdKey.

#[global] Definition rationalToDoubleIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #133.

#[global] Definition rationalToDoubleName : Name.Name :=
  varQual gHC_INTERNAL_FLOAT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "rationalToDouble")) rationalToDoubleIdKey.

#[global] Definition ixClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #18.

#[global] Definition ixClassName : Name.Name :=
  clsQual gHC_INTERNAL_IX (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "Ix"))
  ixClassKey.

#[global] Definition trModuleTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #105.

#[global] Definition trModuleTyConName : Name.Name :=
  tcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "Module"))
  trModuleTyConKey.

#[global] Definition trModuleDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #43.

#[global] Definition trModuleDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "Module"))
  trModuleDataConKey.

#[global] Definition trNameTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #106.

#[global] Definition trNameTyConName : Name.Name :=
  tcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "TrName"))
  trNameTyConKey.

#[global] Definition trNameSDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #45.

#[global] Definition trNameSDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "TrNameS"))
  trNameSDataConKey.

#[global] Definition trNameDDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #46.

#[global] Definition trNameDDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "TrNameD"))
  trNameDDataConKey.

#[global] Definition trTyConTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #104.

#[global] Definition trTyConTyConName : Name.Name :=
  tcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "TyCon"))
  trTyConTyConKey.

#[global] Definition trTyConDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #41.

#[global] Definition trTyConDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "TyCon"))
  trTyConDataConKey.

#[global] Definition kindRepTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #107.

#[global] Definition kindRepTyConName : Name.Name :=
  tcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "KindRep"))
  kindRepTyConKey.

#[global] Definition kindRepTyConAppDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #106.

#[global] Definition kindRepTyConAppDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                               "KindRepTyConApp")) kindRepTyConAppDataConKey.

#[global] Definition kindRepVarDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #107.

#[global] Definition kindRepVarDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "KindRepVar"))
  kindRepVarDataConKey.

#[global] Definition kindRepAppDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #108.

#[global] Definition kindRepAppDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "KindRepApp"))
  kindRepAppDataConKey.

#[global] Definition kindRepFunDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #109.

#[global] Definition kindRepFunDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "KindRepFun"))
  kindRepFunDataConKey.

#[global] Definition kindRepTYPEDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #110.

#[global] Definition kindRepTYPEDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                               "KindRepTYPE")) kindRepTYPEDataConKey.

#[global] Definition kindRepTypeLitSDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #111.

#[global] Definition kindRepTypeLitSDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                               "KindRepTypeLitS")) kindRepTypeLitSDataConKey.

#[global] Definition kindRepTypeLitDDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #112.

#[global] Definition kindRepTypeLitDDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                               "KindRepTypeLitD")) kindRepTypeLitDDataConKey.

#[global] Definition typeLitSortTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #108.

#[global] Definition typeLitSortTyConName : Name.Name :=
  tcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                               "TypeLitSort")) typeLitSortTyConKey.

#[global] Definition typeLitSymbolDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #113.

#[global] Definition typeLitSymbolDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                               "TypeLitSymbol")) typeLitSymbolDataConKey.

#[global] Definition typeLitNatDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #114.

#[global] Definition typeLitNatDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "TypeLitNat"))
  typeLitNatDataConKey.

#[global] Definition typeLitCharDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #115.

#[global] Definition typeLitCharDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                               "TypeLitChar")) typeLitCharDataConKey.

#[global] Definition typeableClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #20.

#[global] Definition typeableClassName : Name.Name :=
  clsQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "Typeable")) typeableClassKey.

#[global] Definition typeRepTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #192.

#[global] Definition typeRepTyConName : Name.Name :=
  tcQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                         (GHC.Base.hs_string__ "TypeRep")) typeRepTyConKey.

#[global] Definition someTypeRepTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #193.

#[global] Definition someTypeRepTyConName : Name.Name :=
  tcQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                         (GHC.Base.hs_string__ "SomeTypeRep")) someTypeRepTyConKey.

#[global] Definition someTypeRepDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #194.

#[global] Definition someTypeRepDataConName : Name.Name :=
  dcQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                         (GHC.Base.hs_string__ "SomeTypeRep")) someTypeRepDataConKey.

#[global] Definition typeRepIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #510.

#[global] Definition typeRepIdName : Name.Name :=
  varQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "typeRep#")) typeRepIdKey.

#[global] Definition mkTrTypeKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #504.

#[global] Definition mkTrTypeName : Name.Name :=
  varQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "mkTrType")) mkTrTypeKey.

#[global] Definition mkTrConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #505.

#[global] Definition mkTrConName : Name.Name :=
  varQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "mkTrCon")) mkTrConKey.

#[global] Definition mkTrAppCheckedKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #506.

#[global] Definition mkTrAppCheckedName : Name.Name :=
  varQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "mkTrAppChecked")) mkTrAppCheckedKey.

#[global] Definition mkTrFunKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #511.

#[global] Definition mkTrFunName : Name.Name :=
  varQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "mkTrFun")) mkTrFunKey.

#[global] Definition typeNatTypeRepKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #507.

#[global] Definition typeNatTypeRepName : Name.Name :=
  varQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "typeNatTypeRep")) typeNatTypeRepKey.

#[global] Definition typeSymbolTypeRepKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #508.

#[global] Definition typeSymbolTypeRepName : Name.Name :=
  varQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "typeSymbolTypeRep")) typeSymbolTypeRepKey.

#[global] Definition typeCharTypeRepKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #509.

#[global] Definition typeCharTypeRepName : Name.Name :=
  varQual gHC_INTERNAL_TYPEABLE_INTERNAL (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "typeCharTypeRep")) typeCharTypeRepKey.

#[global] Definition trGhcPrimModuleKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #47.

#[global] Definition trGhcPrimModuleName : Name.Name :=
  varQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                "tr$ModuleGHCPrim")) trGhcPrimModuleKey.

#[global] Definition starKindRepKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #520.

#[global] Definition starKindRepName : Name.Name :=
  varQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "krep$*"))
  starKindRepKey.

#[global] Definition starArrStarKindRepKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #521.

#[global] Definition starArrStarKindRepName : Name.Name :=
  varQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                "krep$*Arr*")) starArrStarKindRepKey.

#[global] Definition starArrStarArrStarKindRepKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #522.

#[global] Definition starArrStarArrStarKindRepName : Name.Name :=
  varQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                "krep$*->*->*")) starArrStarArrStarKindRepKey.

#[global] Definition constraintKindRepKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #523.

#[global] Definition constraintKindRepName : Name.Name :=
  varQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                "krep$Constraint")) constraintKindRepKey.

#[global] Definition withDictClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #21.

#[global] Definition withDictClassName : Name.Name :=
  clsQual gHC_MAGIC_DICT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                     "WithDict")) withDictClassKey.

#[global] Definition nonEmptyTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #86.

#[global] Definition nonEmptyTyConName : Name.Name :=
  tcQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                       "NonEmpty")) nonEmptyTyConKey.

#[global] Definition dataToTagClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #23.

#[global] Definition dataToTagClassName : Name.Name :=
  clsQual gHC_MAGIC (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "DataToTag"))
  dataToTagClassKey.

#[global] Definition errorMessageTypeErrorFamKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #181.

#[global] Definition errorMessageTypeErrorFamName : Name.Name :=
  tcQual gHC_INTERNAL_TYPEERROR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "TypeError")) errorMessageTypeErrorFamKey.

#[global] Definition typeErrorTextDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #50.

#[global] Definition typeErrorTextDataConName : Name.Name :=
  dcQual gHC_INTERNAL_TYPEERROR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "Text")) typeErrorTextDataConKey.

#[global] Definition typeErrorAppendDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #51.

#[global] Definition typeErrorAppendDataConName : Name.Name :=
  dcQual gHC_INTERNAL_TYPEERROR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            ":<>:")) typeErrorAppendDataConKey.

#[global] Definition typeErrorVAppendDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #52.

#[global] Definition typeErrorVAppendDataConName : Name.Name :=
  dcQual gHC_INTERNAL_TYPEERROR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            ":$$:")) typeErrorVAppendDataConKey.

#[global] Definition typeErrorShowTypeDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #53.

#[global] Definition typeErrorShowTypeDataConName : Name.Name :=
  dcQual gHC_INTERNAL_TYPEERROR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "ShowType")) typeErrorShowTypeDataConKey.

#[global] Definition unsatisfiableClassNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #170.

#[global] Definition unsatisfiableClassName : Name.Name :=
  clsQual gHC_INTERNAL_TYPEERROR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                             "Unsatisfiable")) unsatisfiableClassNameKey.

#[global] Definition unsatisfiableIdNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #580.

#[global] Definition unsatisfiableIdName : Name.Name :=
  varQual gHC_INTERNAL_TYPEERROR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                             "unsatisfiable")) unsatisfiableIdNameKey.

#[global] Definition unsafeEqualityProofIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #570.

#[global] Definition unsafeEqualityProofName : Name.Name :=
  varQual gHC_INTERNAL_UNSAFE_COERCE (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "unsafeEqualityProof")) unsafeEqualityProofIdKey.

#[global] Definition unsafeEqualityTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #196.

#[global] Definition unsafeEqualityTyConName : Name.Name :=
  tcQual gHC_INTERNAL_UNSAFE_COERCE (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "UnsafeEquality")) unsafeEqualityTyConKey.

#[global] Definition unsafeReflDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #116.

#[global] Definition unsafeReflDataConName : Name.Name :=
  dcQual gHC_INTERNAL_UNSAFE_COERCE (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "UnsafeRefl")) unsafeReflDataConKey.

#[global] Definition unsafeCoercePrimIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #571.

#[global] Definition unsafeCoercePrimName : Name.Name :=
  varQual gHC_INTERNAL_UNSAFE_COERCE (GHC.Data.FastString.fsLit
                                      (GHC.Base.hs_string__ "unsafeCoerce#")) unsafeCoercePrimIdKey.

#[global] Definition toDynIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #530.

#[global] Definition toDynName : Name.Name :=
  varQual gHC_INTERNAL_DYNAMIC (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "toDyn")) toDynIdKey.

#[global] Definition dataClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #9.

#[global] Definition dataClassName : Name.Name :=
  clsQual gHC_INTERNAL_DATA_DATA (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                             "Data")) dataClassKey.

#[global] Definition assertErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #105.

#[global] Definition assertErrorName : Name.Name :=
  varQual gHC_INTERNAL_IO_Exception (GHC.Data.FastString.fsLit
                                     (GHC.Base.hs_string__ "assertError")) assertErrorIdKey.

#[global] Definition traceKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #108.

#[global] Definition traceName : Name.Name :=
  varQual gHC_INTERNAL_DEBUG_TRACE (GHC.Data.FastString.fsLit
                                    (GHC.Base.hs_string__ "trace")) traceKey.

#[global] Definition enumClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #2.

#[global] Definition enumClassName : Name.Name :=
  clsQual gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Enum")) enumClassKey.

#[global] Definition boundedClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #1.

#[global] Definition boundedClassName : Name.Name :=
  clsQual gHC_INTERNAL_ENUM (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Bounded")) boundedClassKey.

#[global] Definition concatIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #31.

#[global] Definition concatName : Name.Name :=
  varQual gHC_INTERNAL_LIST (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "concat")) concatIdKey.

#[global] Definition filterIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #32.

#[global] Definition filterName : Name.Name :=
  varQual gHC_INTERNAL_LIST (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "filter")) filterIdKey.

#[global] Definition zipIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #33.

#[global] Definition zipName : Name.Name :=
  varQual gHC_INTERNAL_LIST (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "zip")) zipIdKey.

#[global] Definition isListClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #198.

#[global] Definition isListClassName : Name.Name :=
  clsQual gHC_INTERNAL_IS_LIST (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "IsList")) isListClassKey.

#[global] Definition fromListClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #199.

#[global] Definition fromListName : Name.Name :=
  varQual gHC_INTERNAL_IS_LIST (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "fromList")) fromListClassOpKey.

#[global] Definition fromListNClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #500.

#[global] Definition fromListNName : Name.Name :=
  varQual gHC_INTERNAL_IS_LIST (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "fromListN")) fromListNClassOpKey.

#[global] Definition toListClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #501.

#[global] Definition toListName : Name.Name :=
  varQual gHC_INTERNAL_IS_LIST (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "toList")) toListClassOpKey.

#[global] Definition getFieldClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #572.

#[global] Definition getFieldName : Name.Name :=
  varQual gHC_INTERNAL_RECORDS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "getField")) getFieldClassOpKey.

#[global] Definition setFieldClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #573.

#[global] Definition setFieldName : Name.Name :=
  varQual gHC_INTERNAL_RECORDS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "setField")) setFieldClassOpKey.

#[global] Definition showClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #17.

#[global] Definition showClassName : Name.Name :=
  clsQual gHC_INTERNAL_SHOW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Show")) showClassKey.

#[global] Definition readClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #13.

#[global] Definition readClassName : Name.Name :=
  clsQual gHC_INTERNAL_READ (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "Read")) readClassKey.

#[global] Definition genClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #37.

#[global] Definition genClassName : Name.Name :=
  clsQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "Generic")) genClassKey.

#[global] Definition gen1ClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #38.

#[global] Definition gen1ClassName : Name.Name :=
  clsQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "Generic1")) gen1ClassKey.

#[global] Definition datatypeClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #39.

#[global] Definition datatypeClassName : Name.Name :=
  clsQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "Datatype")) datatypeClassKey.

#[global] Definition constructorClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #40.

#[global] Definition constructorClassName : Name.Name :=
  clsQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "Constructor")) constructorClassKey.

#[global] Definition selectorClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #41.

#[global] Definition selectorClassName : Name.Name :=
  clsQual gHC_INTERNAL_GENERICS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "Selector")) selectorClassKey.

#[global] Definition genericClassNames : list Name.Name :=
  cons genClassName (cons gen1ClassName nil).

#[global] Definition ghciIoClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #45.

#[global] Definition ghciIoClassName : Name.Name :=
  clsQual gHC_INTERNAL_GHCI (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "GHCiSandboxIO")) ghciIoClassKey.

#[global] Definition ghciStepIoMClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #197.

#[global] Definition ghciStepIoMName : Name.Name :=
  varQual gHC_INTERNAL_GHCI (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "ghciStepIO")) ghciStepIoMClassOpKey.

#[global] Definition ioTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #57.

#[global] Definition ioTyConName : Name.Name :=
  tcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "IO"))
  ioTyConKey.

#[global] Definition ioDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #16.

#[global] Definition ioDataConName : Name.Name :=
  dcQual gHC_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "IO"))
  ioDataConKey.

#[global] Definition thenIOIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #103.

#[global] Definition thenIOName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "thenIO")) thenIOIdKey.

#[global] Definition bindIOIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #34.

#[global] Definition bindIOName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "bindIO")) bindIOIdKey.

#[global] Definition returnIOIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #35.

#[global] Definition returnIOName : Name.Name :=
  varQual gHC_INTERNAL_BASE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "returnIO")) returnIOIdKey.

#[global] Definition failIOIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #38.

#[global] Definition failIOName : Name.Name :=
  varQual gHC_INTERNAL_IO (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                      "failIO")) failIOIdKey.

#[global] Definition printIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #37.

#[global] Definition printName : Name.Name :=
  varQual gHC_INTERNAL_SYSTEM_IO (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                             "print")) printIdKey.

#[global] Definition int8TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #17.

#[global] Definition int8TyConName : Name.Name :=
  tcQual gHC_INTERNAL_INT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                      "Int8")) int8TyConKey.

#[global] Definition int16TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #19.

#[global] Definition int16TyConName : Name.Name :=
  tcQual gHC_INTERNAL_INT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                      "Int16")) int16TyConKey.

#[global] Definition int32TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #21.

#[global] Definition int32TyConName : Name.Name :=
  tcQual gHC_INTERNAL_INT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                      "Int32")) int32TyConKey.

#[global] Definition int64TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #23.

#[global] Definition int64TyConName : Name.Name :=
  tcQual gHC_INTERNAL_INT (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                      "Int64")) int64TyConKey.

#[global] Definition word8TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #62.

#[global] Definition word8TyConName : Name.Name :=
  tcQual gHC_INTERNAL_WORD (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                       "Word8")) word8TyConKey.

#[global] Definition word16TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #64.

#[global] Definition word16TyConName : Name.Name :=
  tcQual gHC_INTERNAL_WORD (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                       "Word16")) word16TyConKey.

#[global] Definition word32TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #66.

#[global] Definition word32TyConName : Name.Name :=
  tcQual gHC_INTERNAL_WORD (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                       "Word32")) word32TyConKey.

#[global] Definition word64TyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #68.

#[global] Definition word64TyConName : Name.Name :=
  tcQual gHC_INTERNAL_WORD (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                       "Word64")) word64TyConKey.

#[global] Definition ptrTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #77.

#[global] Definition ptrTyConName : Name.Name :=
  tcQual gHC_INTERNAL_PTR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "Ptr"))
  ptrTyConKey.

#[global] Definition funPtrTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #78.

#[global] Definition funPtrTyConName : Name.Name :=
  tcQual gHC_INTERNAL_PTR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                      "FunPtr")) funPtrTyConKey.

#[global] Definition stablePtrTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #39.

#[global] Definition stablePtrTyConName : Name.Name :=
  tcQual gHC_INTERNAL_STABLE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "StablePtr")) stablePtrTyConKey.

#[global] Definition newStablePtrIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #36.

#[global] Definition newStablePtrName : Name.Name :=
  varQual gHC_INTERNAL_STABLE (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                          "newStablePtr")) newStablePtrIdKey.

#[global] Definition monadFixClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #28.

#[global] Definition monadFixClassName : Name.Name :=
  clsQual gHC_INTERNAL_MONAD_FIX (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                             "MonadFix")) monadFixClassKey.

#[global] Definition mfixIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #175.

#[global] Definition mfixName : Name.Name :=
  varQual gHC_INTERNAL_MONAD_FIX (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                             "mfix")) mfixIdKey.

#[global] Definition arrAIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #180.

#[global] Definition arrAName : Name.Name :=
  varQual gHC_INTERNAL_ARROW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "arr")) arrAIdKey.

#[global] Definition composeAIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #181.

#[global] Definition composeAName : Name.Name :=
  varQual gHC_INTERNAL_DESUGAR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           ">>>")) composeAIdKey.

#[global] Definition firstAIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #182.

#[global] Definition firstAName : Name.Name :=
  varQual gHC_INTERNAL_ARROW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "first")) firstAIdKey.

#[global] Definition appAIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #183.

#[global] Definition appAName : Name.Name :=
  varQual gHC_INTERNAL_ARROW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "app")) appAIdKey.

#[global] Definition choiceAIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #184.

#[global] Definition choiceAName : Name.Name :=
  varQual gHC_INTERNAL_ARROW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "|||")) choiceAIdKey.

#[global] Definition loopAIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #185.

#[global] Definition loopAName : Name.Name :=
  varQual gHC_INTERNAL_ARROW (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "loop")) loopAIdKey.

#[global] Definition guardMIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #194.

#[global] Definition guardMName : Name.Name :=
  varQual gHC_INTERNAL_MONAD (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "guard")) guardMIdKey.

#[global] Definition liftMIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #195.

#[global] Definition liftMName : Name.Name :=
  varQual gHC_INTERNAL_MONAD (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "liftM")) liftMIdKey.

#[global] Definition mzipIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #196.

#[global] Definition mzipName : Name.Name :=
  varQual cONTROL_MONAD_ZIP (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                        "mzip")) mzipIdKey.

#[global] Definition toAnnotationWrapperIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #187.

#[global] Definition toAnnotationWrapperName : Name.Name :=
  varQual gHC_INTERNAL_DESUGAR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "toAnnotationWrapper")) toAnnotationWrapperIdKey.

#[global] Definition monadPlusClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #30.

#[global] Definition monadPlusClassName : Name.Name :=
  clsQual gHC_INTERNAL_MONAD (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                         "MonadPlus")) monadPlusClassKey.

#[global] Definition isStringClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #33.

#[global] Definition isStringClassName : Name.Name :=
  clsQual gHC_INTERNAL_DATA_STRING (GHC.Data.FastString.fsLit
                                    (GHC.Base.hs_string__ "IsString")) isStringClassKey.

#[global] Definition knownNatClassNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #42.

#[global] Definition knownNatClassName : Name.Name :=
  clsQual gHC_INTERNAL_TYPENATS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "KnownNat")) knownNatClassNameKey.

#[global] Definition knownSymbolClassNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #43.

#[global] Definition knownSymbolClassName : Name.Name :=
  clsQual gHC_INTERNAL_TYPELITS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "KnownSymbol")) knownSymbolClassNameKey.

#[global] Definition knownCharClassNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #44.

#[global] Definition knownCharClassName : Name.Name :=
  clsQual gHC_INTERNAL_TYPELITS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "KnownChar")) knownCharClassNameKey.

#[global] Definition fromLabelClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #177.

#[global] Definition fromLabelClassOpName : Name.Name :=
  varQual gHC_INTERNAL_OVER_LABELS (GHC.Data.FastString.fsLit
                                    (GHC.Base.hs_string__ "fromLabel")) fromLabelClassOpKey.

#[global] Definition ipClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #49.

#[global] Definition ipClassName : Name.Name :=
  clsQual gHC_CLASSES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "IP"))
  ipClassKey.

#[global] Definition hasFieldClassNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #50.

#[global] Definition hasFieldClassName : Name.Name :=
  clsQual gHC_INTERNAL_RECORDS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                           "HasField")) hasFieldClassNameKey.

#[global] Definition exceptionContextTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #420.

#[global] Definition exceptionContextTyConName : Name.Name :=
  tcQual gHC_INTERNAL_EXCEPTION_CONTEXT (GHC.Data.FastString.fsLit
                                         (GHC.Base.hs_string__ "ExceptionContext")) exceptionContextTyConKey.

#[global] Definition emptyExceptionContextKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #562.

#[global] Definition emptyExceptionContextName : Name.Name :=
  varQual gHC_INTERNAL_EXCEPTION_CONTEXT (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "emptyExceptionContext")) emptyExceptionContextKey.

#[global] Definition callStackTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #191.

#[global] Definition callStackTyConName : Name.Name :=
  tcQual gHC_INTERNAL_STACK_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                              "CallStack")) callStackTyConKey.

#[global] Definition emptyCallStackKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #558.

#[global] Definition emptyCallStackName : Name.Name :=
  varQual gHC_INTERNAL_STACK_TYPES (GHC.Data.FastString.fsLit
                                    (GHC.Base.hs_string__ "emptyCallStack")) emptyCallStackKey.

#[global] Definition pushCallStackKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #559.

#[global] Definition pushCallStackName : Name.Name :=
  varQual gHC_INTERNAL_STACK_TYPES (GHC.Data.FastString.fsLit
                                    (GHC.Base.hs_string__ "pushCallStack")) pushCallStackKey.

#[global] Definition srcLocDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #37.

#[global] Definition srcLocDataConName : Name.Name :=
  dcQual gHC_INTERNAL_STACK_TYPES (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                              "SrcLoc")) srcLocDataConKey.

#[global] Definition pLUGINS : GHC.Unit.Types.Module :=
  mkThisGhcModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                              "GHC.Driver.Plugins")).

#[global] Definition pluginTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #102.

#[global] Definition pluginTyConName : Name.Name :=
  tcQual pLUGINS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__ "Plugin"))
  pluginTyConKey.

#[global] Definition frontendPluginTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #103.

#[global] Definition frontendPluginTyConName : Name.Name :=
  tcQual pLUGINS (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                             "FrontendPlugin")) frontendPluginTyConKey.

#[global] Definition makeStaticKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #561.

#[global] Definition makeStaticName : Name.Name :=
  varQual gHC_INTERNAL_STATICPTR_INTERNAL (GHC.Data.FastString.fsLit
                                           (GHC.Base.hs_string__ "makeStatic")) makeStaticKey.

#[global] Definition staticPtrInfoTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #190.

#[global] Definition staticPtrInfoTyConName : Name.Name :=
  tcQual gHC_INTERNAL_STATICPTR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "StaticPtrInfo")) staticPtrInfoTyConKey.

#[global] Definition staticPtrInfoDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #34.

#[global] Definition staticPtrInfoDataConName : Name.Name :=
  dcQual gHC_INTERNAL_STATICPTR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "StaticPtrInfo")) staticPtrInfoDataConKey.

#[global] Definition staticPtrTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #189.

#[global] Definition staticPtrTyConName : Name.Name :=
  tcQual gHC_INTERNAL_STATICPTR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "StaticPtr")) staticPtrTyConKey.

#[global] Definition staticPtrDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #33.

#[global] Definition staticPtrDataConName : Name.Name :=
  dcQual gHC_INTERNAL_STATICPTR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                            "StaticPtr")) staticPtrDataConKey.

#[global] Definition fromStaticPtrClassOpKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #560.

#[global] Definition fromStaticPtrName : Name.Name :=
  varQual gHC_INTERNAL_STATICPTR (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                             "fromStaticPtr")) fromStaticPtrClassOpKey.

#[global] Definition fingerprintDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #35.

#[global] Definition fingerprintDataConName : Name.Name :=
  dcQual gHC_INTERNAL_FINGERPRINT_TYPE (GHC.Data.FastString.fsLit
                                        (GHC.Base.hs_string__ "Fingerprint")) fingerprintDataConKey.

#[global] Definition constPtrTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #417.

#[global] Definition constPtrConName : Name.Name :=
  tcQual gHC_INTERNAL_FOREIGN_C_CONSTPTR (GHC.Data.FastString.fsLit
                                          (GHC.Base.hs_string__ "ConstPtr")) constPtrTyConKey.

#[global] Definition jsvalTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #418.

#[global] Definition jsvalTyConName : Name.Name :=
  tcQual (mkGhcInternalModule (GHC.Data.FastString.fsLit (GHC.Base.hs_string__
                                                          "GHC.Internal.Wasm.Prim.Types"))) (GHC.Data.FastString.fsLit
                                                                                             (GHC.Base.hs_string__
                                                                                              "JSVal")) jsvalTyConKey.

#[global] Definition randomClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #31.

#[global] Definition randomGenClassKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeClassUnique #32.

#[global] Definition addrPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #1.

#[global] Definition arrayPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #3.

#[global] Definition boolTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #4.

#[global] Definition byteArrayPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #5.

#[global] Definition stringTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #6.

#[global] Definition charPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #7.

#[global] Definition charTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #8.

#[global] Definition doublePrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #9.

#[global] Definition doubleTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #10.

#[global] Definition floatPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #11.

#[global] Definition floatTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #12.

#[global] Definition fUNTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #13.

#[global] Definition intPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #14.

#[global] Definition intTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #15.

#[global] Definition int8PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #16.

#[global] Definition int16PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #18.

#[global] Definition int32PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #20.

#[global] Definition int64PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #22.

#[global] Definition integerTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #24.

#[global] Definition naturalTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #25.

#[global] Definition listTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #26.

#[global] Definition foreignObjPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #27.

#[global] Definition maybeTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #28.

#[global] Definition weakPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #29.

#[global] Definition mutableArrayPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #30.

#[global] Definition mutableByteArrayPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #31.

#[global] Definition mVarPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #33.

#[global] Definition ioPortPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #34.

#[global] Definition realWorldTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #37.

#[global] Definition stablePtrPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #38.

#[global] Definition eqTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #40.

#[global] Definition heqTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #41.

#[global] Definition ctArrowTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #42.

#[global] Definition ccArrowTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #43.

#[global] Definition tcArrowTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #44.

#[global] Definition statePrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #50.

#[global] Definition stableNamePrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #51.

#[global] Definition stableNameTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #52.

#[global] Definition eqPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #53.

#[global] Definition eqReprPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #54.

#[global] Definition eqPhantPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #55.

#[global] Definition mutVarPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #56.

#[global] Definition wordPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #59.

#[global] Definition wordTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #60.

#[global] Definition word8PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #61.

#[global] Definition word16PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #63.

#[global] Definition word32PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #65.

#[global] Definition word64PrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #67.

#[global] Definition kindConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #72.

#[global] Definition boxityConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #73.

#[global] Definition typeConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #74.

#[global] Definition threadIdPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #75.

#[global] Definition bcoPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #76.

#[global] Definition tVarPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #79.

#[global] Definition compactPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #80.

#[global] Definition stackSnapshotPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #81.

#[global] Definition promptTagPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #82.

#[global] Definition dictTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #87.

#[global] Definition liftedTypeKindTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #88.

#[global] Definition unliftedTypeKindTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #89.

#[global] Definition tYPETyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #91.

#[global] Definition cONSTRAINTTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #92.

#[global] Definition constraintKindTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #93.

#[global] Definition levityTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #94.

#[global] Definition runtimeRepTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #95.

#[global] Definition vecCountTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #96.

#[global] Definition vecElemTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #97.

#[global] Definition liftedRepTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #98.

#[global] Definition unliftedRepTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #99.

#[global] Definition zeroBitRepTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #100.

#[global] Definition zeroBitTypeTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #101.

#[global] Definition anyTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #171.

#[global] Definition zonkAnyTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #172.

#[global] Definition coercibleTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #183.

#[global] Definition proxyPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #184.

#[global] Definition smallArrayPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #187.

#[global] Definition smallMutableArrayPrimTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #188.

#[global] Definition typeSymbolAppendFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #195.

#[global] Definition multiplicityTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #197.

#[global] Definition unrestrictedFunTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #198.

#[global] Definition multMulTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #199.

#[global] Definition typeSymbolKindConNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #400.

#[global] Definition typeCharKindConNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #401.

#[global] Definition typeNatAddTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #402.

#[global] Definition typeNatMulTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #403.

#[global] Definition typeNatExpTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #404.

#[global] Definition typeNatSubTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #405.

#[global] Definition typeSymbolCmpTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #406.

#[global] Definition typeNatCmpTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #407.

#[global] Definition typeCharCmpTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #408.

#[global] Definition typeLeqCharTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #409.

#[global] Definition typeNatDivTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #410.

#[global] Definition typeNatModTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #411.

#[global] Definition typeNatLogTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #412.

#[global] Definition typeConsSymbolTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #413.

#[global] Definition typeUnconsSymbolTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #414.

#[global] Definition typeCharToNatTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #415.

#[global] Definition typeNatToCharTyFamNameKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeTyConUnique #416.

#[global] Definition charDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #1.

#[global] Definition consDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #2.

#[global] Definition doubleDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #3.

#[global] Definition falseDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #4.

#[global] Definition floatDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #5.

#[global] Definition intDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #6.

#[global] Definition nothingDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #7.

#[global] Definition justDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #8.

#[global] Definition eqDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #9.

#[global] Definition nilDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #10.

#[global] Definition word8DataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #12.

#[global] Definition stableNameDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #13.

#[global] Definition trueDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #14.

#[global] Definition wordDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #15.

#[global] Definition heqDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #18.

#[global] Definition crossDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #20.

#[global] Definition inlDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #21.

#[global] Definition inrDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #22.

#[global] Definition genUnitDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #23.

#[global] Definition mkDictDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #30.

#[global] Definition coercibleDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #32.

#[global] Definition vecRepDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #71.

#[global] Definition tupleRepDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #72.

#[global] Definition sumRepDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #73.

#[global] Definition boxedRepDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #74.

#[global] Definition boxedRepDataConTyConKey : Unique.Unique :=
  boxedRepDataConKey.

#[global] Definition tupleRepDataConTyConKey : Unique.Unique :=
  tupleRepDataConKey.

(* Skipping definition `PrelNames.runtimeRepSimpleDataConKeys' *)

#[global] Definition liftedDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #88.

#[global] Definition unliftedDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #89.

#[global] Definition vecCountDataConKeys : list Unique.Unique :=
  GHC.Base.map GHC.Builtin.Uniques.mkPreludeDataConUnique (GHC.Enum.enumFromTo #90
                                                                               #95).

#[global] Definition vecElemDataConKeys : list Unique.Unique :=
  GHC.Base.map GHC.Builtin.Uniques.mkPreludeDataConUnique (GHC.Enum.enumFromTo #96
                                                                               #105).

#[global] Definition oneDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #117.

#[global] Definition manyDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #118.

#[global] Definition integerISDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #120.

#[global] Definition integerINDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #121.

#[global] Definition integerIPDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #122.

#[global] Definition naturalNSDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #123.

#[global] Definition naturalNBDataConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeDataConUnique #124.

#[global] Definition absentErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #1.

#[global] Definition absentConstraintErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #2.

#[global] Definition recSelErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #7.

#[global] Definition seqIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #8.

#[global] Definition absentSumFieldErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #9.

#[global] Definition noMethodBindingErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #11.

#[global] Definition nonExhaustiveGuardsErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #12.

#[global] Definition impossibleErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #13.

#[global] Definition impossibleConstraintErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #14.

#[global] Definition patErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #15.

#[global] Definition realWorldPrimIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #16.

#[global] Definition recConErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #17.

#[global] Definition voidPrimIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #24.

#[global] Definition typeErrorIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #25.

#[global] Definition nullAddrIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #39.

#[global] Definition voidArgIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #40.

#[global] Definition leftSectionKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #45.

#[global] Definition rightSectionKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #46.

#[global] Definition rootMainKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #101.

#[global] Definition lazyIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #104.

#[global] Definition oneShotKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #106.

#[global] Definition nospecIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #109.

#[global] Definition coercionTokenIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #124.

#[global] Definition noinlineIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #126.

#[global] Definition noinlineConstraintIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #127.

#[global] Definition coerceKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #157.

#[global] Definition proxyHashKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #502.

#[global] Definition mkTyConKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #503.

#[global] Definition eqSCSelIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #551.

#[global] Definition heqSCSelIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #552.

#[global] Definition coercibleSCSelIdKey : Unique.Unique :=
  GHC.Builtin.Uniques.mkPreludeMiscIdUnique #553.

#[global] Definition fractionalClassKeys : list Unique.Unique :=
  cons fractionalClassKey (cons floatingClassKey (cons realFracClassKey (cons
                                                        realFloatClassKey nil))).

#[global] Definition numericClassKeys : list Unique.Unique :=
  Coq.Init.Datatypes.app (cons numClassKey (cons realClassKey (cons
                                                  integralClassKey nil))) fractionalClassKeys.

#[global] Definition derivableClassKeys : list Unique.Unique :=
  cons eqClassKey (cons ordClassKey (cons enumClassKey (cons ixClassKey (cons
                                                              boundedClassKey (cons showClassKey (cons readClassKey
                                                                                                       nil)))))).

#[global] Definition standardClassKeys : list Unique.Unique :=
  Coq.Init.Datatypes.app derivableClassKeys (Coq.Init.Datatypes.app
                          numericClassKeys (cons randomClassKey (cons randomGenClassKey (cons
                                                                       functorClassKey (cons monadClassKey (cons
                                                                                              monadPlusClassKey (cons
                                                                                               monadFailClassKey (cons
                                                                                                semigroupClassKey (cons
                                                                                                 monoidClassKey (cons
                                                                                                  isStringClassKey (cons
                                                                                                   applicativeClassKey
                                                                                                   (cons
                                                                                                    foldableClassKey
                                                                                                    (cons
                                                                                                     traversableClassKey
                                                                                                     (cons
                                                                                                      alternativeClassKey
                                                                                                      nil)))))))))))))).

#[global] Definition interactiveClassNames : list Name.Name :=
  cons showClassName (cons eqClassName (cons ordClassName (cons foldableClassName
                                                                (cons traversableClassName nil)))).

#[global] Definition interactiveClassKeys : list Unique.Unique :=
  GHC.Base.map Unique.getUnique interactiveClassNames.

(* External variables:
     Type bool cons list nil Coq.Init.Datatypes.app GHC.Base.String GHC.Base.map
     GHC.Builtin.Uniques.mkPreludeClassUnique
     GHC.Builtin.Uniques.mkPreludeDataConUnique
     GHC.Builtin.Uniques.mkPreludeMiscIdUnique
     GHC.Builtin.Uniques.mkPreludeTyConUnique GHC.Data.FastString.FastString
     GHC.Data.FastString.fsLit GHC.Data.List.Infinite.Infinite
     GHC.Data.List.Infinite.toList GHC.Enum.enumFromTo GHC.Num.fromInteger
     GHC.Types.Name.Reader.mkOrig GHC.Unit.Types.Module GHC.Unit.Types.baseUnit
     GHC.Unit.Types.bignumUnit GHC.Unit.Types.experimentalUnit
     GHC.Unit.Types.ghcInternalUnit GHC.Unit.Types.mainUnit GHC.Unit.Types.mkModule
     GHC.Unit.Types.primUnit GHC.Unit.Types.thisGhcUnit
     Language.Haskell.Syntax.Module.Name.ModuleName
     Language.Haskell.Syntax.Module.Name.mkModuleNameFS Name.Name Name.mkExternalName
     Name.mkInternalName Name.mkSystemVarName OccName.NameSpace OccName.OccName
     OccName.clsName OccName.dataName OccName.fieldName OccName.mkOccNameFS
     OccName.tcName OccName.varName SrcLoc.SrcSpan SrcLoc.noSrcSpan Unique.Unique
     Unique.getUnique Unique.hasKey
*)
