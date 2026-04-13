(* Default settings (from HsToRocq.Rocq.Preamble) *)

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

Require FastString.
Require GHC.Base.
Require GHC.Data.List.Infinite.
Require Module.
Require Name.
Require OccName.
Require SrcLoc.
Require Unique.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom int8X16PrimTyConKey : Unique.Unique.

Axiom int16X8PrimTyConKey : Unique.Unique.

Axiom int32X4PrimTyConKey : Unique.Unique.

Axiom int64X2PrimTyConKey : Unique.Unique.

Axiom int8X32PrimTyConKey : Unique.Unique.

Axiom int16X16PrimTyConKey : Unique.Unique.

Axiom int32X8PrimTyConKey : Unique.Unique.

Axiom int64X4PrimTyConKey : Unique.Unique.

Axiom int8X64PrimTyConKey : Unique.Unique.

Axiom int16X32PrimTyConKey : Unique.Unique.

Axiom int32X16PrimTyConKey : Unique.Unique.

Axiom int64X8PrimTyConKey : Unique.Unique.

Axiom word8X16PrimTyConKey : Unique.Unique.

Axiom word16X8PrimTyConKey : Unique.Unique.

Axiom word32X4PrimTyConKey : Unique.Unique.

Axiom word64X2PrimTyConKey : Unique.Unique.

Axiom word8X32PrimTyConKey : Unique.Unique.

Axiom word16X16PrimTyConKey : Unique.Unique.

Axiom word32X8PrimTyConKey : Unique.Unique.

Axiom word64X4PrimTyConKey : Unique.Unique.

Axiom word8X64PrimTyConKey : Unique.Unique.

Axiom word16X32PrimTyConKey : Unique.Unique.

Axiom word32X16PrimTyConKey : Unique.Unique.

Axiom word64X8PrimTyConKey : Unique.Unique.

Axiom floatX4PrimTyConKey : Unique.Unique.

Axiom doubleX2PrimTyConKey : Unique.Unique.

Axiom floatX8PrimTyConKey : Unique.Unique.

Axiom doubleX4PrimTyConKey : Unique.Unique.

Axiom floatX16PrimTyConKey : Unique.Unique.

Axiom doubleX8PrimTyConKey : Unique.Unique.

Axiom allNameStrings : GHC.Data.List.Infinite.Infinite GHC.Base.String.

Axiom allNameStringList : list GHC.Base.String.

Axiom itName : Unique.Unique -> SrcLoc.SrcSpan -> Name.Name.

Axiom mkUnboundName : OccName.OccName -> Name.Name.

Axiom isUnboundName : Name.Name -> bool.

Axiom basicKnownKeyNames : list Name.Name.

Axiom genericTyConNames : list Name.Name.

Axiom gHC_PRIM : Module.Module.

Axiom gHC_PRIM_PANIC : Module.Module.

Axiom gHC_TYPES : Module.Module.

Axiom gHC_MAGIC : Module.Module.

Axiom gHC_MAGIC_DICT : Module.Module.

Axiom gHC_CSTRING : Module.Module.

Axiom gHC_CLASSES : Module.Module.

Axiom gHC_PRIMOPWRAPPERS : Module.Module.

Axiom gHC_INTERNAL_TUPLE : Module.Module.

Axiom pRELUDE : Module.Module.

Axiom dATA_LIST : Module.Module.

Axiom cONTROL_MONAD_ZIP : Module.Module.

Axiom gHC_INTERNAL_NUM_INTEGER : Module.Module.

Axiom gHC_INTERNAL_NUM_NATURAL : Module.Module.

Axiom gHC_INTERNAL_NUM_BIGNAT : Module.Module.

Axiom gHC_INTERNAL_BASE : Module.Module.

Axiom gHC_INTERNAL_ENUM : Module.Module.

Axiom gHC_INTERNAL_GHCI : Module.Module.

Axiom gHC_INTERNAL_GHCI_HELPERS : Module.Module.

Axiom gHC_INTERNAL_SHOW : Module.Module.

Axiom gHC_INTERNAL_READ : Module.Module.

Axiom gHC_INTERNAL_NUM : Module.Module.

Axiom gHC_INTERNAL_MAYBE : Module.Module.

Axiom gHC_INTERNAL_LIST : Module.Module.

Axiom gHC_INTERNAL_DATA_EITHER : Module.Module.

Axiom gHC_INTERNAL_DATA_STRING : Module.Module.

Axiom gHC_INTERNAL_DATA_FOLDABLE : Module.Module.

Axiom gHC_INTERNAL_DATA_TRAVERSABLE : Module.Module.

Axiom gHC_INTERNAL_CONC : Module.Module.

Axiom gHC_INTERNAL_IO : Module.Module.

Axiom gHC_INTERNAL_IO_Exception : Module.Module.

Axiom gHC_INTERNAL_ST : Module.Module.

Axiom gHC_INTERNAL_IX : Module.Module.

Axiom gHC_INTERNAL_STABLE : Module.Module.

Axiom gHC_INTERNAL_PTR : Module.Module.

Axiom gHC_INTERNAL_ERR : Module.Module.

Axiom gHC_INTERNAL_REAL : Module.Module.

Axiom gHC_INTERNAL_FLOAT : Module.Module.

Axiom gHC_INTERNAL_TOP_HANDLER : Module.Module.

Axiom gHC_INTERNAL_SYSTEM_IO : Module.Module.

Axiom gHC_INTERNAL_DYNAMIC : Module.Module.

Axiom gHC_INTERNAL_TYPEABLE : Module.Module.

Axiom gHC_INTERNAL_TYPEABLE_INTERNAL : Module.Module.

Axiom gHC_INTERNAL_DATA_DATA : Module.Module.

Axiom gHC_INTERNAL_READ_PREC : Module.Module.

Axiom gHC_INTERNAL_LEX : Module.Module.

Axiom gHC_INTERNAL_INT : Module.Module.

Axiom gHC_INTERNAL_WORD : Module.Module.

Axiom gHC_INTERNAL_MONAD : Module.Module.

Axiom gHC_INTERNAL_MONAD_FIX : Module.Module.

Axiom gHC_INTERNAL_MONAD_FAIL : Module.Module.

Axiom gHC_INTERNAL_ARROW : Module.Module.

Axiom gHC_INTERNAL_DESUGAR : Module.Module.

Axiom gHC_INTERNAL_RANDOM : Module.Module.

Axiom gHC_INTERNAL_EXTS : Module.Module.

Axiom gHC_INTERNAL_IS_LIST : Module.Module.

Axiom gHC_INTERNAL_CONTROL_EXCEPTION_BASE : Module.Module.

Axiom gHC_INTERNAL_EXCEPTION_CONTEXT : Module.Module.

Axiom gHC_INTERNAL_GENERICS : Module.Module.

Axiom gHC_INTERNAL_TYPEERROR : Module.Module.

Axiom gHC_INTERNAL_TYPELITS : Module.Module.

Axiom gHC_INTERNAL_TYPELITS_INTERNAL : Module.Module.

Axiom gHC_INTERNAL_TYPENATS : Module.Module.

Axiom gHC_INTERNAL_TYPENATS_INTERNAL : Module.Module.

Axiom gHC_INTERNAL_DATA_COERCE : Module.Module.

Axiom gHC_INTERNAL_DEBUG_TRACE : Module.Module.

Axiom gHC_INTERNAL_UNSAFE_COERCE : Module.Module.

Axiom gHC_INTERNAL_FOREIGN_C_CONSTPTR : Module.Module.

Axiom gHC_INTERNAL_SRCLOC : Module.Module.

Axiom gHC_INTERNAL_STACK : Module.Module.

Axiom gHC_INTERNAL_STACK_TYPES : Module.Module.

Axiom gHC_INTERNAL_STATICPTR : Module.Module.

Axiom gHC_INTERNAL_STATICPTR_INTERNAL : Module.Module.

Axiom gHC_INTERNAL_FINGERPRINT_TYPE : Module.Module.

Axiom gHC_INTERNAL_OVER_LABELS : Module.Module.

Axiom gHC_INTERNAL_RECORDS : Module.Module.

Axiom dATA_TUPLE_EXPERIMENTAL : Module.Module.

Axiom dATA_SUM_EXPERIMENTAL : Module.Module.

Axiom rOOT_MAIN : Module.Module.

Axiom mkInteractiveModule : GHC.Base.String -> Module.Module.

Axiom pRELUDE_NAME : Module.ModuleName.

Axiom mAIN_NAME : Module.ModuleName.

Axiom mkPrimModule : FastString.FastString -> Module.Module.

Axiom mkBignumModule : FastString.FastString -> Module.Module.

Axiom mkGhcInternalModule : FastString.FastString -> Module.Module.

Axiom mkGhcInternalModule_ : Module.ModuleName -> Module.Module.

Axiom mkBaseModule : FastString.FastString -> Module.Module.

Axiom mkBaseModule_ : Module.ModuleName -> Module.Module.

Axiom mkThisGhcModule : FastString.FastString -> Module.Module.

Axiom mkThisGhcModule_ : Module.ModuleName -> Module.Module.

Axiom mkMainModule : FastString.FastString -> Module.Module.

Axiom mkMainModule_ : Module.ModuleName -> Module.Module.

Axiom mkExperimentalModule : FastString.FastString -> Module.Module.

Axiom RdrName : Type.

Axiom main_RDR_Unqual : RdrName.

Axiom eq_RDR : RdrName.

Axiom ge_RDR : RdrName.

Axiom le_RDR : RdrName.

Axiom lt_RDR : RdrName.

Axiom gt_RDR : RdrName.

Axiom compare_RDR : RdrName.

Axiom ltTag_RDR : RdrName.

Axiom eqTag_RDR : RdrName.

Axiom gtTag_RDR : RdrName.

Axiom map_RDR : RdrName.

Axiom append_RDR : RdrName.

Axiom foldr_RDR : RdrName.

Axiom build_RDR : RdrName.

Axiom returnM_RDR : RdrName.

Axiom bindM_RDR : RdrName.

Axiom failM_RDR : RdrName.

Axiom left_RDR : RdrName.

Axiom right_RDR : RdrName.

Axiom fromEnum_RDR : RdrName.

Axiom toEnum_RDR : RdrName.

Axiom enumFrom_RDR : RdrName.

Axiom enumFromTo_RDR : RdrName.

Axiom enumFromThen_RDR : RdrName.

Axiom enumFromThenTo_RDR : RdrName.

Axiom times_RDR : RdrName.

Axiom plus_RDR : RdrName.

Axiom compose_RDR : RdrName.

Axiom and_RDR : RdrName.

Axiom not_RDR : RdrName.

Axiom dataToTag_RDR : RdrName.

Axiom succ_RDR : RdrName.

Axiom pred_RDR : RdrName.

Axiom minBound_RDR : RdrName.

Axiom maxBound_RDR : RdrName.

Axiom range_RDR : RdrName.

Axiom inRange_RDR : RdrName.

Axiom index_RDR : RdrName.

Axiom unsafeIndex_RDR : RdrName.

Axiom unsafeRangeSize_RDR : RdrName.

Axiom readList_RDR : RdrName.

Axiom readListDefault_RDR : RdrName.

Axiom readListPrec_RDR : RdrName.

Axiom readListPrecDefault_RDR : RdrName.

Axiom readPrec_RDR : RdrName.

Axiom parens_RDR : RdrName.

Axiom choose_RDR : RdrName.

Axiom lexP_RDR : RdrName.

Axiom expectP_RDR : RdrName.

Axiom readField_RDR : RdrName.

Axiom readFieldHash_RDR : RdrName.

Axiom readSymField_RDR : RdrName.

Axiom punc_RDR : RdrName.

Axiom ident_RDR : RdrName.

Axiom symbol_RDR : RdrName.

Axiom step_RDR : RdrName.

Axiom alt_RDR : RdrName.

Axiom reset_RDR : RdrName.

Axiom prec_RDR : RdrName.

Axiom pfail_RDR : RdrName.

Axiom showsPrec_RDR : RdrName.

Axiom shows_RDR : RdrName.

Axiom showString_RDR : RdrName.

Axiom showSpace_RDR : RdrName.

Axiom showCommaSpace_RDR : RdrName.

Axiom showParen_RDR : RdrName.

Axiom error_RDR : RdrName.

Axiom u1DataCon_RDR : RdrName.

Axiom par1DataCon_RDR : RdrName.

Axiom rec1DataCon_RDR : RdrName.

Axiom k1DataCon_RDR : RdrName.

Axiom m1DataCon_RDR : RdrName.

Axiom l1DataCon_RDR : RdrName.

Axiom r1DataCon_RDR : RdrName.

Axiom prodDataCon_RDR : RdrName.

Axiom comp1DataCon_RDR : RdrName.

Axiom unPar1_RDR : RdrName.

Axiom unRec1_RDR : RdrName.

Axiom unK1_RDR : RdrName.

Axiom unComp1_RDR : RdrName.

Axiom from_RDR : RdrName.

Axiom from1_RDR : RdrName.

Axiom to_RDR : RdrName.

Axiom to1_RDR : RdrName.

Axiom datatypeName_RDR : RdrName.

Axiom moduleName_RDR : RdrName.

Axiom packageName_RDR : RdrName.

Axiom isNewtypeName_RDR : RdrName.

Axiom selName_RDR : RdrName.

Axiom conName_RDR : RdrName.

Axiom conFixity_RDR : RdrName.

Axiom conIsRecord_RDR : RdrName.

Axiom prefixDataCon_RDR : RdrName.

Axiom infixDataCon_RDR : RdrName.

Axiom leftAssocDataCon_RDR : RdrName.

Axiom rightAssocDataCon_RDR : RdrName.

Axiom notAssocDataCon_RDR : RdrName.

Axiom uAddrDataCon_RDR : RdrName.

Axiom uCharDataCon_RDR : RdrName.

Axiom uDoubleDataCon_RDR : RdrName.

Axiom uFloatDataCon_RDR : RdrName.

Axiom uIntDataCon_RDR : RdrName.

Axiom uWordDataCon_RDR : RdrName.

Axiom uAddrHash_RDR : RdrName.

Axiom uCharHash_RDR : RdrName.

Axiom uDoubleHash_RDR : RdrName.

Axiom uFloatHash_RDR : RdrName.

Axiom uIntHash_RDR : RdrName.

Axiom uWordHash_RDR : RdrName.

Axiom fmap_RDR : RdrName.

Axiom replace_RDR : RdrName.

Axiom pure_RDR : RdrName.

Axiom ap_RDR : RdrName.

Axiom liftA2_RDR : RdrName.

Axiom foldable_foldr_RDR : RdrName.

Axiom foldMap_RDR : RdrName.

Axiom null_RDR : RdrName.

Axiom all_RDR : RdrName.

Axiom traverse_RDR : RdrName.

Axiom mempty_RDR : RdrName.

Axiom mappend_RDR : RdrName.

Axiom varQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Axiom tcQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Axiom clsQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Axiom dataQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Axiom fieldQual_RDR : Module.Module ->
                      FastString.FastString -> FastString.FastString -> RdrName.

Axiom wildCardName : Name.Name.

Axiom runMainIOName : Name.Name.

Axiom runRWName : Name.Name.

Axiom orderingTyConName : Name.Name.

Axiom ordLTDataConName : Name.Name.

Axiom ordEQDataConName : Name.Name.

Axiom ordGTDataConName : Name.Name.

Axiom specTyConName : Name.Name.

Axiom eitherTyConName : Name.Name.

Axiom leftDataConName : Name.Name.

Axiom rightDataConName : Name.Name.

Axiom voidTyConName : Name.Name.

Axiom v1TyConName : Name.Name.

Axiom u1TyConName : Name.Name.

Axiom par1TyConName : Name.Name.

Axiom rec1TyConName : Name.Name.

Axiom k1TyConName : Name.Name.

Axiom m1TyConName : Name.Name.

Axiom sumTyConName : Name.Name.

Axiom prodTyConName : Name.Name.

Axiom compTyConName : Name.Name.

Axiom rTyConName : Name.Name.

Axiom dTyConName : Name.Name.

Axiom cTyConName : Name.Name.

Axiom sTyConName : Name.Name.

Axiom rec0TyConName : Name.Name.

Axiom d1TyConName : Name.Name.

Axiom c1TyConName : Name.Name.

Axiom s1TyConName : Name.Name.

Axiom repTyConName : Name.Name.

Axiom rep1TyConName : Name.Name.

Axiom uRecTyConName : Name.Name.

Axiom uAddrTyConName : Name.Name.

Axiom uCharTyConName : Name.Name.

Axiom uDoubleTyConName : Name.Name.

Axiom uFloatTyConName : Name.Name.

Axiom uIntTyConName : Name.Name.

Axiom uWordTyConName : Name.Name.

Axiom prefixIDataConName : Name.Name.

Axiom infixIDataConName : Name.Name.

Axiom leftAssociativeDataConName : Name.Name.

Axiom rightAssociativeDataConName : Name.Name.

Axiom notAssociativeDataConName : Name.Name.

Axiom sourceUnpackDataConName : Name.Name.

Axiom sourceNoUnpackDataConName : Name.Name.

Axiom noSourceUnpackednessDataConName : Name.Name.

Axiom sourceLazyDataConName : Name.Name.

Axiom sourceStrictDataConName : Name.Name.

Axiom noSourceStrictnessDataConName : Name.Name.

Axiom decidedLazyDataConName : Name.Name.

Axiom decidedStrictDataConName : Name.Name.

Axiom decidedUnpackDataConName : Name.Name.

Axiom metaDataDataConName : Name.Name.

Axiom metaConsDataConName : Name.Name.

Axiom metaSelDataConName : Name.Name.

Axiom divIntName : Name.Name.

Axiom modIntName : Name.Name.

Axiom cstringLengthName : Name.Name.

Axiom eqStringName : Name.Name.

Axiom unpackCStringName : Name.Name.

Axiom unpackCStringAppendName : Name.Name.

Axiom unpackCStringFoldrName : Name.Name.

Axiom unpackCStringUtf8Name : Name.Name.

Axiom unpackCStringAppendUtf8Name : Name.Name.

Axiom unpackCStringFoldrUtf8Name : Name.Name.

Axiom inlineIdName : Name.Name.

Axiom eqClassName : Name.Name.

Axiom eqName : Name.Name.

Axiom ordClassName : Name.Name.

Axiom geName : Name.Name.

Axiom functorClassName : Name.Name.

Axiom fmapName : Name.Name.

Axiom monadClassName : Name.Name.

Axiom thenMName : Name.Name.

Axiom bindMName : Name.Name.

Axiom returnMName : Name.Name.

Axiom monadFailClassName : Name.Name.

Axiom failMName : Name.Name.

Axiom applicativeClassName : Name.Name.

Axiom apAName : Name.Name.

Axiom pureAName : Name.Name.

Axiom thenAName : Name.Name.

Axiom foldableClassName : Name.Name.

Axiom traversableClassName : Name.Name.

Axiom semigroupClassName : Name.Name.

Axiom sappendName : Name.Name.

Axiom monoidClassName : Name.Name.

Axiom memptyName : Name.Name.

Axiom mappendName : Name.Name.

Axiom mconcatName : Name.Name.

Axiom joinMName : Name.Name.

Axiom alternativeClassName : Name.Name.

Axiom joinMIdKey : Unique.Unique.

Axiom apAClassOpKey : Unique.Unique.

Axiom pureAClassOpKey : Unique.Unique.

Axiom thenAClassOpKey : Unique.Unique.

Axiom alternativeClassKey : Unique.Unique.

Axiom considerAccessibleName : Name.Name.

Axiom dollarName : Name.Name.

Axiom otherwiseIdName : Name.Name.

Axiom foldrName : Name.Name.

Axiom buildName : Name.Name.

Axiom augmentName : Name.Name.

Axiom mapName : Name.Name.

Axiom appendName : Name.Name.

Axiom assertName : Name.Name.

Axiom fromStringName : Name.Name.

Axiom numClassName : Name.Name.

Axiom fromIntegerName : Name.Name.

Axiom minusName : Name.Name.

Axiom negateName : Name.Name.

Axiom bnbVarQual : GHC.Base.String -> Unique.Unique -> Name.Name.

Axiom bnnVarQual : GHC.Base.String -> Unique.Unique -> Name.Name.

Axiom bniVarQual : GHC.Base.String -> Unique.Unique -> Name.Name.

Axiom bignatEqName : Name.Name.

Axiom bignatCompareName : Name.Name.

Axiom bignatCompareWordName : Name.Name.

Axiom naturalToWordName : Name.Name.

Axiom naturalPopCountName : Name.Name.

Axiom naturalShiftRName : Name.Name.

Axiom naturalShiftLName : Name.Name.

Axiom naturalAddName : Name.Name.

Axiom naturalSubName : Name.Name.

Axiom naturalSubThrowName : Name.Name.

Axiom naturalSubUnsafeName : Name.Name.

Axiom naturalMulName : Name.Name.

Axiom naturalQuotRemName : Name.Name.

Axiom naturalQuotName : Name.Name.

Axiom naturalRemName : Name.Name.

Axiom naturalAndName : Name.Name.

Axiom naturalAndNotName : Name.Name.

Axiom naturalOrName : Name.Name.

Axiom naturalXorName : Name.Name.

Axiom naturalTestBitName : Name.Name.

Axiom naturalBitName : Name.Name.

Axiom naturalGcdName : Name.Name.

Axiom naturalLcmName : Name.Name.

Axiom naturalLog2Name : Name.Name.

Axiom naturalLogBaseWordName : Name.Name.

Axiom naturalLogBaseName : Name.Name.

Axiom naturalPowModName : Name.Name.

Axiom naturalSizeInBaseName : Name.Name.

Axiom integerFromNaturalName : Name.Name.

Axiom integerToNaturalClampName : Name.Name.

Axiom integerToNaturalThrowName : Name.Name.

Axiom integerToNaturalName : Name.Name.

Axiom integerToWordName : Name.Name.

Axiom integerToIntName : Name.Name.

Axiom integerToWord64Name : Name.Name.

Axiom integerToInt64Name : Name.Name.

Axiom integerFromWordName : Name.Name.

Axiom integerFromWord64Name : Name.Name.

Axiom integerFromInt64Name : Name.Name.

Axiom integerAddName : Name.Name.

Axiom integerMulName : Name.Name.

Axiom integerSubName : Name.Name.

Axiom integerNegateName : Name.Name.

Axiom integerAbsName : Name.Name.

Axiom integerPopCountName : Name.Name.

Axiom integerQuotName : Name.Name.

Axiom integerRemName : Name.Name.

Axiom integerDivName : Name.Name.

Axiom integerModName : Name.Name.

Axiom integerDivModName : Name.Name.

Axiom integerQuotRemName : Name.Name.

Axiom integerEncodeFloatName : Name.Name.

Axiom integerEncodeDoubleName : Name.Name.

Axiom integerGcdName : Name.Name.

Axiom integerLcmName : Name.Name.

Axiom integerAndName : Name.Name.

Axiom integerOrName : Name.Name.

Axiom integerXorName : Name.Name.

Axiom integerComplementName : Name.Name.

Axiom integerBitName : Name.Name.

Axiom integerTestBitName : Name.Name.

Axiom integerShiftLName : Name.Name.

Axiom integerShiftRName : Name.Name.

Axiom rationalTyConName : Name.Name.

Axiom ratioTyConName : Name.Name.

Axiom ratioDataConName : Name.Name.

Axiom realClassName : Name.Name.

Axiom integralClassName : Name.Name.

Axiom realFracClassName : Name.Name.

Axiom fractionalClassName : Name.Name.

Axiom fromRationalName : Name.Name.

Axiom toIntegerName : Name.Name.

Axiom toRationalName : Name.Name.

Axiom fromIntegralName : Name.Name.

Axiom realToFracName : Name.Name.

Axiom mkRationalBase2Name : Name.Name.

Axiom mkRationalBase10Name : Name.Name.

Axiom floatingClassName : Name.Name.

Axiom realFloatClassName : Name.Name.

Axiom integerToFloatName : Name.Name.

Axiom integerToDoubleName : Name.Name.

Axiom naturalToFloatName : Name.Name.

Axiom naturalToDoubleName : Name.Name.

Axiom rationalToFloatName : Name.Name.

Axiom rationalToDoubleName : Name.Name.

Axiom ixClassName : Name.Name.

Axiom trModuleTyConName : Name.Name.

Axiom trModuleDataConName : Name.Name.

Axiom trNameTyConName : Name.Name.

Axiom trNameSDataConName : Name.Name.

Axiom trNameDDataConName : Name.Name.

Axiom trTyConTyConName : Name.Name.

Axiom trTyConDataConName : Name.Name.

Axiom kindRepTyConName : Name.Name.

Axiom kindRepTyConAppDataConName : Name.Name.

Axiom kindRepVarDataConName : Name.Name.

Axiom kindRepAppDataConName : Name.Name.

Axiom kindRepFunDataConName : Name.Name.

Axiom kindRepTYPEDataConName : Name.Name.

Axiom kindRepTypeLitSDataConName : Name.Name.

Axiom kindRepTypeLitDDataConName : Name.Name.

Axiom typeLitSortTyConName : Name.Name.

Axiom typeLitSymbolDataConName : Name.Name.

Axiom typeLitNatDataConName : Name.Name.

Axiom typeLitCharDataConName : Name.Name.

Axiom typeableClassName : Name.Name.

Axiom typeRepTyConName : Name.Name.

Axiom someTypeRepTyConName : Name.Name.

Axiom someTypeRepDataConName : Name.Name.

Axiom typeRepIdName : Name.Name.

Axiom mkTrTypeName : Name.Name.

Axiom mkTrConName : Name.Name.

Axiom mkTrAppCheckedName : Name.Name.

Axiom mkTrFunName : Name.Name.

Axiom typeNatTypeRepName : Name.Name.

Axiom typeSymbolTypeRepName : Name.Name.

Axiom typeCharTypeRepName : Name.Name.

Axiom trGhcPrimModuleName : Name.Name.

Axiom starKindRepName : Name.Name.

Axiom starArrStarKindRepName : Name.Name.

Axiom starArrStarArrStarKindRepName : Name.Name.

Axiom constraintKindRepName : Name.Name.

Axiom withDictClassName : Name.Name.

Axiom nonEmptyTyConName : Name.Name.

Axiom dataToTagClassName : Name.Name.

Axiom errorMessageTypeErrorFamName : Name.Name.

Axiom typeErrorTextDataConName : Name.Name.

Axiom typeErrorAppendDataConName : Name.Name.

Axiom typeErrorVAppendDataConName : Name.Name.

Axiom typeErrorShowTypeDataConName : Name.Name.

Axiom unsatisfiableClassName : Name.Name.

Axiom unsatisfiableIdName : Name.Name.

Axiom unsafeEqualityProofName : Name.Name.

Axiom unsafeEqualityTyConName : Name.Name.

Axiom unsafeReflDataConName : Name.Name.

Axiom unsafeCoercePrimName : Name.Name.

Axiom toDynName : Name.Name.

Axiom dataClassName : Name.Name.

Axiom assertErrorName : Name.Name.

Axiom traceName : Name.Name.

Axiom enumClassName : Name.Name.

Axiom enumFromName : Name.Name.

Axiom enumFromToName : Name.Name.

Axiom enumFromThenName : Name.Name.

Axiom enumFromThenToName : Name.Name.

Axiom boundedClassName : Name.Name.

Axiom concatName : Name.Name.

Axiom filterName : Name.Name.

Axiom zipName : Name.Name.

Axiom isListClassName : Name.Name.

Axiom fromListName : Name.Name.

Axiom fromListNName : Name.Name.

Axiom toListName : Name.Name.

Axiom getFieldName : Name.Name.

Axiom setFieldName : Name.Name.

Axiom showClassName : Name.Name.

Axiom readClassName : Name.Name.

Axiom genClassName : Name.Name.

Axiom gen1ClassName : Name.Name.

Axiom datatypeClassName : Name.Name.

Axiom constructorClassName : Name.Name.

Axiom selectorClassName : Name.Name.

Axiom genericClassNames : list Name.Name.

Axiom ghciIoClassName : Name.Name.

Axiom ghciStepIoMName : Name.Name.

Axiom ioTyConName : Name.Name.

Axiom ioDataConName : Name.Name.

Axiom thenIOName : Name.Name.

Axiom bindIOName : Name.Name.

Axiom returnIOName : Name.Name.

Axiom failIOName : Name.Name.

Axiom printName : Name.Name.

Axiom int8TyConName : Name.Name.

Axiom int16TyConName : Name.Name.

Axiom int32TyConName : Name.Name.

Axiom int64TyConName : Name.Name.

Axiom word8TyConName : Name.Name.

Axiom word16TyConName : Name.Name.

Axiom word32TyConName : Name.Name.

Axiom word64TyConName : Name.Name.

Axiom ptrTyConName : Name.Name.

Axiom funPtrTyConName : Name.Name.

Axiom stablePtrTyConName : Name.Name.

Axiom newStablePtrName : Name.Name.

Axiom monadFixClassName : Name.Name.

Axiom mfixName : Name.Name.

Axiom arrAName : Name.Name.

Axiom composeAName : Name.Name.

Axiom firstAName : Name.Name.

Axiom appAName : Name.Name.

Axiom choiceAName : Name.Name.

Axiom loopAName : Name.Name.

Axiom guardMName : Name.Name.

Axiom liftMName : Name.Name.

Axiom mzipName : Name.Name.

Axiom toAnnotationWrapperName : Name.Name.

Axiom monadPlusClassName : Name.Name.

Axiom isStringClassName : Name.Name.

Axiom knownNatClassName : Name.Name.

Axiom knownSymbolClassName : Name.Name.

Axiom knownCharClassName : Name.Name.

Axiom fromLabelClassOpName : Name.Name.

Axiom ipClassName : Name.Name.

Axiom hasFieldClassName : Name.Name.

Axiom exceptionContextTyConName : Name.Name.

Axiom emptyExceptionContextName : Name.Name.

Axiom callStackTyConName : Name.Name.

Axiom emptyCallStackName : Name.Name.

Axiom pushCallStackName : Name.Name.

Axiom srcLocDataConName : Name.Name.

Axiom pLUGINS : Module.Module.

Axiom pluginTyConName : Name.Name.

Axiom frontendPluginTyConName : Name.Name.

Axiom makeStaticName : Name.Name.

Axiom staticPtrInfoTyConName : Name.Name.

Axiom staticPtrInfoDataConName : Name.Name.

Axiom staticPtrTyConName : Name.Name.

Axiom staticPtrDataConName : Name.Name.

Axiom fromStaticPtrName : Name.Name.

Axiom fingerprintDataConName : Name.Name.

Axiom constPtrConName : Name.Name.

Axiom jsvalTyConName : Name.Name.

Axiom varQual : Module.Module ->
                FastString.FastString -> Unique.Unique -> Name.Name.

Axiom tcQual : Module.Module ->
               FastString.FastString -> Unique.Unique -> Name.Name.

Axiom clsQual : Module.Module ->
                FastString.FastString -> Unique.Unique -> Name.Name.

Axiom dcQual : Module.Module ->
               FastString.FastString -> Unique.Unique -> Name.Name.

Axiom mk_known_key_name : OccName.NameSpace ->
                          Module.Module -> FastString.FastString -> Unique.Unique -> Name.Name.

Axiom boundedClassKey : Unique.Unique.

Axiom enumClassKey : Unique.Unique.

Axiom eqClassKey : Unique.Unique.

Axiom floatingClassKey : Unique.Unique.

Axiom fractionalClassKey : Unique.Unique.

Axiom integralClassKey : Unique.Unique.

Axiom monadClassKey : Unique.Unique.

Axiom dataClassKey : Unique.Unique.

Axiom functorClassKey : Unique.Unique.

Axiom numClassKey : Unique.Unique.

Axiom ordClassKey : Unique.Unique.

Axiom readClassKey : Unique.Unique.

Axiom realClassKey : Unique.Unique.

Axiom realFloatClassKey : Unique.Unique.

Axiom realFracClassKey : Unique.Unique.

Axiom showClassKey : Unique.Unique.

Axiom ixClassKey : Unique.Unique.

Axiom typeableClassKey : Unique.Unique.

Axiom withDictClassKey : Unique.Unique.

Axiom dataToTagClassKey : Unique.Unique.

Axiom monadFixClassKey : Unique.Unique.

Axiom monadFailClassKey : Unique.Unique.

Axiom monadPlusClassKey : Unique.Unique.

Axiom randomClassKey : Unique.Unique.

Axiom randomGenClassKey : Unique.Unique.

Axiom isStringClassKey : Unique.Unique.

Axiom applicativeClassKey : Unique.Unique.

Axiom foldableClassKey : Unique.Unique.

Axiom traversableClassKey : Unique.Unique.

Axiom genClassKey : Unique.Unique.

Axiom gen1ClassKey : Unique.Unique.

Axiom datatypeClassKey : Unique.Unique.

Axiom constructorClassKey : Unique.Unique.

Axiom selectorClassKey : Unique.Unique.

Axiom knownNatClassNameKey : Unique.Unique.

Axiom knownSymbolClassNameKey : Unique.Unique.

Axiom knownCharClassNameKey : Unique.Unique.

Axiom ghciIoClassKey : Unique.Unique.

Axiom semigroupClassKey : Unique.Unique.

Axiom monoidClassKey : Unique.Unique.

Axiom ipClassKey : Unique.Unique.

Axiom hasFieldClassNameKey : Unique.Unique.

Axiom addrPrimTyConKey : Unique.Unique.

Axiom arrayPrimTyConKey : Unique.Unique.

Axiom boolTyConKey : Unique.Unique.

Axiom byteArrayPrimTyConKey : Unique.Unique.

Axiom stringTyConKey : Unique.Unique.

Axiom charPrimTyConKey : Unique.Unique.

Axiom charTyConKey : Unique.Unique.

Axiom doublePrimTyConKey : Unique.Unique.

Axiom doubleTyConKey : Unique.Unique.

Axiom floatPrimTyConKey : Unique.Unique.

Axiom floatTyConKey : Unique.Unique.

Axiom fUNTyConKey : Unique.Unique.

Axiom intPrimTyConKey : Unique.Unique.

Axiom intTyConKey : Unique.Unique.

Axiom int8PrimTyConKey : Unique.Unique.

Axiom int8TyConKey : Unique.Unique.

Axiom int16PrimTyConKey : Unique.Unique.

Axiom int16TyConKey : Unique.Unique.

Axiom int32PrimTyConKey : Unique.Unique.

Axiom int32TyConKey : Unique.Unique.

Axiom int64PrimTyConKey : Unique.Unique.

Axiom int64TyConKey : Unique.Unique.

Axiom integerTyConKey : Unique.Unique.

Axiom naturalTyConKey : Unique.Unique.

Axiom listTyConKey : Unique.Unique.

Axiom foreignObjPrimTyConKey : Unique.Unique.

Axiom maybeTyConKey : Unique.Unique.

Axiom weakPrimTyConKey : Unique.Unique.

Axiom mutableArrayPrimTyConKey : Unique.Unique.

Axiom mutableByteArrayPrimTyConKey : Unique.Unique.

Axiom orderingTyConKey : Unique.Unique.

Axiom mVarPrimTyConKey : Unique.Unique.

Axiom ioPortPrimTyConKey : Unique.Unique.

Axiom ratioTyConKey : Unique.Unique.

Axiom rationalTyConKey : Unique.Unique.

Axiom realWorldTyConKey : Unique.Unique.

Axiom stablePtrPrimTyConKey : Unique.Unique.

Axiom stablePtrTyConKey : Unique.Unique.

Axiom eqTyConKey : Unique.Unique.

Axiom heqTyConKey : Unique.Unique.

Axiom ctArrowTyConKey : Unique.Unique.

Axiom ccArrowTyConKey : Unique.Unique.

Axiom tcArrowTyConKey : Unique.Unique.

Axiom statePrimTyConKey : Unique.Unique.

Axiom stableNamePrimTyConKey : Unique.Unique.

Axiom stableNameTyConKey : Unique.Unique.

Axiom eqPrimTyConKey : Unique.Unique.

Axiom eqReprPrimTyConKey : Unique.Unique.

Axiom eqPhantPrimTyConKey : Unique.Unique.

Axiom mutVarPrimTyConKey : Unique.Unique.

Axiom ioTyConKey : Unique.Unique.

Axiom wordPrimTyConKey : Unique.Unique.

Axiom wordTyConKey : Unique.Unique.

Axiom word8PrimTyConKey : Unique.Unique.

Axiom word8TyConKey : Unique.Unique.

Axiom word16PrimTyConKey : Unique.Unique.

Axiom word16TyConKey : Unique.Unique.

Axiom word32PrimTyConKey : Unique.Unique.

Axiom word32TyConKey : Unique.Unique.

Axiom word64PrimTyConKey : Unique.Unique.

Axiom word64TyConKey : Unique.Unique.

Axiom kindConKey : Unique.Unique.

Axiom boxityConKey : Unique.Unique.

Axiom typeConKey : Unique.Unique.

Axiom threadIdPrimTyConKey : Unique.Unique.

Axiom bcoPrimTyConKey : Unique.Unique.

Axiom ptrTyConKey : Unique.Unique.

Axiom funPtrTyConKey : Unique.Unique.

Axiom tVarPrimTyConKey : Unique.Unique.

Axiom compactPrimTyConKey : Unique.Unique.

Axiom stackSnapshotPrimTyConKey : Unique.Unique.

Axiom promptTagPrimTyConKey : Unique.Unique.

Axiom eitherTyConKey : Unique.Unique.

Axiom voidTyConKey : Unique.Unique.

Axiom nonEmptyTyConKey : Unique.Unique.

Axiom dictTyConKey : Unique.Unique.

Axiom liftedTypeKindTyConKey : Unique.Unique.

Axiom unliftedTypeKindTyConKey : Unique.Unique.

Axiom tYPETyConKey : Unique.Unique.

Axiom cONSTRAINTTyConKey : Unique.Unique.

Axiom constraintKindTyConKey : Unique.Unique.

Axiom levityTyConKey : Unique.Unique.

Axiom runtimeRepTyConKey : Unique.Unique.

Axiom vecCountTyConKey : Unique.Unique.

Axiom vecElemTyConKey : Unique.Unique.

Axiom liftedRepTyConKey : Unique.Unique.

Axiom unliftedRepTyConKey : Unique.Unique.

Axiom zeroBitRepTyConKey : Unique.Unique.

Axiom zeroBitTypeTyConKey : Unique.Unique.

Axiom pluginTyConKey : Unique.Unique.

Axiom frontendPluginTyConKey : Unique.Unique.

Axiom trTyConTyConKey : Unique.Unique.

Axiom trModuleTyConKey : Unique.Unique.

Axiom trNameTyConKey : Unique.Unique.

Axiom kindRepTyConKey : Unique.Unique.

Axiom typeLitSortTyConKey : Unique.Unique.

Axiom v1TyConKey : Unique.Unique.

Axiom u1TyConKey : Unique.Unique.

Axiom par1TyConKey : Unique.Unique.

Axiom rec1TyConKey : Unique.Unique.

Axiom k1TyConKey : Unique.Unique.

Axiom m1TyConKey : Unique.Unique.

Axiom sumTyConKey : Unique.Unique.

Axiom prodTyConKey : Unique.Unique.

Axiom compTyConKey : Unique.Unique.

Axiom rTyConKey : Unique.Unique.

Axiom dTyConKey : Unique.Unique.

Axiom cTyConKey : Unique.Unique.

Axiom sTyConKey : Unique.Unique.

Axiom rec0TyConKey : Unique.Unique.

Axiom d1TyConKey : Unique.Unique.

Axiom c1TyConKey : Unique.Unique.

Axiom s1TyConKey : Unique.Unique.

Axiom repTyConKey : Unique.Unique.

Axiom rep1TyConKey : Unique.Unique.

Axiom uRecTyConKey : Unique.Unique.

Axiom uAddrTyConKey : Unique.Unique.

Axiom uCharTyConKey : Unique.Unique.

Axiom uDoubleTyConKey : Unique.Unique.

Axiom uFloatTyConKey : Unique.Unique.

Axiom uIntTyConKey : Unique.Unique.

Axiom uWordTyConKey : Unique.Unique.

Axiom unsatisfiableClassNameKey : Unique.Unique.

Axiom anyTyConKey : Unique.Unique.

Axiom zonkAnyTyConKey : Unique.Unique.

Axiom errorMessageTypeErrorFamKey : Unique.Unique.

Axiom coercibleTyConKey : Unique.Unique.

Axiom proxyPrimTyConKey : Unique.Unique.

Axiom specTyConKey : Unique.Unique.

Axiom smallArrayPrimTyConKey : Unique.Unique.

Axiom smallMutableArrayPrimTyConKey : Unique.Unique.

Axiom staticPtrTyConKey : Unique.Unique.

Axiom staticPtrInfoTyConKey : Unique.Unique.

Axiom callStackTyConKey : Unique.Unique.

Axiom typeRepTyConKey : Unique.Unique.

Axiom someTypeRepTyConKey : Unique.Unique.

Axiom someTypeRepDataConKey : Unique.Unique.

Axiom typeSymbolAppendFamNameKey : Unique.Unique.

Axiom unsafeEqualityTyConKey : Unique.Unique.

Axiom multiplicityTyConKey : Unique.Unique.

Axiom unrestrictedFunTyConKey : Unique.Unique.

Axiom multMulTyConKey : Unique.Unique.

Axiom typeSymbolKindConNameKey : Unique.Unique.

Axiom typeCharKindConNameKey : Unique.Unique.

Axiom typeNatAddTyFamNameKey : Unique.Unique.

Axiom typeNatMulTyFamNameKey : Unique.Unique.

Axiom typeNatExpTyFamNameKey : Unique.Unique.

Axiom typeNatSubTyFamNameKey : Unique.Unique.

Axiom typeSymbolCmpTyFamNameKey : Unique.Unique.

Axiom typeNatCmpTyFamNameKey : Unique.Unique.

Axiom typeCharCmpTyFamNameKey : Unique.Unique.

Axiom typeLeqCharTyFamNameKey : Unique.Unique.

Axiom typeNatDivTyFamNameKey : Unique.Unique.

Axiom typeNatModTyFamNameKey : Unique.Unique.

Axiom typeNatLogTyFamNameKey : Unique.Unique.

Axiom typeConsSymbolTyFamNameKey : Unique.Unique.

Axiom typeUnconsSymbolTyFamNameKey : Unique.Unique.

Axiom typeCharToNatTyFamNameKey : Unique.Unique.

Axiom typeNatToCharTyFamNameKey : Unique.Unique.

Axiom constPtrTyConKey : Unique.Unique.

Axiom jsvalTyConKey : Unique.Unique.

Axiom exceptionContextTyConKey : Unique.Unique.

Axiom charDataConKey : Unique.Unique.

Axiom consDataConKey : Unique.Unique.

Axiom doubleDataConKey : Unique.Unique.

Axiom falseDataConKey : Unique.Unique.

Axiom floatDataConKey : Unique.Unique.

Axiom intDataConKey : Unique.Unique.

Axiom nothingDataConKey : Unique.Unique.

Axiom justDataConKey : Unique.Unique.

Axiom eqDataConKey : Unique.Unique.

Axiom nilDataConKey : Unique.Unique.

Axiom ratioDataConKey : Unique.Unique.

Axiom word8DataConKey : Unique.Unique.

Axiom stableNameDataConKey : Unique.Unique.

Axiom trueDataConKey : Unique.Unique.

Axiom wordDataConKey : Unique.Unique.

Axiom ioDataConKey : Unique.Unique.

Axiom heqDataConKey : Unique.Unique.

Axiom crossDataConKey : Unique.Unique.

Axiom inlDataConKey : Unique.Unique.

Axiom inrDataConKey : Unique.Unique.

Axiom genUnitDataConKey : Unique.Unique.

Axiom leftDataConKey : Unique.Unique.

Axiom rightDataConKey : Unique.Unique.

Axiom ordLTDataConKey : Unique.Unique.

Axiom ordEQDataConKey : Unique.Unique.

Axiom ordGTDataConKey : Unique.Unique.

Axiom mkDictDataConKey : Unique.Unique.

Axiom coercibleDataConKey : Unique.Unique.

Axiom staticPtrDataConKey : Unique.Unique.

Axiom staticPtrInfoDataConKey : Unique.Unique.

Axiom fingerprintDataConKey : Unique.Unique.

Axiom srcLocDataConKey : Unique.Unique.

Axiom trTyConDataConKey : Unique.Unique.

Axiom trModuleDataConKey : Unique.Unique.

Axiom trNameSDataConKey : Unique.Unique.

Axiom trNameDDataConKey : Unique.Unique.

Axiom trGhcPrimModuleKey : Unique.Unique.

Axiom typeErrorTextDataConKey : Unique.Unique.

Axiom typeErrorAppendDataConKey : Unique.Unique.

Axiom typeErrorVAppendDataConKey : Unique.Unique.

Axiom typeErrorShowTypeDataConKey : Unique.Unique.

Axiom prefixIDataConKey : Unique.Unique.

Axiom infixIDataConKey : Unique.Unique.

Axiom leftAssociativeDataConKey : Unique.Unique.

Axiom rightAssociativeDataConKey : Unique.Unique.

Axiom notAssociativeDataConKey : Unique.Unique.

Axiom sourceUnpackDataConKey : Unique.Unique.

Axiom sourceNoUnpackDataConKey : Unique.Unique.

Axiom noSourceUnpackednessDataConKey : Unique.Unique.

Axiom sourceLazyDataConKey : Unique.Unique.

Axiom sourceStrictDataConKey : Unique.Unique.

Axiom noSourceStrictnessDataConKey : Unique.Unique.

Axiom decidedLazyDataConKey : Unique.Unique.

Axiom decidedStrictDataConKey : Unique.Unique.

Axiom decidedUnpackDataConKey : Unique.Unique.

Axiom metaDataDataConKey : Unique.Unique.

Axiom metaConsDataConKey : Unique.Unique.

Axiom metaSelDataConKey : Unique.Unique.

Axiom vecRepDataConKey : Unique.Unique.

Axiom tupleRepDataConKey : Unique.Unique.

Axiom sumRepDataConKey : Unique.Unique.

Axiom boxedRepDataConKey : Unique.Unique.

Axiom boxedRepDataConTyConKey : Unique.Unique.

Axiom tupleRepDataConTyConKey : Unique.Unique.

(* Skipping definition `PrelNames.runtimeRepSimpleDataConKeys' *)

Axiom liftedDataConKey : Unique.Unique.

Axiom unliftedDataConKey : Unique.Unique.

Axiom vecCountDataConKeys : list Unique.Unique.

Axiom vecElemDataConKeys : list Unique.Unique.

Axiom kindRepTyConAppDataConKey : Unique.Unique.

Axiom kindRepVarDataConKey : Unique.Unique.

Axiom kindRepAppDataConKey : Unique.Unique.

Axiom kindRepFunDataConKey : Unique.Unique.

Axiom kindRepTYPEDataConKey : Unique.Unique.

Axiom kindRepTypeLitSDataConKey : Unique.Unique.

Axiom kindRepTypeLitDDataConKey : Unique.Unique.

Axiom typeLitSymbolDataConKey : Unique.Unique.

Axiom typeLitNatDataConKey : Unique.Unique.

Axiom typeLitCharDataConKey : Unique.Unique.

Axiom unsafeReflDataConKey : Unique.Unique.

Axiom oneDataConKey : Unique.Unique.

Axiom manyDataConKey : Unique.Unique.

Axiom integerISDataConKey : Unique.Unique.

Axiom integerINDataConKey : Unique.Unique.

Axiom integerIPDataConKey : Unique.Unique.

Axiom naturalNSDataConKey : Unique.Unique.

Axiom naturalNBDataConKey : Unique.Unique.

Axiom wildCardKey : Unique.Unique.

Axiom absentErrorIdKey : Unique.Unique.

Axiom absentConstraintErrorIdKey : Unique.Unique.

Axiom augmentIdKey : Unique.Unique.

Axiom appendIdKey : Unique.Unique.

Axiom buildIdKey : Unique.Unique.

Axiom foldrIdKey : Unique.Unique.

Axiom recSelErrorIdKey : Unique.Unique.

Axiom seqIdKey : Unique.Unique.

Axiom absentSumFieldErrorIdKey : Unique.Unique.

Axiom eqStringIdKey : Unique.Unique.

Axiom noMethodBindingErrorIdKey : Unique.Unique.

Axiom nonExhaustiveGuardsErrorIdKey : Unique.Unique.

Axiom impossibleErrorIdKey : Unique.Unique.

Axiom impossibleConstraintErrorIdKey : Unique.Unique.

Axiom patErrorIdKey : Unique.Unique.

Axiom realWorldPrimIdKey : Unique.Unique.

Axiom recConErrorIdKey : Unique.Unique.

Axiom unpackCStringUtf8IdKey : Unique.Unique.

Axiom unpackCStringAppendUtf8IdKey : Unique.Unique.

Axiom unpackCStringFoldrUtf8IdKey : Unique.Unique.

Axiom unpackCStringIdKey : Unique.Unique.

Axiom unpackCStringAppendIdKey : Unique.Unique.

Axiom unpackCStringFoldrIdKey : Unique.Unique.

Axiom voidPrimIdKey : Unique.Unique.

Axiom typeErrorIdKey : Unique.Unique.

Axiom divIntIdKey : Unique.Unique.

Axiom modIntIdKey : Unique.Unique.

Axiom cstringLengthIdKey : Unique.Unique.

Axiom concatIdKey : Unique.Unique.

Axiom filterIdKey : Unique.Unique.

Axiom zipIdKey : Unique.Unique.

Axiom bindIOIdKey : Unique.Unique.

Axiom returnIOIdKey : Unique.Unique.

Axiom newStablePtrIdKey : Unique.Unique.

Axiom printIdKey : Unique.Unique.

Axiom failIOIdKey : Unique.Unique.

Axiom nullAddrIdKey : Unique.Unique.

Axiom voidArgIdKey : Unique.Unique.

Axiom otherwiseIdKey : Unique.Unique.

Axiom assertIdKey : Unique.Unique.

Axiom leftSectionKey : Unique.Unique.

Axiom rightSectionKey : Unique.Unique.

Axiom rootMainKey : Unique.Unique.

Axiom runMainKey : Unique.Unique.

Axiom thenIOIdKey : Unique.Unique.

Axiom lazyIdKey : Unique.Unique.

Axiom assertErrorIdKey : Unique.Unique.

Axiom oneShotKey : Unique.Unique.

Axiom runRWKey : Unique.Unique.

Axiom traceKey : Unique.Unique.

Axiom nospecIdKey : Unique.Unique.

Axiom inlineIdKey : Unique.Unique.

Axiom mapIdKey : Unique.Unique.

Axiom dollarIdKey : Unique.Unique.

Axiom coercionTokenIdKey : Unique.Unique.

Axiom considerAccessibleIdKey : Unique.Unique.

Axiom noinlineIdKey : Unique.Unique.

Axiom noinlineConstraintIdKey : Unique.Unique.

Axiom integerToFloatIdKey : Unique.Unique.

Axiom integerToDoubleIdKey : Unique.Unique.

Axiom naturalToFloatIdKey : Unique.Unique.

Axiom naturalToDoubleIdKey : Unique.Unique.

Axiom rationalToFloatIdKey : Unique.Unique.

Axiom rationalToDoubleIdKey : Unique.Unique.

Axiom coerceKey : Unique.Unique.

Axiom unboundKey : Unique.Unique.

Axiom fromIntegerClassOpKey : Unique.Unique.

Axiom minusClassOpKey : Unique.Unique.

Axiom fromRationalClassOpKey : Unique.Unique.

Axiom enumFromClassOpKey : Unique.Unique.

Axiom enumFromThenClassOpKey : Unique.Unique.

Axiom enumFromToClassOpKey : Unique.Unique.

Axiom enumFromThenToClassOpKey : Unique.Unique.

Axiom eqClassOpKey : Unique.Unique.

Axiom geClassOpKey : Unique.Unique.

Axiom negateClassOpKey : Unique.Unique.

Axiom bindMClassOpKey : Unique.Unique.

Axiom thenMClassOpKey : Unique.Unique.

Axiom fmapClassOpKey : Unique.Unique.

Axiom returnMClassOpKey : Unique.Unique.

Axiom mfixIdKey : Unique.Unique.

Axiom failMClassOpKey : Unique.Unique.

Axiom fromLabelClassOpKey : Unique.Unique.

Axiom arrAIdKey : Unique.Unique.

Axiom composeAIdKey : Unique.Unique.

Axiom firstAIdKey : Unique.Unique.

Axiom appAIdKey : Unique.Unique.

Axiom choiceAIdKey : Unique.Unique.

Axiom loopAIdKey : Unique.Unique.

Axiom fromStringClassOpKey : Unique.Unique.

Axiom toAnnotationWrapperIdKey : Unique.Unique.

Axiom fromIntegralIdKey : Unique.Unique.

Axiom realToFracIdKey : Unique.Unique.

Axiom toIntegerClassOpKey : Unique.Unique.

Axiom toRationalClassOpKey : Unique.Unique.

Axiom guardMIdKey : Unique.Unique.

Axiom liftMIdKey : Unique.Unique.

Axiom mzipIdKey : Unique.Unique.

Axiom ghciStepIoMClassOpKey : Unique.Unique.

Axiom isListClassKey : Unique.Unique.

Axiom fromListClassOpKey : Unique.Unique.

Axiom fromListNClassOpKey : Unique.Unique.

Axiom toListClassOpKey : Unique.Unique.

Axiom proxyHashKey : Unique.Unique.

Axiom mkTyConKey : Unique.Unique.

Axiom mkTrTypeKey : Unique.Unique.

Axiom mkTrConKey : Unique.Unique.

Axiom mkTrAppCheckedKey : Unique.Unique.

Axiom typeNatTypeRepKey : Unique.Unique.

Axiom typeSymbolTypeRepKey : Unique.Unique.

Axiom typeCharTypeRepKey : Unique.Unique.

Axiom typeRepIdKey : Unique.Unique.

Axiom mkTrFunKey : Unique.Unique.

Axiom starKindRepKey : Unique.Unique.

Axiom starArrStarKindRepKey : Unique.Unique.

Axiom starArrStarArrStarKindRepKey : Unique.Unique.

Axiom constraintKindRepKey : Unique.Unique.

Axiom toDynIdKey : Unique.Unique.

Axiom eqSCSelIdKey : Unique.Unique.

Axiom heqSCSelIdKey : Unique.Unique.

Axiom coercibleSCSelIdKey : Unique.Unique.

Axiom sappendClassOpKey : Unique.Unique.

Axiom memptyClassOpKey : Unique.Unique.

Axiom mappendClassOpKey : Unique.Unique.

Axiom mconcatClassOpKey : Unique.Unique.

Axiom emptyCallStackKey : Unique.Unique.

Axiom pushCallStackKey : Unique.Unique.

Axiom fromStaticPtrClassOpKey : Unique.Unique.

Axiom makeStaticKey : Unique.Unique.

Axiom emptyExceptionContextKey : Unique.Unique.

Axiom unsafeEqualityProofIdKey : Unique.Unique.

Axiom unsafeCoercePrimIdKey : Unique.Unique.

Axiom getFieldClassOpKey : Unique.Unique.

Axiom setFieldClassOpKey : Unique.Unique.

Axiom unsatisfiableIdNameKey : Unique.Unique.

Axiom integerFromNaturalIdKey : Unique.Unique.

Axiom integerToNaturalClampIdKey : Unique.Unique.

Axiom integerToNaturalThrowIdKey : Unique.Unique.

Axiom integerToNaturalIdKey : Unique.Unique.

Axiom integerToWordIdKey : Unique.Unique.

Axiom integerToIntIdKey : Unique.Unique.

Axiom integerToWord64IdKey : Unique.Unique.

Axiom integerToInt64IdKey : Unique.Unique.

Axiom integerAddIdKey : Unique.Unique.

Axiom integerMulIdKey : Unique.Unique.

Axiom integerSubIdKey : Unique.Unique.

Axiom integerNegateIdKey : Unique.Unique.

Axiom integerAbsIdKey : Unique.Unique.

Axiom integerPopCountIdKey : Unique.Unique.

Axiom integerQuotIdKey : Unique.Unique.

Axiom integerRemIdKey : Unique.Unique.

Axiom integerDivIdKey : Unique.Unique.

Axiom integerModIdKey : Unique.Unique.

Axiom integerDivModIdKey : Unique.Unique.

Axiom integerQuotRemIdKey : Unique.Unique.

Axiom integerEncodeFloatIdKey : Unique.Unique.

Axiom integerEncodeDoubleIdKey : Unique.Unique.

Axiom integerGcdIdKey : Unique.Unique.

Axiom integerLcmIdKey : Unique.Unique.

Axiom integerAndIdKey : Unique.Unique.

Axiom integerOrIdKey : Unique.Unique.

Axiom integerXorIdKey : Unique.Unique.

Axiom integerComplementIdKey : Unique.Unique.

Axiom integerBitIdKey : Unique.Unique.

Axiom integerTestBitIdKey : Unique.Unique.

Axiom integerShiftLIdKey : Unique.Unique.

Axiom integerShiftRIdKey : Unique.Unique.

Axiom integerFromWordIdKey : Unique.Unique.

Axiom integerFromWord64IdKey : Unique.Unique.

Axiom integerFromInt64IdKey : Unique.Unique.

Axiom naturalToWordIdKey : Unique.Unique.

Axiom naturalPopCountIdKey : Unique.Unique.

Axiom naturalShiftRIdKey : Unique.Unique.

Axiom naturalShiftLIdKey : Unique.Unique.

Axiom naturalAddIdKey : Unique.Unique.

Axiom naturalSubIdKey : Unique.Unique.

Axiom naturalSubThrowIdKey : Unique.Unique.

Axiom naturalSubUnsafeIdKey : Unique.Unique.

Axiom naturalMulIdKey : Unique.Unique.

Axiom naturalQuotRemIdKey : Unique.Unique.

Axiom naturalQuotIdKey : Unique.Unique.

Axiom naturalRemIdKey : Unique.Unique.

Axiom naturalAndIdKey : Unique.Unique.

Axiom naturalAndNotIdKey : Unique.Unique.

Axiom naturalOrIdKey : Unique.Unique.

Axiom naturalXorIdKey : Unique.Unique.

Axiom naturalTestBitIdKey : Unique.Unique.

Axiom naturalBitIdKey : Unique.Unique.

Axiom naturalGcdIdKey : Unique.Unique.

Axiom naturalLcmIdKey : Unique.Unique.

Axiom naturalLog2IdKey : Unique.Unique.

Axiom naturalLogBaseWordIdKey : Unique.Unique.

Axiom naturalLogBaseIdKey : Unique.Unique.

Axiom naturalPowModIdKey : Unique.Unique.

Axiom naturalSizeInBaseIdKey : Unique.Unique.

Axiom bignatEqIdKey : Unique.Unique.

Axiom bignatCompareIdKey : Unique.Unique.

Axiom bignatCompareWordIdKey : Unique.Unique.

Axiom mkRationalBase2IdKey : Unique.Unique.

Axiom mkRationalBase10IdKey : Unique.Unique.

Axiom numericClassKeys : list Unique.Unique.

Axiom fractionalClassKeys : list Unique.Unique.

Axiom standardClassKeys : list Unique.Unique.

Axiom derivableClassKeys : list Unique.Unique.

Axiom interactiveClassNames : list Name.Name.

Axiom interactiveClassKeys : list Unique.Unique.

Axiom nameRdrName : Name.Name -> RdrName.

(* External variables:
     Type bool list FastString.FastString GHC.Base.String
     GHC.Data.List.Infinite.Infinite Module.Module Module.ModuleName Name.Name
     OccName.NameSpace OccName.OccName SrcLoc.SrcSpan Unique.Unique
*)
