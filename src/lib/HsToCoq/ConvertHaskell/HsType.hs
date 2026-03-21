{-# LANGUAGE CPP,
             LambdaCase,
             OverloadedStrings,
             FlexibleContexts, TypeApplications #-}

#include "ghc-compat.h"

module HsToCoq.ConvertHaskell.HsType
  (convertHsType,
   convertLHsType,
   convertLHsTyVarBndr,
   convertLHsTyVarBndrs,
#if __GLASGOW_HASKELL__ < 806
   getLHsTyVarName,
#endif
   convertLHsSigType,
   convertLHsSigTypeWithExcls,
   convertLHsSigWcType,
   convertHsSigType_)
where

import Control.Applicative (liftA2)
import Control.Lens

import Data.Functor (($>))
import Data.Traversable
import Data.List.NonEmpty (nonEmpty)
import Data.List ((\\))
import Data.Maybe (maybe)

import GHC hiding (Name)
import qualified GHC
import HsToCoq.Util.GHC.FastString

import HsToCoq.Util.GHC
import HsToCoq.Util.GHC.HsTypes
import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.FreeVars

import HsToCoq.Edits.Types
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Literals

--------------------------------------------------------------------------------

#if __GLASGOW_HASKELL__ < 806
-- In later versions of GHC. [HsTyVarBndr] is a [NamedThing], so we won't need
-- this function.
getLHsTyVarName :: LHsTyVarBndr _ GhcRn -> GHC.Name
getLHsTyVarName tv = case unLoc tv of
  UserTyVar   NOEXTP tv    -> unLoc tv
  KindedTyVar NOEXTP tv _k -> unLoc tv
#endif

-- GHC 9.0+ parameterized HsTyVarBndr by a flag type (specificity/required),
-- and added the flag as an extra constructor field (the GHC_900(_) argument).
-- We accept any flag and discard it since Coq has no specificity annotations.
convertLHsTyVarBndr :: LocalConvMonad r m => Explicitness -> LHsTyVarBndr flag GhcRn -> m Binder
convertLHsTyVarBndr ex tv = case unLoc tv of
  UserTyVar   NOEXTP GHC_900(_) tv   -> mkBinder ex . Ident <$> var TypeNS (unLoc tv)
  KindedTyVar NOEXTP GHC_900(_) tv k -> mkBinders ex <$> (pure . Ident <$> var TypeNS (unLoc tv)) <*> convertLHsType k
#if __GLASGOW_HASKELL__ >= 806
  XTyVarBndr v -> noExtCon v
#endif

convertLHsTyVarBndrs :: LocalConvMonad r m => Explicitness -> [LHsTyVarBndr flag GhcRn] -> m [Binder]
convertLHsTyVarBndrs ex = mapM (convertLHsTyVarBndr ex)

--------------------------------------------------------------------------------

convertHsType :: LocalConvMonad r m => HsType GhcRn -> m Term
-- GHC 9.0+ restructured HsForAllTy: the forall telescope is now an explicit
-- HsForAllInvis/HsForAllVis datatype instead of a flat list of binders.
-- We only handle invisible foralls (the normal Haskell 'forall a b.').
#if __GLASGOW_HASKELL__ >= 900
convertHsType (HsForAllTy NOEXTP (HsForAllInvis _ tvs) ty) = do
#elif __GLASGOW_HASKELL__ >= 810
convertHsType (HsForAllTy NOEXTP _ tvs ty) = do
#else
convertHsType (HsForAllTy NOEXTP tvs ty) = do
#endif
  explicitTVs <- convertLHsTyVarBndrs Coq.Implicit tvs
  tyBody      <- convertLHsType ty
  pure . maybe tyBody (Forall ?? tyBody) $ nonEmpty explicitTVs

convertHsType (HsQualTy NOEXTP lctx ty) = convertLHsType ty >>= convertContext lctx

convertHsType (HsTyVar NOEXTP _ (L _ tv)) =
  Qualid <$> var TypeNS tv

convertHsType (HsAppTy NOEXTP ty1 ty2) =
  App1 <$> convertLHsType ty1 <*> convertLHsType ty2

#if __GLASGOW_HASKELL__ >= 808
convertHsType HsAppKindTy{} = convUnsupported "type level type application"
#endif
#if __GLASGOW_HASKELL__ >= 806
convertHsType HsStarTy{} = pure (Sort Type)
convertHsType XHsType{} = convUnsupported "NewHsTypeX"
#else
-- TODO: This constructor handles '*' and deparses it later.  I'm just gonna
-- bank on never seeing any infix type things.
convertHsType (HsAppsTy tys) =
  let assertPrefix (L _ (HsAppPrefix lty)) = convertLHsType lty
      assertPrefix (L _ (HsAppInfix _))    = convUnsupported' "infix types in type application lists"
  in traverse assertPrefix tys >>= \case
       tyFun:tyArgs ->
         pure $ appList tyFun $ map PosArg tyArgs
       [] ->
         convUnsupported' "empty lists of type applications"

convertHsType (HsPArrTy _ty) =
  convUnsupported' "parallel arrays (`[:a:]')"

convertHsType (HsEqTy _ty1 _ty2) =
  convUnsupported' "type equality" -- FIXME

convertHsType (HsCoreTy _) =
  convUnsupported' "[internal] embedded core types"
#endif

-- GHC 9.0+ added a multiplicity argument to HsFunTy for linear types
-- (HsScaled wrapper). The GHC_900(_) macro absorbs this extra field;
-- we discard it since Coq has no linear types.
convertHsType (HsFunTy NOEXTP GHC_900(_) ty1 ty2) =
  Arrow <$> convertLHsType ty1 <*> convertLHsType ty2

convertHsType (HsListTy NOEXTP ty) =
  App1 (Var "list") <$> convertLHsType ty

convertHsType (HsTupleTy NOEXTP tupTy tys) = do
  case tupTy of
    HsUnboxedTuple           -> pure () -- TODO: Mark converted unboxed tuples specially?
    -- GHC 9.0+ merged HsBoxedTuple/HsConstraintTuple into this single constructor
    HsBoxedOrConstraintTuple -> pure () -- Sure, it's boxed, why not
#if __GLASGOW_HASKELL__ < 900
    HsBoxedTuple             -> pure ()
    HsConstraintTuple        -> convUnsupported' "constraint tuples"
#endif
  case tys of
    []   -> pure $ Var "unit"
    [ty] -> convertLHsType ty
    _    -> (`InScope` "type") . foldl1 (mkInfix ?? "*") <$> traverse convertLHsType tys

-- GHC 9.0+ added a promotedness flag to HsOpTy (GHC_900(_)); we discard it.
convertHsType (HsOpTy NOEXTP GHC_900(_) ty1 op ty2) =
  App2 <$> (Qualid <$> var TypeNS (unLoc op)) <*> convertLHsType ty1 <*> convertLHsType ty2   -- ???

convertHsType (HsParTy NOEXTP ty) =
  Parens <$> convertLHsType ty

convertHsType (HsIParamTy NOEXTP (L _ (HsIPName ip)) lty) = do
  isTyCallStack <- maybe (pure False) (fmap (== "CallStack") . ghcPpr) $ viewLHsTyVar lty
  if isTyCallStack && ip == fsLit "callStack"
    then pure "GHC.Stack.CallStack"
    else convUnsupported' "implicit parameter constraints"

convertHsType (HsKindSig NOEXTP ty k) =
  HasType <$> convertLHsType ty <*> convertLHsType k

convertHsType (HsSpliceTy _ _) =
  convUnsupported' "Template Haskell type splices"

convertHsType (HsDocTy NOEXTP ty _doc) =
  convertLHsType ty

convertHsType (HsBangTy NOEXTP _bang ty) =
  convertLHsType ty -- Strictness annotations are ignored

convertHsType (HsRecTy NOEXTP _fields) =
  convUnsupported' "record types" -- FIXME

convertHsType (HsExplicitListTy _ _ tys) =
  foldr (App2 $ Var "cons") (Var "nil") <$> traverse convertLHsType tys

convertHsType (HsExplicitTupleTy _PlaceHolders tys) =
  case tys of
    []   -> pure $ Var "tt"
    [ty] -> convertLHsType ty
    _    -> foldl1 (App2 $ Var "pair") <$> traverse convertLHsType tys

convertHsType (HsTyLit NOEXTP lit) =
  case lit of
    HsNumTy _src int -> either convUnsupported' (pure . Num) $ convertInteger "type-level integers" int
    HsStrTy _src str -> pure $ convertFastString str

convertHsType (HsWildCardTy _) =
  convUnsupported' "wildcards"

convertHsType (HsSumTy NOEXTP _) =
  convUnsupported' "sum types"

convertContext :: LocalConvMonad r m => LHsContext GhcRn -> Term -> m Term
convertContext lctx tyBody = do
  classes <- traverse (fmap (Generalized Coq.Implicit) . convertLHsType) (unLoc lctx)
  pure . maybe tyBody (Forall ?? tyBody) $ nonEmpty classes

--------------------------------------------------------------------------------

convertLHsType :: LocalConvMonad r m => LHsType GhcRn -> m Term
convertLHsType = convertHsType . unLoc

--------------------------------------------------------------------------------

convertLHsSigTypeWithExcls :: LocalConvMonad r m => UnusedTyVarMode -> LHsSigType GhcRn -> [Qualid] -> m Term
-- GHC 9.0+ replaced HsImplicitBndrs with HsSig/HsOuterSigTyVarBndrs.
-- HsOuterImplicit carries implicitly-bound type variables (the common case);
-- HsOuterExplicit carries an explicit forall's binders (e.g., standalone deriving).
#if __GLASGOW_HASKELL__ >= 900
convertLHsSigTypeWithExcls utvm (L _ (HsSig _ (HsOuterImplicit hs_itvs) hs_lty)) excls = do
#elif __GLASGOW_HASKELL__ >= 808
convertLHsSigTypeWithExcls utvm (HsIB hs_itvs hs_lty) excls = do
#elif __GLASGOW_HASKELL__ == 806
convertLHsSigTypeWithExcls utvm (HsIB (HsIBRn {hsib_vars=hs_itvs}) hs_lty) excls = do
#else
convertLHsSigTypeWithExcls utvm (HsIB hs_itvs hs_lty _) excls = do
#endif
  coq_itvs <- traverse (var TypeNS) hs_itvs
  coq_ty   <- convertLHsType hs_lty
  finishConvertHsSigTypeWithExcls utvm coq_itvs coq_ty excls
#if __GLASGOW_HASKELL__ >= 900
convertLHsSigTypeWithExcls utvm (L _ (HsSig _ (HsOuterExplicit _ hs_etvs) hs_lty)) excls = do
  let hs_itvs = map (hsTyVarName . unLoc) hs_etvs
  coq_itvs <- traverse (var TypeNS) hs_itvs
  coq_ty   <- convertLHsType hs_lty
  finishConvertHsSigTypeWithExcls utvm coq_itvs coq_ty excls
convertLHsSigTypeWithExcls _ (L _ (XHsSigType v)) _ = noExtCon v
#elif __GLASGOW_HASKELL__ >= 806
convertLHsSigTypeWithExcls _ (XHsImplicitBndrs v) _ = noExtCon v
#endif

finishConvertHsSigTypeWithExcls
  :: LocalConvMonad r m => UnusedTyVarMode -> [Qualid] -> Term -> [Qualid] -> m Term
finishConvertHsSigTypeWithExcls utvm coq_itvs coq_ty excls =
  let coq_tyVars = case utvm of
        PreserveUnusedTyVars -> coq_itvs
        DeleteUnusedTyVars   -> let fvs = getFreeVars coq_ty
                                in filter (`elem` fvs) coq_itvs
      coq_binders = mkBinder Coq.Implicit . Ident <$> coq_tyVars \\ excls
  in pure $ maybeForall coq_binders coq_ty

convertLHsSigType :: LocalConvMonad r m => UnusedTyVarMode -> LHsSigType GhcRn -> m Term
convertLHsSigType utvm sigTy = convertLHsSigTypeWithExcls utvm sigTy []

convertLHsSigWcType :: LocalConvMonad r m => UnusedTyVarMode -> LHsSigWcType GhcRn -> m Term
convertLHsSigWcType utvm (HsWC wcs hsib)
  | null wcs  = convertLHsSigType utvm hsib
  | otherwise = convUnsupported' "type wildcards"
#if __GLASGOW_HASKELL__ >= 806
convertLHsSigWcType _ (XHsWildCardBndrs v) = noExtCon v
#endif

--------------------------------------------------------------------------------

-- GHC 9.0+ renamed HsConDeclDetails to HsConDeclGADTDetails and split
-- GADT-style constructor details from H98-style (PrefixCon/InfixCon/RecCon
-- became PrefixConGADT/RecConGADT; InfixCon is not used for GADT syntax).
#if __GLASGOW_HASKELL__ >= 900
#define HsConDeclDetails HsConDeclGADTDetails
#endif

convertHsSigType_
  :: LocalConvMonad r m
  => UnusedTyVarMode
  -> LHsQTyVars GhcRn
  -> Maybe (LHsContext GhcRn)
  -> HsConDeclDetails GhcRn
  -> LHsType GhcRn
  -> [Qualid] -> m Term
convertHsSigType_ utvm HsQTvs { hsq_explicit = qvars } mcxt args resTy excls = do
  coq_itvs <- traverse (var TypeNS . binderName . unLoc) qvars
  coq_ty <- convertLHsType resTy >>= convertArgs args >>= maybe pure convertContext mcxt
  finishConvertHsSigTypeWithExcls utvm coq_itvs coq_ty excls
#if __GLASGOW_HASKELL__ >= 806
convertHsSigType_ _ (XLHsQTyVars v) _ _ _ _ = noExtCon v
#endif

convertArgs :: LocalConvMonad r m => HsConDeclDetails GhcRn -> Term -> m Term
-- GHC 9.0+ wraps constructor argument types in HsScaled for linear types;
-- hsScaledThing extracts the type, discarding the multiplicity annotation.
#if __GLASGOW_HASKELL__ >= 910
convertArgs (PrefixConGADT _ args_) ty = do
  let args = map hsScaledThing args_
#elif __GLASGOW_HASKELL__ >= 900
convertArgs (PrefixConGADT args_) ty = do
  let args = map hsScaledThing args_
#else
convertArgs (PrefixCon args) ty = do
#endif
  coq_args <- traverse convertLHsType args
  pure (foldr Arrow ty coq_args)
#if __GLASGOW_HASKELL__ >= 910
convertArgs (RecConGADT _ rec) ty = do
#elif __GLASGOW_HASKELL__ >= 900
convertArgs (RecConGADT rec _) ty = do
#else
convertArgs (RecCon rec) ty = do
#endif
  tyss <- for (unLoc rec) $ \lfield -> case unLoc lfield of
    -- We must be careful to copy the type when multiple fields @fds@ are under
    -- the same signature @t@
    ConDeclField { cd_fld_names = fds, cd_fld_type = t } -> do
      ty <- convertLHsType t
      pure (fds $> ty)
#if __GLASGOW_HASKELL__ >= 806
    XConDeclField v -> noExtCon v
#endif
  pure (foldr Arrow ty (concat tyss))
#if __GLASGOW_HASKELL__ < 900
convertArgs (InfixCon t1 t2) ty =
  liftA2 Arrow (convertLHsType t1) (liftA2 Arrow (convertLHsType t2) (pure ty))
#endif

binderName :: HsTyVarBndr flag GhcRn -> GHC.Name
binderName (UserTyVar NOEXTP GHC_900(_) lname) = unLoc lname
binderName (KindedTyVar NOEXTP GHC_900(_) lname _) = unLoc lname
#if __GLASGOW_HASKELL__ >= 806
binderName (XTyVarBndr v) = noExtCon v
#endif
