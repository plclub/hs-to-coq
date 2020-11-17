{-# LANGUAGE CPP, FlexibleContexts #-}

#include "ghc-compat.h"

module HsToCoq.ConvertHaskell.Type
  (convertType)
where

import Data.List.NonEmpty

import TyCoRep
import TyCon
import Name (getName)

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Edits.Types

import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Literals
import HsToCoq.ConvertHaskell.Monad

convertType :: ConversionMonad r m => Type -> m Term
convertType (TyVarTy tv) = Qualid <$> var TypeNS (getName tv)
convertType (AppTy ty1 ty2) = App1 <$> convertType ty1 <*> convertType ty2
convertType (TyConApp tc ts) = appList <$> convertTyCon tc <*> mapM (fmap PosArg . convertKindOrType) ts
convertType (ForAllTy tv ty) = do
  convertedTv <- convertTyVarBinder Coq.Implicit tv
  convertedTy <- convertType ty
  pure $ Forall (convertedTv :| []) convertedTy
convertType (FunTy ty1 ty2) = Arrow <$> convertType ty1 <*> convertType ty2
convertType (LitTy tl) = case tl of
  NumTyLit int -> either convUnsupported' (pure . Num) $ convertInteger "type-level integers" int
  StrTyLit str -> pure $ convertFastString str
convertType (CastTy _ty _coercion) = convUnsupported' "Kind cast"
convertType (CoercionTy _coercion) = convUnsupported' "Injection of a Coercion into a type"
  
convertKindOrType :: ConversionMonad r m => KindOrType -> m Term
convertKindOrType = convertType

convertKind :: ConversionMonad r m => Kind -> m Term
convertKind = convertType

convertTyCon :: ConversionMonad r m => TyCon -> m Term
convertTyCon tc = Qualid <$> var TypeNS (getName tc)

convertTyVarBinder :: ConversionMonad r m => Explicitness -> TyVarBinder -> m Binder
convertTyVarBinder ex bndr = do
  tv <- Ident <$> var TypeNS (getName $ binderVar bndr)
  tk <- convertKind $ binderKind bndr
  pure $ mkBinders ex (tv :| []) tk
