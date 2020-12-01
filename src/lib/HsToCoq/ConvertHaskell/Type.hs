{-# LANGUAGE CPP, FlexibleContexts, OverloadedStrings #-}

#include "ghc-compat.h"

module HsToCoq.ConvertHaskell.Type (convertType) where

import Data.List.NonEmpty (NonEmpty(..))
import Control.Lens

import TyCoRep
import TyCon
import Type (isPredTy)
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
convertType (TyConApp tc []) = Qualid <$> convertTyCon tc
convertType (TyConApp tc ts@(t:ts')) = do
  convertedTc <- convertTyCon tc
  case convertedTc of
    -- many hacks ahead
    (Qualified m t) | m == "GHC.Prim" && t == "TYPE"
                      -> pure $ Qualid (Bare "Type")
                    | m == "GHC.Tuple" && t == "op_Z2T__"
                      -> (`InScope` "type") . foldl1 (mkInfix ?? "*") <$> traverse convertType ts
                    | m == "GHC.Prim" && t == "arrow"
                      -> do
                        cts <- mapM convertType $ drop 1 ts'
                        case cts of
                          ct : cts' -> pure $ App (Qualid convertedTc) $ PosArg <$> (ct :| cts')
                          _         -> pure $ Qualid convertedTc
    _ -> do
      ct  <- convertType t
      cts <- mapM convertType ts'
      pure $ App (Qualid convertedTc) $ PosArg <$> (ct :| cts)
convertType (ForAllTy tv ty) = do
  convertedTv <- convertTyVarBinder Coq.Implicit tv
  convertedTy <- convertType ty
  pure $ Forall (convertedTv :| []) convertedTy
convertType (FunTy ty1 ty2) | isPredTy ty1 = do
                                cons <- convertType ty1
                                Forall (Generalized Coq.Implicit cons :| []) <$> convertType ty2
                            | otherwise    = Arrow <$> convertType ty1 <*> convertType ty2
convertType (LitTy tl) = case tl of
  NumTyLit int -> either convUnsupported' (pure . Num) $ convertInteger "type-level integers" int
  StrTyLit str -> pure $ convertFastString str
convertType (CastTy _ty _coercion) = convUnsupported' "Kind cast"
convertType (CoercionTy _coercion) = convUnsupported' "Injection of a Coercion into a type"
  
convertKind :: ConversionMonad r m => Kind -> m Term
convertKind = convertType

convertTyCon :: ConversionMonad r m => TyCon -> m Qualid
convertTyCon tc = var TypeNS $ getName tc

convertTyVarBinder :: ConversionMonad r m => Explicitness -> TyVarBinder -> m Binder
convertTyVarBinder ex bndr = do
  tv <- Ident <$> var TypeNS (getName $ binderVar bndr)
  tk <- convertKind $ binderKind bndr
  pure $ mkBinders ex (tv :| []) tk
