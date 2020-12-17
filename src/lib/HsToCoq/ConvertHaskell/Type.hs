{-# LANGUAGE CPP, FlexibleContexts, OverloadedStrings #-}

#include "ghc-compat.h"

module HsToCoq.ConvertHaskell.Type (
  convertType,
  convertKind,
  convertTyCon,
  convertPredType) where

import Data.List.NonEmpty (NonEmpty(..))
import Control.Lens

#if __GLASGOW_HASKELL__ >= 808
import Var
#endif
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

convertTyConApp :: ConversionMonad r m => Bool -> TyCon -> [KindOrType] -> Qualid -> m Term
convertTyConApp b tc ts ctc = do
  let cond = if b then const True else fst
  let rest = repeat True
  ts' <- mapM (convertType . snd) $ filter cond $
    zip ((isVisibleTyConBinder <$> tyConBinders tc) <> rest) ts
  case ts' of
    ct : cts' -> pure $ App (Qualid ctc) $ PosArg <$> (ct :| cts')
    _         -> pure $ Qualid ctc

convertType' :: ConversionMonad r m => Bool -> Type -> m Term
convertType' _ (TyVarTy tv) = Qualid <$> var TypeNS (getName tv)
convertType' b (AppTy ty1 ty2) = App1 <$> convertType' b ty1 <*> convertType' b ty2
convertType' _ (TyConApp tc []) = Qualid <$> convertTyCon tc
convertType' b (TyConApp tc ts@(_:_)) = do
  convertedTc <- convertTyCon tc
  case convertedTc of
    (Qualified m t) | m == "GHC.Prim" && t == "TYPE"
                      -> pure $ Qualid (Bare "Type")
                    | m == "GHC.Tuple" && length ts > 1 ->
                      if (t == "pair_type" || t == "op_Z2T__") || (t == "triple_type" && length ts > 2) ||
                         (t == "quad_type" && length ts > 3) || (t == "quint_type" && length ts > 4) ||
                         (t == "sext_type" && length ts > 5) || (t == "sept_type" && length ts > 6)
                      then (`InScope` "type") . foldl1 (mkInfix ?? "*") <$> traverse (convertType' b) ts
                      else convertTyConApp b tc ts convertedTc
    _ -> convertTyConApp b tc ts convertedTc
convertType' b (ForAllTy tv ty) = do
  convertedTv <- convertTyVarBinder Coq.Implicit tv
  convertedTy <- convertType' b ty
  pure $ Forall (convertedTv :| []) convertedTy
#if __GLASGOW_HASKELL__ >= 810
convertType' b (FunTy InvisArg ty1 ty2)  = do
  cons <- convertPredType ty1
  Forall (Generalized Coq.Implicit cons :| []) <$> convertType' b ty2
convertType' b (FunTy VisArg ty1 ty2) = Arrow <$> convertType' b ty1 <*> convertType' b ty2
#else
convertType' b (FunTy ty1 ty2) | isPredTy ty1 = do
                                   cons <- convertPredType ty1
                                   Forall (Generalized Coq.Implicit cons :| []) <$> convertType' b ty2
                               | otherwise    = Arrow <$> convertType' b ty1 <*> convertType' b ty2
#endif                                   
convertType' _ (LitTy tl) = case tl of
  NumTyLit int -> either convUnsupported' (pure . Num) $ convertInteger "type-level integers" int
  StrTyLit str -> pure $ convertFastString str
convertType' _ (CastTy _ty _coercion) = convUnsupported' "Kind cast"
convertType' _ (CoercionTy _coercion) = convUnsupported' "Injection of a Coercion into a type"
  
convertType :: ConversionMonad r m => Type -> m Term
convertType = convertType' False

convertKind :: ConversionMonad r m => Kind -> m Term
convertKind = convertType' False

convertPredType :: ConversionMonad r m => Kind -> m Term
convertPredType = convertType' True

convertTyCon :: ConversionMonad r m => TyCon -> m Qualid
convertTyCon tc = var TypeNS $ getName tc

convertTyVarBinder :: ConversionMonad r m => Explicitness -> TyVarBinder -> m Binder
convertTyVarBinder ex bndr = do
  tv <- Ident <$> var TypeNS (getName $ binderVar bndr)
#if __GLASGOW_HASKELL__ >= 808
  tk <- convertKind $ binderType bndr
#else
  tk <- convertKind $ binderKind bndr
#endif
  pure $ mkBinders ex (tv :| []) tk
