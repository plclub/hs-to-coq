{-# LANGUAGE DeriveDataTypeable, RecordWildCards, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.TypeEnv.TyCl(
  ConvertedTyClEnv,
  ConvertedTyCl,
  convertedTyClName,
  convertedTyClTyVars,
  convertTyClEnv,
  convertedTyCl,
  ) where

import qualified Data.Map as M
import Data.Generics (Data)

import Class
import HscTypes
import Var

import HsToCoq.Coq.Gallina
import HsToCoq.Edits.Types

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type

data ConvertedTyCl =
  ConvertedTyCl { convertedTyClName :: Qualid 
                  -- A map from type variable name to the variable's kind, we
                  -- don't use [Binder] here because we don't know the
                  -- explicitness
                , convertedTyClTyVars :: [(Qualid, Term)]
                }
  deriving (Eq, Ord, Show, Data)

type ConvertedTyClEnv = M.Map Qualid ConvertedTyCl

convertedTyCl :: Qualid -> ConvertedTyClEnv -> Maybe ConvertedTyCl
convertedTyCl = M.lookup

convertTyClEnv :: ConversionMonad r m => ModDetails -> m ConvertedTyClEnv
convertTyClEnv mod = do
  cls <- convertTyCls mod
  pure $ M.fromList $ fmap (\cl -> (convertedTyClName cl, cl)) cls

convertTyCls :: ConversionMonad r m => ModDetails -> m [ConvertedTyCl]
convertTyCls mod = do
  let typeEnv = md_types mod
  let classes = typeEnvClasses typeEnv
  mapM convertTyCl classes

convertTyClVar :: ConversionMonad r m => Var -> m (Qualid, Term)
convertTyClVar tv = do
  name <- var TypeNS $ tyVarName tv
  kind <- convertType $ tyVarKind tv
  pure (name, kind)
  
convertTyCl :: ConversionMonad r m => Class -> m ConvertedTyCl
convertTyCl cl = do
  convertedTyClName <- var TypeNS $ className cl
  convertedTyClTyVars <- mapM convertTyClVar (classTyVars cl)
  pure ConvertedTyCl{..}
