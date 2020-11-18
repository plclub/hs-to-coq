{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.TypeEnv.Id(
  ConvertedIdEnv,
  ConvertedId,
  convertedIdType,
  convertIdEnv,
  convertId
  ) where

import qualified Data.Map as M
import Data.Generics (Data)

import HscTypes
import Var

import HsToCoq.Coq.Gallina
import HsToCoq.Edits.Types

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type

newtype ConvertedId = ConvertedId Term
  deriving (Eq, Ord, Show, Data)

type ConvertedIdEnv = M.Map Qualid ConvertedId

convertedIdType :: Qualid -> ConvertedIdEnv -> Maybe Term
convertedIdType q env = do
  id <- M.lookup q env
  case id of
    ConvertedId t -> pure t

convertIdEnv :: ConversionMonad r m => ModDetails -> m ConvertedIdEnv
convertIdEnv mod = do
  let typeEnv = md_types mod
  let ids = typeEnvIds typeEnv
  M.fromList <$> mapM convertId ids

convertId :: ConversionMonad r m => Id -> m (Qualid, ConvertedId)
convertId id = do
  name <- var ExprNS $ varName id
  typ  <- convertType $ varType id
  pure (name, ConvertedId typ)
  
