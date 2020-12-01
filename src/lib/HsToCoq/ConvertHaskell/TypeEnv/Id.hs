{-# LANGUAGE FlexibleContexts #-}

module HsToCoq.ConvertHaskell.TypeEnv.Id(
  ConvertedIdEnv,
  ConvertedId,
  convertedIdType,
  convertIdEnv,
  convertId,
  idEnvOfModDetails
  ) where

import qualified Data.Map as M

import HscTypes
import Var

import HsToCoq.Coq.Gallina
import HsToCoq.Edits.Types

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type

type ConvertedId = (Qualid, Term)

type ConvertedIdEnv = M.Map Qualid Term

convertedIdType :: Qualid -> ConvertedIdEnv -> Maybe Term
convertedIdType = M.lookup

idEnvOfModDetails :: ConversionMonad r m => ModDetails -> m ConvertedIdEnv
idEnvOfModDetails mod = M.fromList <$> mapM convertId (typeEnvIds $ md_types mod)

convertIdEnv :: ConversionMonad r m => [Id] -> m ConvertedIdEnv
convertIdEnv ids = M.fromList <$> mapM convertId ids

convertId :: ConversionMonad r m => Id -> m ConvertedId
convertId id = (,) <$> var ExprNS (varName id) <*> convertType (varType id)
