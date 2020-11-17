{-# LANGUAGE DeriveDataTypeable, RecordWildCards, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.TypeEnv.TyCl(
  ConvertedTyClEnv,
  convertTyClEnvs,
  ) where

import qualified Data.Map as M
import Data.Generics (Data)

import Class
import Name (getName)
import Var

import HsToCoq.Coq.Gallina
import HsToCoq.Edits.Types

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type

data ConvertedTyClEnv =
  ConvertedTyClEnv { convertedTyClName :: Qualid 
                     -- A map from type variable name to the variable's kind
                   , convertedTyClTyVars :: M.Map Qualid Term
                   }
  deriving (Eq, Ord, Show, Data)

convertTyClEnvs :: ConversionMonad r m => [Class] -> m [ConvertedTyClEnv]
convertTyClEnvs = mapM convertTyClEnv


convertTyClEnv :: ConversionMonad r m => Class -> m ConvertedTyClEnv
convertTyClEnv cl = do
  convertedTyClName <- var TypeNS $ className cl
  let vars = classTyVars cl
  names <- mapM (var TypeNS . getName) vars
  kinds <- mapM (convertType . tyVarKind) vars
  let convertedTyClTyVars = M.fromList (zip names kinds)
  pure ConvertedTyClEnv{..}
