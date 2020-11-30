{-# LANGUAGE DeriveDataTypeable, RecordWildCards, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.TypeEnv.TyCl(
  ConvertedTyClEnv,
  ConvertedTyCl,
  convertedTyClName,
  convertedTyClTyVars,
  convertedTyClMethods,
  convertTyClEnv,
  convertedTyCl,
  convertTyCl,
  unpeelTyClVars
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

import HsToCoq.ConvertHaskell.TypeEnv.Id

data ConvertedTyCl =
  ConvertedTyCl { convertedTyClName :: Qualid 
                  -- A map from type variable name to the variable's kind, we
                  -- don't use [Binder] here because we don't know the
                  -- explicitness
                , convertedTyClTyVars  :: [(Qualid, Term)]
                , convertedTyClMethods :: [(Qualid, Term)]
                }
  deriving (Eq, Ord, Show, Data)

type ConvertedTyClEnv = M.Map Qualid ConvertedTyCl

convertedTyCl :: Qualid -> ConvertedTyClEnv -> Maybe ConvertedTyCl
convertedTyCl = M.lookup

isTyClConstraint :: Binder -> Qualid -> Bool
isTyClConstraint (Generalized _ex t) className = go t className
  where go :: Term -> Qualid -> Bool
        go (App t _args) className = go t className
        go (Qualid q) className = q == className
        go _t _className = False
isTyClConstraint _binder _className = False

unpeelTyClVars :: Term -> Qualid -> Term
unpeelTyClVars (Forall bs t) className
  | any (`isTyClConstraint` className) bs = t
  | otherwise                             = unpeelTyClVars t className
unpeelTyClVars t _className = t

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
  convertedTyClTyVars <- mapM convertTyClVar $ classTyVars cl
  convertedTyClMethods <- mapM convertId $ classMethods cl
  pure ConvertedTyCl{..}
