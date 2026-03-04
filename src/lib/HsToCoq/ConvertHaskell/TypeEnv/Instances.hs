{-# LANGUAGE CPP, DeriveDataTypeable, RecordWildCards, FlexibleContexts, OverloadedStrings #-}
#include "ghc-compat.h"

module HsToCoq.ConvertHaskell.TypeEnv.Instances where

import Data.Foldable
import Data.Generics (Data)
import Data.Map as M
import Data.Maybe

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.Pretty
import HsToCoq.Edits.Types

import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.TypeEnv.TyCl
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables

#if __GLASGOW_HASKELL__ >= 900
import GHC.Unit.Module.ModDetails
import GHC.Core.InstEnv
import GHC.Core.RoughMap (RoughMatchTc(..))
import GHC.Types.Var
#else
import HscTypes
import InstEnv
import Var
#endif

data ConvertedInstance =
  ConvertedInstance { convertedInstanceClass :: ConvertedTyCl
                    , convertedInstanceBinds :: [Binder]
                    , convertedInstanceTops  :: [Qualid]
                    , convertedInstanceSubst :: M.Map Qualid Term
                    , convertedInstanceTypes :: [Term]
                    }
  deriving (Eq, Ord, Show, Data)

type ConvertedInstanceEnv = [ConvertedInstance]

instancesOfModDetails :: ConversionMonad r m => ModDetails -> m ConvertedInstanceEnv
instancesOfModDetails mod = mapM convertInstance GHC_900($ instEnvElts) $ md_insts mod

convertInstance :: ConversionMonad r m => ClsInst -> m ConvertedInstance
convertInstance inst = do
  let (binds, cls, tms) = instanceHead inst
  convertedInstanceClass <- convertTyCl cls
  convertedInstanceBinds <- mapM tyVarToBinder binds
  convertedInstanceTypes <- mapM convertType tms
  let convertedInstanceSubst = M.fromList $ zip
        (fst <$> convertedTyClTyVars convertedInstanceClass) convertedInstanceTypes
  convertedInstanceTops <- mapM (var TypeNS)
#if __GLASGOW_HASKELL__ >= 900
                             [n | RM_KnownTc n <- is_tcs inst]
#else
                             (catMaybes $ is_tcs inst)
#endif
  pure ConvertedInstance{..}
  where tyVarToBinder tv = do
          name <- var TypeNS  $ varName tv
          typ  <- convertType $ varType tv
          pure $ mkTypedBinder Implicit (Ident name) typ

lookupInstance :: ConversionMonad r m => Term -> Qualid -> ConvertedInstanceEnv -> m ConvertedInstance
lookupInstance instTy className env = case find matchInstance env of
  Just t -> pure t
  _      -> throwProgramError $ "The class " <> showP className <> " of " <> showP instTy <> " is not found"
  where matchInstance i = elem instTy (convertedInstanceTypes i) &&
          convertedTyClName (convertedInstanceClass i) == className
