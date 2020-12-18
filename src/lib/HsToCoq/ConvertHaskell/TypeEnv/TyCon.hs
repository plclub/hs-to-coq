{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, RecordWildCards #-}

module HsToCoq.ConvertHaskell.TypeEnv.TyCon (
  tyConsOfModDetails,
  convertedTyConBinds,
  convertedTyConResType,
  applyTyConArgs) where
import Data.Generics (Data)
import Data.Map as M hiding (filter)

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Edits.Types

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type

import HscTypes
import TyCon
import TyCoRep
import Name (getName)

data ConvertedTyCon =
  ConvertedTyCon { convertedTyConBinds :: [Binder]
                 , convertedTyConResType :: Term
                 }
  deriving (Eq, Ord, Show, Data)

type ConvertedTyConEnv = M.Map Qualid ConvertedTyCon

tyConsOfModDetails :: ConversionMonad r m => ModDetails -> m ConvertedTyConEnv
tyConsOfModDetails mod = M.fromList <$> mapM convertTycon (typeEnvTyCons $ md_types mod)

convertTycon :: ConversionMonad r m => TyCon -> m (Qualid, ConvertedTyCon)
convertTycon tc = do
  convertedTyConBinds <- mapM convertTyConBinder (tyConBinders tc)
  convertedTyConResType <- convertKind $ tyConResKind tc
  tyConName <- convertTyCon tc  -- [convertTyCon] from [HsToCoq.ConvertHaskell.Type]
  pure (tyConName, ConvertedTyCon{..})

convertTyConBinder :: ConversionMonad r m => TyConBinder -> m Binder
convertTyConBinder b = do
#if __GLASGOW_HASKELL__ >= 808
  tk <- convertKind $ binderType b
#else
  tk <- convertKind $ binderKind b
#endif
  let ex = if isVisibleTyConBinder b then Explicit else Implicit
  if isNamedTyConBinder b then do
    tv <- Ident <$> var TypeNS (getName $ binderVar b)
    pure $ mkTypedBinder ex tv tk
  else pure $ Generalized ex tk

applyTyConArgs :: ConvertedTyCon -> [Term] -> [Term]
applyTyConArgs ConvertedTyCon{..} t =
  snd <$> filter (\(b, _) -> binderExplicitness b == Explicit) (zip convertedTyConBinds t)
