{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections, LambdaCase, FlexibleContexts, FlexibleInstances, ScopedTypeVariables #-}

#include "ghc-compat.h"

module HsToCoq.ConvertHaskell.Sigs (
  convertLSigs, convertSigs, lookupSig,
  HsSignature(..), collectSigs, collectSigsWithErrors, convertSignatures, convertSignature,
  ) where

import Prelude hiding (Num)

import Control.Lens

import Data.Maybe
import Data.Semigroup (Semigroup(..))
import Data.Traversable (for)
import qualified Data.Text as T

import Control.Monad.Reader
import Control.Monad.Except

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import GHC hiding (Name)
import qualified GHC

import HsToCoq.Util.GHC
#if __GLASGOW_HASKELL__ >= 806
import HsToCoq.Util.GHC.HsTypes (noExtCon)
#endif
import HsToCoq.Coq.Gallina

import HsToCoq.Edits.Types
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.HsType

-- From Haskell declaration
data HsSignature = HsSignature { hsSigType   :: LHsSigType GhcRn
                               , hsSigFixity :: Maybe Fixity }


collectSigs :: [Sig GhcRn] -> Either String (Map GHC.Name (Either String HsSignature))
collectSigs sigs = do
  let asType x = ([x], [])
      --asFixity = (S.singleton mname, [], ) . pure

      asTypes lnames sigTy = pure (map ((, asType sigTy) . unLoc) lnames)
      --asFixities lnames fixity = list . map (, asFixity fixity) . filter isRdrOperator $ map unLoc lnames

  multimap :: M.Map GHC.Name ([LHsSigType GhcRn],[Fixity])
   <- fmap (M.fromListWith (<>) . concat) . for sigs $ \case
    TypeSig NOEXTP lnames (HsWC wcs hsib)
      | null wcs  -> asTypes lnames hsib
      | otherwise -> throwError "type wildcards found"
#if __GLASGOW_HASKELL__ >= 806
    TypeSig NOEXTP _ (XHsWildCardBndrs v) -> noExtCon v
    XSig v -> noExtCon v
#endif
    ClassOpSig NOEXTP False lnames sigTy -> asTypes lnames sigTy
    ClassOpSig NOEXTP True _ _ -> pure [] -- Ignore default methods signatures
    FixSig NOEXTP _            -> pure []
    InlineSig NOEXTP _ _       -> pure []
    SpecSig   NOEXTP _ _ _     -> pure []
    SpecInstSig NOEXTP _ _     -> pure []
    MinimalSig  NOEXTP _ _     -> pure []
    SCCFunSig{}          -> pure []
    CompleteMatchSig{}   -> pure []
    PatSynSig NOEXTP _ _ -> pure []
    IdSig     NOEXTP _   -> throwError "generated-code signatures"

  pure $ flip M.mapWithKey multimap $ \_key info@(_,_) -> case info of
         ([ty],  [fixity])  -> Right $ HsSignature ty (Just fixity)
         ([ty],  [])        -> Right $ HsSignature ty Nothing
         ([],    [_fixity]) -> Left "a fixity annotation without a type signature"
         ([],    _)         -> Left "multiple fixity annotations without a type signature"
         (_,     [])        -> Left "multiple type signatures for the same identifier"
         (_,     _)         -> Left "multiple type and fixity signatures for the same identifier"

collectSigsWithErrors :: ConversionMonad r m => [Sig GhcRn] -> m (Map GHC.Name HsSignature)
collectSigsWithErrors =
  either convUnsupported' (M.traverseWithKey multiplesError) . collectSigs
  where multiplesError name (Left err) = do
          nameStr <- T.unpack <$> ghcPpr name
          convUnsupported' $ err ++ " for `" ++ nameStr ++ "'"
        multiplesError _ (Right sig) =
          pure sig

convertSignature :: ConversionMonad r m => Qualid -> UnusedTyVarMode -> HsSignature -> m Signature
convertSignature coqName utvm (HsSignature sigTy _hsFix) =
  withCurrentDefinition coqName (Signature <$> convertLHsSigType utvm sigTy <*> pure Nothing)

-- Incorporates @set type …@ edits ('replacedTypes') for all bindings that
-- /already had/ a type signature; use 'lookupSig' to get the rest.
convertSignatures :: ConversionMonad r m => Map GHC.Name HsSignature -> m (Map Qualid Signature)
convertSignatures = fmap (M.fromList . catMaybes) . traverse conv . M.toList where
  conv (hsName, hsSig) = do
    coqName <- var ExprNS hsName
    view (edits.replacedTypes.at coqName) >>= \case
      Just (Just ty) -> pure $ Just (coqName, Signature ty Nothing)
      Just Nothing   -> pure Nothing
      Nothing -> do
        utvm <- unusedTyVarModeFor coqName
        Just . (coqName,) <$> convertSignature coqName utvm hsSig

-- Incorporates @set type …@ edits ('replacedTypes') for all bindings that
-- /already had/ a type signature; use 'lookupSig' to get the rest.
convertSigs :: ConversionMonad r m => [Sig GhcRn] -> m (Map Qualid Signature)
convertSigs = convertSignatures <=< collectSigsWithErrors

-- Incorporates @set type …@ edits ('replacedTypes') for all bindings that
-- /already had/ a type signature; use 'lookupSig' to get the rest.
convertLSigs :: ConversionMonad r m => [LSig GhcRn] -> m (Map Qualid Signature)
convertLSigs = convertSigs . map unLoc

-- Falls back on the @set type …@ edits ('replacedTypes') if there's no
-- 'Signature' in the map.
lookupSig :: (MonadReader r m, HasEdits r Edits) => Qualid -> Map Qualid Signature -> m (Maybe Signature)
lookupSig qid sigs = case M.lookup qid sigs of
                       sig@Just{} -> pure sig
                       Nothing    -> views (edits.replacedTypes.at qid) (fmap (Signature ?? Nothing) . join)
