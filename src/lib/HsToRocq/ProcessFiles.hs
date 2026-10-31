{-# LANGUAGE CPP, FlexibleContexts, LambdaCase, ScopedTypeVariables #-}

#include "ghc-compat.h"

module HsToRocq.ProcessFiles (ProcessingMode(..), processFiles) where

import Control.Lens hiding (Strict)

import Data.Foldable
import Data.List (find)
import Data.Maybe (fromMaybe)
import Control.Monad
import Control.Monad.IO.Class

import qualified Data.Set as S

import System.Directory
import System.IO (hPutStrLn, stderr)

import GHC
import GHC.Hs
#if __GLASGOW_HASKELL__ >= 910
import GHC.Data.Bag (bagToList)
import GHC.Types.Error (getMessages, errMsgSpan, errMsgDiagnostic)
import GHC.Utils.Outputable (ppr, showSDocUnsafe)
import GHC.Types.SourceError (srcErrorMessages)
import qualified Control.Exception as E
import HsToRocq.Util.GHC.StockDeriving
#endif

import HsToRocq.ConvertHaskell.Monad
import HsToRocq.Util.GHC.Deriving

--------------------------------------------------------------------------------

data ProcessingMode = Recursive | NonRecursive
                    deriving (Eq, Ord, Enum, Bounded, Show, Read)

-- | Load and typecheck Haskell source files via the GHC API.
processFiles :: GlobalMonad r m => ProcessingMode -> [FilePath] -> m (Maybe [TypecheckedModule])
processFiles mode files = do
  initForDeriving
  traverse_ (addTarget <=< (guessTarget ?? Nothing ?? Nothing)) files
  filterModules <- case mode of
    Recursive    -> pure pure
    NonRecursive -> do
      let canonicalizePaths trav = traverse (liftIO . canonicalizePath) trav {- HLINT ignore "Eta reduce" -}
      filePaths <- S.fromList . map Just <$> canonicalizePaths files
      let moduleFile = canonicalizePaths . ml_hs_file . ms_location
      pure . filterM $ fmap (`S.member` filePaths) . moduleFile
  load LoadAllTargets >>= \case
    Succeeded -> Just <$> do
      traverse (processModule <=< parseModule)
        =<< skipModulesBy ms_mod_name
        =<< filterModules . mgModSummaries
        =<< getModuleGraph
    Failed ->
#if __GLASGOW_HASKELL__ >= 910
      do
        modSummaries <- skipModulesBy ms_mod_name
                          =<< filterModules . mgModSummaries
                          =<< getModuleGraph
        if null modSummaries
          then do
            liftIO $ putStrLn "hs-to-rocq: error: no modules found in module graph after filtering"
            pure Nothing
          else do
            Just <$> traverse (recoverDeriving <=< parseModule) modSummaries
#else
      do
        liftIO $ putStrLn "hs-to-rocq: error: GHC load failed (standalone deriving recovery requires GHC >= 9.10)"
        pure Nothing
#endif
  where
    processModule pm =
#if __GLASGOW_HASKELL__ >= 910
      handleSourceError (const (recoverDeriving pm)) $
#endif
        addDerivedInstances =<< typecheckModule pm

#if __GLASGOW_HASKELL__ >= 910
-- Retry the original declarations, removing only a diagnosed failed request.
-- The final typecheck supplies authoritative metadata and also checks uses of
-- the accepted instances in the rest of the module.
recoverDeriving :: GlobalMonad r m => ParsedModule -> m TypecheckedModule
recoverDeriving pm = do
  (renamedEnv, group) <- renameForDeriving pm
  retry renamedEnv group (derivingRequests group) [] pm
  where
    retry renamedEnv group requests expanded parsed =
      handleSourceError (recover renamedEnv group requests expanded parsed) $ do
        checked <- typecheckModule parsed
        verifyStockExpansions expanded checked
        addDerivedInstances checked

    recover renamedEnv group requests expanded parsed err = do
      let messages = bagToList (getMessages (srcErrorMessages err))
          matches span actual = sameDerivingSpan span actual || actual `isSubspanOf` span
          failed = find (\(span, _) -> any (matches span . errMsgSpan) messages) requests
      case failed of
        Nothing -> liftIO $ E.throwIO err
        Just (span, requestType) -> do
          let diagnostic = find (matches span . errMsgSpan) messages
              ty = fromMaybe requestType (diagnostic >>= failedDerivationType . errMsgDiagnostic)
          skipped <- derivationIsSkipped (ms_mod_name (pm_mod_summary pm))
            ty
          let discard failure = do
                policy <- view leniency
                let description = showSDocUnsafe (ppr span) ++ ": deriving "
                      ++ showSDocUnsafe (ppr ty) ++ " failed:\n" ++ show failure
                unless skipped $ case policy of
                  Strict -> throwProgramError description
                  Permissive -> liftIO $ hPutStrLn stderr $ "hs-to-rocq: warning: " ++ description
                retry renamedEnv group (filter (not . sameDerivingSpan span . fst) requests)
                  (filter (not . sameDerivingSpan span . stockExpansionSpan) expanded)
                  (removeDerivingRequest span parsed)
              standalone = find (sameDerivingSpan span . getLocA) (hs_derivds group)
          if skipped || any (sameDerivingSpan span . stockExpansionSpan) expanded then discard err else
            case standalone of
              Nothing -> discard err
              Just request -> do
                result <- handleSourceError (pure . Left) $
                  Right <$> expandStockDeriving parsed renamedEnv group request
                case result of
                  Left failure -> discard failure
                  Right Nothing -> discard err
                  Right (Just (parsed', expansion)) ->
                    retry renamedEnv group requests (expansion : expanded) parsed'
#endif
