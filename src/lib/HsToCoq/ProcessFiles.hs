{-# LANGUAGE CPP, FlexibleContexts, LambdaCase, ScopedTypeVariables #-}

#include "ghc-compat.h"

module HsToCoq.ProcessFiles (ProcessingMode(..), processFiles) where

import Control.Lens

import Data.Foldable
import Control.Monad
import Control.Monad.IO.Class

import qualified Data.Set as S

import System.Directory

import GHC
import GHC.Hs

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.Edits.Types (skippedModules, skippedClasses)
import HsToCoq.Util.GHC.Module (moduleNameText)
import HsToCoq.Coq.Gallina.Util (qualidToIdent)
import HsToCoq.Util.GHC.Deriving

--------------------------------------------------------------------------------

data ProcessingMode = Recursive | NonRecursive
                    deriving (Eq, Ord, Enum, Bounded, Show, Read)

#if __GLASGOW_HASKELL__ >= 910
-- | Remove all standalone deriving declarations from a parsed module.
-- This prevents GHC's typechecker from failing on derivations for types
-- from skipped modules. The derivations we DO want are handled separately
-- by 'addDerivedInstances'.
stripStandaloneDerivDecls :: ParsedModule -> ParsedModule
stripStandaloneDerivDecls pm =
  let L loc hsmod = pm_parsed_source pm
      decls' = filter (not . isDerivDecl . unLoc) (hsmodDecls hsmod)
      hsmod' = hsmod { hsmodDecls = decls' }
  in pm { pm_parsed_source = L loc hsmod' }

-- | Test whether a parsed declaration is a standalone @deriving@ declaration.
isDerivDecl :: HsDecl GhcPs -> Bool
isDerivDecl (DerivD _ _) = True
isDerivDecl _            = False
#endif

-- | Load and typecheck Haskell source files via the GHC API.
--
-- Uses a two-pass error-tolerant strategy (GHC >= 9.10): if the initial
-- 'load' fails — typically because standalone @deriving instance@
-- declarations reference types from skipped modules — we fall back to
-- parsing each module individually, stripping standalone deriving decls,
-- typechecking, and then re-deriving the wanted instances via
-- 'addDerivedInstances'.
processFiles :: GlobalMonad r m => ProcessingMode -> [FilePath] -> m (Maybe [TypecheckedModule])
processFiles mode files = do
  initForDeriving
  -- Build skip info from edits so addDerivedInstances can filter out
  -- instances involving skipped modules or type classes.
  skipMods <- view (edits.skippedModules)
  skipCls  <- view (edits.skippedClasses)
  let skipInfo = DerivSkipInfo
        { dsi_skippedModules = S.map moduleNameText skipMods
        , dsi_skippedClasses = S.map qualidToIdent skipCls
        }
  traverse_ (addTarget <=< (guessTarget ?? Nothing ?? Nothing)) files
  load LoadAllTargets >>= \case
    Succeeded -> Just <$> do
      filterModules <- case mode of
        Recursive    -> pure pure
        NonRecursive -> do
          let canonicalizePaths trav = traverse (liftIO . canonicalizePath) trav
          filePaths <- S.fromList . map Just <$> canonicalizePaths files
          let moduleFile = canonicalizePaths . ml_hs_file . ms_location
          pure . filterM $ fmap (`S.member` filePaths) . moduleFile
      traverse (addDerivedInstances skipInfo <=< typecheckModule <=< parseModule)
        =<< skipModulesBy ms_mod_name
        =<< filterModules . mgModSummaries
        =<< getModuleGraph
    Failed ->
#if __GLASGOW_HASKELL__ >= 910
      -- When load fails (e.g. due to standalone deriving errors for types
      -- from skipped modules), try again with standalone deriving declarations
      -- stripped from the parsed AST. The module graph is still available even
      -- when load fails.
      do
        liftIO $ putStrLn "hs-to-coq: initial load failed, attempting recovery by stripping standalone deriving declarations"
        filterModules <- case mode of
          Recursive    -> pure pure
          NonRecursive -> do
            let canonicalizePaths trav = traverse (liftIO . canonicalizePath) trav
            filePaths <- S.fromList . map Just <$> canonicalizePaths files
            let moduleFile = canonicalizePaths . ml_hs_file . ms_location
            pure . filterM $ fmap (`S.member` filePaths) . moduleFile
        modSummaries <- skipModulesBy ms_mod_name
                          =<< filterModules . mgModSummaries
                          =<< getModuleGraph
        if null modSummaries
          then do
            liftIO $ putStrLn "hs-to-coq: error: no modules found in module graph after filtering"
            pure Nothing
          else do
            -- Process each module individually: parse, strip standalone derivs,
            -- typecheck, then re-derive. Modules that still fail are skipped
            -- (handleSourceError in processWithStrippedDerivs returns Nothing).
            results <- traverse (processWithStrippedDerivs skipInfo) modSummaries
            let successes = [tcm | Just tcm <- results]
            if null successes
              then do
                liftIO $ putStrLn "hs-to-coq: error: all modules failed to typecheck"
                pure Nothing
              else pure (Just successes)
#else
      do
        liftIO $ putStrLn "hs-to-coq: error: GHC load failed (standalone deriving recovery requires GHC >= 9.10)"
        pure Nothing
#endif

#if __GLASGOW_HASKELL__ >= 910
-- | Parse a module, strip standalone deriving declarations, typecheck,
-- then add back derived instances via addDerivedInstances.
processWithStrippedDerivs :: GlobalMonad r m => DerivSkipInfo -> ModSummary -> m (Maybe TypecheckedModule)
processWithStrippedDerivs skipInfo ms =
  handleSourceError (\e -> do
    liftIO $ putStrLn $ "hs-to-coq: warning: failed to typecheck "
      ++ moduleNameString (moduleName (ms_mod ms))
      ++ " even after stripping standalone deriving declarations:"
    liftIO $ putStrLn $ "  " ++ show e
    return Nothing) $ do
    liftIO $ putStrLn $ "hs-to-coq: retrying " ++ moduleNameString (moduleName (ms_mod ms))
      ++ " with standalone deriving declarations stripped"
    pm <- parseModule ms
    let pm' = stripStandaloneDerivDecls pm
    tcm <- typecheckModule pm'
    Just <$> addDerivedInstances skipInfo tcm
#endif
