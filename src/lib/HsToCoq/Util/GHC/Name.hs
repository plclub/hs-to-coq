{-# LANGUAGE CPP, ViewPatterns #-}
module HsToCoq.Util.GHC.Name (module Name, isOperator, freshInternalName) where

import Control.Monad.IO.Class
import Data.IORef
import System.IO.Unsafe

import HsToCoq.ConvertHaskell.InfixNames
import qualified Data.Text as T

#if __GLASGOW_HASKELL__ >= 900
import GHC.Types.Name as Name
import GHC.Plugins
#else
import Module
import OccName
import Name
import Unique
import UniqSupply
import SrcLoc
#endif

isOperator :: Name -> Bool
isOperator = isSymOcc . nameOccName
{-# INLINABLE isOperator #-}

-- Module-local
freshInternalNameUniqSupply :: IORef UniqSupply
freshInternalNameUniqSupply = unsafePerformIO $ newIORef =<< mkSplitUniqSupply '殊'
{-# NOINLINE freshInternalNameUniqSupply #-}

-- Module-local
freshInternalNameNewUnique :: MonadIO m => m Unique
freshInternalNameNewUnique = liftIO $ do
  supply <- readIORef freshInternalNameUniqSupply
  let (u, supply') = takeUniqFromSupply supply
  u <$ writeIORef freshInternalNameUniqSupply supply'

freshInternalName :: MonadIO m => String -> m Name
freshInternalName var
    | Just (T.unpack -> mn, T.unpack -> base) <- splitModule (T.pack var) = do
      let mod = mkModule
-- GHC 9.x renamed stringToUnitId to stringToUnit
#if __GLASGOW_HASKELL__ >= 900
            (stringToUnit "hs-to-coq")
#else
            (stringToUnitId "hs-to-coq")
#endif
            (mkModuleName mn)
      u <- freshInternalNameNewUnique
      pure $ mkExternalName u mod (mkVarOcc base) noSrcSpan
    | otherwise = do
      u <- freshInternalNameNewUnique
      pure $ mkInternalName u (mkVarOcc var) noSrcSpan
