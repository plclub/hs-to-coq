{-# LANGUAGE CPP #-}
module HsToCoq.Util.GHC (
  defaultRunGhc,
  ghcPpr
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import Control.Monad

import GHC
import GHC.Paths
#if __GLASGOW_HASKELL__ <= 900
import DynFlags (showPpr, defaultFatalMessager, defaultFlushOut)
import Outputable (Outputable)
#else
import GHC.Plugins (Outputable, showPpr, defaultFatalMessager, defaultFlushOut)
#endif

ghcPpr :: (GhcMonad m, Outputable a) => a -> m Text
ghcPpr x = fmap T.pack $ showPpr <$> getSessionDynFlags <*> pure x

defaultRunGhc :: Ghc () -> IO ()
defaultRunGhc ghc = defaultErrorHandler defaultFatalMessager defaultFlushOut
                  . runGhc (Just libdir)
                  . handleSourceError printException $ do
                      void $ setSessionDynFlags =<< getSessionDynFlags
                      ghc
