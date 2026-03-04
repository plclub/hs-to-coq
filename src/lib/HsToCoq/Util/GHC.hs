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
#if __GLASGOW_HASKELL__ >= 900
import GHC.Driver.Session
import GHC.Driver.Ppr
import GHC.Utils.Outputable
#else
import DynFlags
import Outputable
#endif

ghcPpr :: (GhcMonad m, Outputable a) => a -> m Text
ghcPpr x = fmap T.pack $ showPpr <$> getSessionDynFlags <*> pure x

defaultRunGhc :: Ghc () -> IO ()
defaultRunGhc ghc = defaultErrorHandler defaultFatalMessager defaultFlushOut
                  . runGhc (Just libdir)
                  . handleSourceError printException $ do
                      void $ setSessionDynFlags =<< getSessionDynFlags
                      ghc
