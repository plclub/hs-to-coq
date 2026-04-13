{-# LANGUAGE CPP #-}
module HsToRocq.Util.TempFiles (
  gWithTempFile, gWithSystemTempFile,
  gIgnoringIOErrors
  ) where

import Control.Monad.IO.Class

import System.IO
import System.Directory

import GHC
#if __GLASGOW_HASKELL__ >= 900
import GHC.Utils.Exception
import qualified Control.Monad.Catch as MC
#define gcatch MC.catch
#define gbracket MC.bracket
#else
import Exception
#endif

-- Based on "System.IO.Temp", from the @temporary@ package

gIgnoringIOErrors :: ExceptionMonad m => m () -> m ()
gIgnoringIOErrors =
  (`gcatch` (const (pure ()) :: Applicative f => IOError -> f ()))

gWithTempFile :: ExceptionMonad m
              => FilePath -> String -> (FilePath -> Handle -> m a) -> m a
gWithTempFile tmpDir template f =
  gbracket (liftIO $ openTempFile tmpDir template)
           (\(tempF, tempH) -> liftIO (hClose tempH)
                            *> gIgnoringIOErrors (liftIO $ removeFile tempF))
           (uncurry f)

gWithSystemTempFile :: ExceptionMonad m
                    => String -> (FilePath -> Handle -> m a) -> m a
gWithSystemTempFile template f =
  liftIO getTemporaryDirectory >>= \tmpDir -> gWithTempFile tmpDir template f
