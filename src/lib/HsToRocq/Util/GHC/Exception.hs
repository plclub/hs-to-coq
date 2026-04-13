{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- GHC >= 9.0 removed the ExceptionMonad class from its API in favor of the
-- standard 'exceptions' library (Control.Monad.Catch). The orphan ExceptionMonad
-- instances below are only needed for older GHC; GHC 9.x provides them upstream.
-- gWithFile uses MC.bracket (via CPP alias gbracket) on GHC >= 9.0.
module HsToRocq.Util.GHC.Exception (module Exception, gWithFile) where

import Control.Monad.IO.Class
import System.IO

import qualified Control.Monad.Trans.Identity      as I
import qualified Control.Monad.Trans.Maybe         as M
import qualified Control.Monad.Trans.Except        as E
import qualified Control.Monad.Trans.Reader        as R
import qualified Control.Monad.Trans.Writer.Strict as WS
import qualified Control.Monad.Trans.Writer.Lazy   as WL
import qualified Control.Monad.Trans.State.Strict  as SS
import qualified Control.Monad.Trans.State.Lazy    as SL
import qualified Control.Monad.Trans.RWS.Strict    as RWSS
import qualified Control.Monad.Trans.RWS.Lazy      as RWSL
import qualified Control.Monad.Catch as MC

#if __GLASGOW_HASKELL__ >= 900
import GHC.Utils.Exception as Exception
#define gbracket MC.bracket
#else
import Exception

instance ExceptionMonad m => ExceptionMonad (I.IdentityT m) where
  gcatch  = I.liftCatch gcatch
  gmask f = I.IdentityT . gmask $ I.runIdentityT . f . I.mapIdentityT

instance ExceptionMonad m => ExceptionMonad (M.MaybeT m) where
  gcatch  = M.liftCatch gcatch
  gmask f = M.MaybeT . gmask $ M.runMaybeT . f . M.mapMaybeT

-- I think this is OK
instance ExceptionMonad m => ExceptionMonad (E.ExceptT e m) where
  m `gcatch` h  = E.ExceptT $ E.runExceptT m `gcatch` (E.runExceptT . h)
  gmask f = E.ExceptT . gmask $ E.runExceptT . f . E.mapExceptT

instance ExceptionMonad m => ExceptionMonad (R.ReaderT r m) where
  gcatch  = R.liftCatch gcatch
  gmask f = R.ReaderT $ \env -> gmask $ flip R.runReaderT env . f . R.mapReaderT

instance (ExceptionMonad m, Monoid w) => ExceptionMonad (WS.WriterT w m) where
  gcatch = WS.liftCatch gcatch
  gmask f = WS.WriterT . gmask $ WS.runWriterT . f . WS.mapWriterT

instance (ExceptionMonad m, Monoid w) => ExceptionMonad (WL.WriterT w m) where
  gcatch  = WL.liftCatch gcatch
  gmask f = WL.WriterT . gmask $ WL.runWriterT . f . WL.mapWriterT

instance ExceptionMonad m => ExceptionMonad (SS.StateT s m) where
  gcatch = SS.liftCatch gcatch
  gmask f = SS.StateT $ \s -> gmask $ flip SS.runStateT s . f . SS.mapStateT

instance ExceptionMonad m => ExceptionMonad (SL.StateT s m) where
  gcatch  = SL.liftCatch gcatch
  gmask f = SL.StateT $ \s -> gmask $ flip SL.runStateT s . f . SL.mapStateT

instance (ExceptionMonad m, Monoid w) => ExceptionMonad (RWSS.RWST r w s m) where
  gcatch = RWSS.liftCatch gcatch
  gmask f = RWSS.RWST $ \r s -> gmask $ (\m -> RWSS.runRWST m r s) . f . RWSS.mapRWST

instance (ExceptionMonad m, Monoid w) => ExceptionMonad (RWSL.RWST r w s m) where
  gcatch  = RWSL.liftCatch gcatch
  gmask f = RWSL.RWST $ \r s -> gmask $ (\m -> RWSL.runRWST m r s) . f . RWSL.mapRWST
#endif

-- Other MTL transformers will be added as necessary

gWithFile :: ExceptionMonad m => FilePath -> IOMode -> (Handle -> m r) -> m r
gWithFile file mode = gbracket (liftIO $ openFile file mode) (liftIO . hClose)
