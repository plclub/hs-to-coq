{-# LANGUAGE FunctionalDependencies,
             FlexibleInstances, UndecidableInstances,
             FlexibleContexts,
             LambdaCase #-}

module Control.Monad.Activatable.Class (
  -- * The 'MonadActivatable' class
  MonadActivatable(..),
  switching', activateWith, activate,
  -- * Activation-related types
  ActivationError(..), Switched(..)
) where

import HsToCoq.Util.Functor
import Control.Monad.Error.Class
import Control.Monad.Trans

import Data.Foldable

import qualified Control.Monad.Trans.Activatable   as A
import qualified Control.Monad.Trans.Identity      as I
import qualified Control.Monad.Trans.Reader        as R
import qualified Control.Monad.Trans.Writer.Strict as WS
import qualified Control.Monad.Trans.Writer.Lazy   as WL
import qualified Control.Monad.Trans.State.Strict  as SS
import qualified Control.Monad.Trans.State.Lazy    as SL
import qualified Control.Monad.Trans.RWS.Strict    as RWSS
import qualified Control.Monad.Trans.RWS.Lazy      as RWSL

import Control.Monad.Trans.Activatable hiding (tryActivate, switching, switching')

-- |The idea is thus:
--
-- @
--                        /\
--                       /  \
--                      /    \  /\
-- ____________________/      \/  \__________________
--        |               |      |           |
--      basic       activated  residual    basic
-- @
--
-- Or, in code:
--
-- @
--     >>> basic         = pure 'b'
--     >>> activated     = pure ('A','X')
--     >>> cmd           = switching' basic activated
--     >>> activatedList = finalizeActivatableT @(Either _) (const Nothing) . sequence
--     >>> activatedList [cmd, cmd, cmd, cmd, cmd]
--     Right "bbbbb"
--     >>> activatedList [cmd, activateWith Just *> cmd, cmd, cmd, cmd]
--     Right "bAXbb"
--     >>> activatedList [cmd, cmd, cmd, activateWith Just *> cmd, cmd]
--     Right "bbbAX"
--     >>> activatedList [cmd, cmd, cmd, activateWith Just *> cmd, cmd]
--     Right "bbbAX"
--     >>> activatedList [cmd, activateWith Just *> cmd, cmd, activateWith Just *> cmd, cmd]
--     Right "bAXAX"
--     >>> activatedList [cmd, activateWith Just *> activateWith Just *> cmd, cmd, cmd, cmd]
--     Left (Just DoubleActivation)
--     >>> activatedList [cmd, activateWith Just *> cmd, activateWith Just *> cmd, cmd, cmd]
--     Left (Just EarlyActivation)
--     >>> activatedList [cmd, cmd, cmd, cmd, activateWith Just *> cmd]
--     Left Nothing
-- @
class Monad m => MonadActivatable x m | m -> x where
  tryActivate :: m (Maybe ActivationError)
  switching   :: m b -> m (a, x) -> m (Switched b a x)

switching' :: MonadActivatable a m => m a -> m (a, a) -> m a
switching' basic activated = switching basic activated <&> \case
                               Basic     b -> b
                               Activated a -> a
                               Residual  x -> x

activateWith :: MonadActivatable x m => (ActivationError -> m ()) -> m ()
activateWith handleAE = traverse_ handleAE =<< tryActivate

activate :: (MonadError ActivationError m, MonadActivatable x m) => m ()
activate = activateWith throwError

--------------------------------------------------------------------------------
-- Instances

-- See "Instance helpers" below

instance Monad m => MonadActivatable x (ActivatableT x m) where
  tryActivate = A.tryActivate
  switching   = A.switching

instance MonadActivatable x m => MonadActivatable x (I.IdentityT m) where
  tryActivate                                           = lift tryActivate
  switching (I.IdentityT basic) (I.IdentityT activated) =
    I.IdentityT $ switching basic activated

instance MonadActivatable x m => MonadActivatable x (R.ReaderT r m) where
  tryActivate                                       = lift tryActivate
  switching (R.ReaderT basic) (R.ReaderT activated) =
    R.ReaderT $ switching <$> basic <*> activated

instance (MonadActivatable x m, Monoid w) => MonadActivatable x (WS.WriterT w m) where
  tryActivate                                         = lift tryActivate
  switching (WS.WriterT basic) (WS.WriterT activated) =
    WS.WriterT $ liftSwitching (switchPairStrict mempty) pushPairStrict basic activated

instance (MonadActivatable x m, Monoid w) => MonadActivatable x (WL.WriterT w m) where
  tryActivate                                         = lift tryActivate
  switching (WL.WriterT basic) (WL.WriterT activated) =
    WL.WriterT $ liftSwitching (switchPairLazy mempty) pushPairLazy basic activated

instance MonadActivatable x m => MonadActivatable x (SS.StateT s m) where
  tryActivate                                       = lift tryActivate
  switching (SS.StateT basic) (SS.StateT activated) =
    SS.StateT $ \s -> liftSwitching (switchPairStrict s) pushPairStrict (basic s) (activated s)

instance MonadActivatable x m => MonadActivatable x (SL.StateT s m) where
  tryActivate                                       = lift tryActivate
  switching (SL.StateT basic) (SL.StateT activated) =
    SL.StateT $ \s -> liftSwitching (switchPairLazy s) pushPairLazy (basic s) (activated s)

instance (MonadActivatable x m, Monoid w) => MonadActivatable x (RWSS.RWST r w s m) where
  tryActivate                                       = lift tryActivate
  switching (RWSS.RWST basic) (RWSS.RWST activated) =
    RWSS.RWST $ \r s -> liftSwitching (switchTripleStrict s mempty) pushTripleStrict (basic r s) (activated r s)

instance (MonadActivatable x m, Monoid w) => MonadActivatable x (RWSL.RWST r w s m) where
  tryActivate                                       = lift tryActivate
  switching (RWSL.RWST basic) (RWSL.RWST activated) =
    RWSL.RWST $ \r s -> liftSwitching (switchTripleLazy s mempty) pushTripleLazy (basic r s) (activated r s)

--------------------------------------------------------------------------------
-- Instance helpers (module-local)

pushPairLazy :: ((a,x),o) -> ((a,o),x)
pushPairLazy ~((a,x),o) = ((a,o),x)
{-# INLINE pushPairLazy #-}

switchPairLazy :: o -> Switched (b,o) (a,o) x -> (Switched b a x, o)
switchPairLazy o' = \case
  Basic     ~(b,o) -> (Basic     b, o)
  Activated ~(a,o) -> (Activated a, o)
  Residual  x      -> (Residual  x, o')
{-# INLINE switchPairLazy #-}

pushPairStrict :: ((a,x),o) -> ((a,o),x)
pushPairStrict ((a,x),o) = ((a,o),x)
{-# INLINE pushPairStrict #-}

switchPairStrict :: o -> Switched (b,o) (a,o) x -> (Switched b a x, o)
switchPairStrict o_strict = \case
  Basic     (b,o) -> (Basic     b, o)
  Activated (a,o) -> (Activated a, o)
  Residual  x     -> (Residual  x, o_strict)
{-# INLINE switchPairStrict #-}

pushTripleLazy :: ((a,x),s,w) -> ((a,s,w),x)
pushTripleLazy ~((a,x),s,w) = ((a,s,w),x)
{-# INLINE pushTripleLazy #-}

switchTripleLazy :: s -> w -> Switched (b,s,w) (a,s,w) x -> (Switched b a x, s, w)
switchTripleLazy s wempty = \case
  Basic     ~(b,s',w) -> (Basic     b, s', w)
  Activated ~(a,s',w) -> (Activated a, s', w)
  Residual  x         -> (Residual  x, s,  wempty)
{-# INLINE switchTripleLazy #-}

pushTripleStrict :: ((a,x),s,w) -> ((a,s,w),x)
pushTripleStrict ((a,x),s,w) = ((a,s,w),x)
{-# INLINE pushTripleStrict #-}

switchTripleStrict :: s -> w -> Switched (b,s,w) (a,s,w) x -> (Switched b a x, s, w)
switchTripleStrict s wempty = \case
  Basic     (b,s',w) -> (Basic     b, s', w)
  Activated (a,s',w) -> (Activated a, s', w)
  Residual  x        -> (Residual  x, s,  wempty)
{-# INLINE switchTripleStrict #-}

liftSwitching :: MonadActivatable x m
               => (Switched b a x -> r) -> (a' -> (a, x))
               -> m b -> m a' -> m r
liftSwitching switch push basic activated = switch <$> switching basic (push <$> activated)
{-# INLINE liftSwitching #-}
