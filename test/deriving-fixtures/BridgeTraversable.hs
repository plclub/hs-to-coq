{-# LANGUAGE CPP, NoImplicitPrelude, StandaloneDeriving, DeriveTraversable, DerivingStrategies #-}
#ifdef BRIDGE_USER_CLASS
module BridgeUserClass where
#else
module GHC.Internal.Data.Traversable where
#endif

import GHC.Internal.Base (Functor(..), Applicative(..), Monad(..), Maybe(..), id, (.))
import GHC.Internal.Data.Foldable (Foldable(..))
#ifdef BRIDGE_HIDDEN_CONSTRUCTOR
import GHC.Internal.Data.Functor.Identity (Identity)
#else
import GHC.Internal.Data.Functor.Identity (Identity(..))
#endif
import GHC.Internal.Generics (V1)

class (Functor t, Foldable t) => Traversable t where
  {-# MINIMAL traverse | sequenceA #-}
  traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
  traverse f = sequenceA . fmap f
  sequenceA :: Applicative f => t (f a) -> f (t a)
  sequenceA = traverse id
#ifdef BRIDGE_METHOD_TYPE
  mapM :: Monad m => (a -> m a) -> t a -> m (t a)
#else
  mapM :: Monad m => (a -> m b) -> t a -> m (t b)
#endif
#ifndef BRIDGE_MISSING_DEFAULT
  mapM = traverse
#endif
  sequence :: Monad m => t (m a) -> m (t a)
  sequence = sequenceA
#ifdef BRIDGE_EXTRA_METHOD
  extraMethod :: t a -> t a
  extraMethod = id
#endif

data Wrap a = MkWrap (Identity a)
instance Functor Wrap where
  fmap f (MkWrap x) = MkWrap (fmap f x)
instance Foldable Wrap where
  foldMap f (MkWrap x) = foldMap f x

#ifdef BRIDGE_EXPLICIT_STOCK
deriving stock instance Traversable Identity
deriving stock instance Traversable Wrap
deriving stock instance Traversable V1
#else
deriving instance Traversable Identity
deriving instance Traversable Wrap
deriving instance Traversable V1
#endif

#ifdef BRIDGE_BAD_FIELD
data Bad a = MkBad (a -> a)
deriving instance Traversable Bad
#endif

#ifdef BRIDGE_MISSING_SUPERCLASS
data Bare a = MkBare a
deriving instance Traversable Bare
#endif

useIdentity :: (a -> Maybe b) -> Identity a -> Maybe (Identity b)
useIdentity = traverse
useWrap :: (a -> Maybe b) -> Wrap a -> Maybe (Wrap b)
useWrap = traverse
