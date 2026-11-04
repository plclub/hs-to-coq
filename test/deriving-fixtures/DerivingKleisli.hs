{-# LANGUAGE NoImplicitPrelude, DeriveFunctor, StandaloneDeriving #-}
module DerivingKleisli where

import GHC.Internal.Base (Functor(..))

newtype Kleisli m a b = MkKleisli { runKleisli :: a -> m b }

deriving instance Functor m => Functor (Kleisli m a)

useMap :: Functor m => (a -> b) -> Kleisli m r a -> Kleisli m r b
useMap = fmap
