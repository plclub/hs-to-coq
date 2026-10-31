{-# LANGUAGE DeriveTraversable, DerivingStrategies, StandaloneDeriving #-}
module DerivingStock where

import Data.Traversable (Traversable(..))
import DerivingForeign (Foreign(..))

deriving stock instance Traversable Foreign

class Rejected a where
  rejected :: a -> a

deriving stock instance Rejected (Foreign Bool)

useTraverse :: Applicative f => (a -> f b) -> Foreign a -> f (Foreign b)
useTraverse = traverse
