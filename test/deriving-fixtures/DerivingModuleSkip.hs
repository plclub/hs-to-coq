{-# LANGUAGE DerivingStrategies, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module DerivingModuleSkip where

import DerivingIgnored (Ignored)

class Keep a where
  keep :: a -> a

instance Keep Bool where
  keep x = x

newtype Wrapped = MkWrapped { unWrapped :: Bool }
deriving newtype instance Keep Wrapped

class Rejected a where
  rejected :: a -> a

deriving stock instance Rejected Ignored

useKept :: Wrapped -> Wrapped
useKept = keep
