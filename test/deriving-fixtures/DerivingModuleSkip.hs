{-# LANGUAGE DerivingStrategies, FlexibleContexts, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
module DerivingModuleSkip where

import DerivingIgnored (Ignored, IgnoredContext)

class Keep a where
  keep :: a -> a

instance Keep Bool where
  keep x = x

newtype Wrapped = MkWrapped { unWrapped :: Bool }
deriving newtype instance Keep Wrapped

class Rejected a where
  rejected :: a -> a

deriving stock instance Rejected Ignored

-- Only the context mentions the skipped module; GHC's error head does not.
deriving stock instance IgnoredContext Bool => Rejected Wrapped

useKept :: Wrapped -> Wrapped
useKept = keep
