{-# LANGUAGE DerivingStrategies, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module DerivingRecovery where

class Keep a where
  keep :: a -> a

instance Keep Bool where
  keep x = x

newtype Wrapped = MkWrapped { unWrapped :: Bool }

deriving newtype instance Keep Wrapped

class Rejected a where
  rejected :: a -> a

deriving stock instance Rejected Wrapped

-- Typechecking this definition needs the retained derived dictionary.
useKept :: Wrapped -> Wrapped
useKept = keep
