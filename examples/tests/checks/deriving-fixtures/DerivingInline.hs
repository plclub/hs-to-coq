{-# LANGUAGE DerivingStrategies, GeneralizedNewtypeDeriving #-}
module DerivingInline where

class Keep a where
  keep :: a -> a

instance Keep Bool where
  keep x = x

class Rejected a where
  rejected :: a -> a

newtype Wrapped = MkWrapped { unWrapped :: Bool }
  deriving newtype Keep
  deriving stock Rejected

useKept :: Wrapped -> Wrapped
useKept = keep
