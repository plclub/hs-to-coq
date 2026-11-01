{-# LANGUAGE DerivingStrategies, GeneralizedNewtypeDeriving #-}
module DerivingInlineFailure where

class Keep a where
  keep :: a -> a

instance Keep Bool where
  keep x = x

newtype Wrapped = MkWrapped { unWrapped :: Bool }
  deriving newtype Keep

class Missing a where
  missing :: a -> a

newtype Failed = MkFailed Bool
  deriving newtype Missing

useKept :: Wrapped -> Wrapped
useKept = keep
