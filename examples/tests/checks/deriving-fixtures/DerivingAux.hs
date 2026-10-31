{-# LANGUAGE DerivingStrategies, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module DerivingAux where

class Keep a where
  keep :: a -> a

instance Keep Bool where
  keep x = x

newtype Wrapped = MkWrapped { unWrapped :: Bool }
deriving newtype instance Keep Wrapped

-- Enum generates tag2con and maxtag helper bindings. Skipping the instance
-- must also discard its helpers, which use untranslatable GHC primitives.
data UnwantedEnum = EnumFirst | EnumLast deriving Enum

useKept :: Wrapped -> Wrapped
useKept = keep
