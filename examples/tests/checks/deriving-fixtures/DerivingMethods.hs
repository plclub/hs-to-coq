{-# LANGUAGE DerivingStrategies, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module DerivingMethods where

class Keep a where
  keep :: a -> a
  ignored :: a -> a
  ignored _ = error "the skipped default must not be converted"

instance Keep Bool where
  keep x = x
  ignored _ = error "the skipped explicit method must not be converted"

newtype Inline = MkInline { unInline :: Bool }
  deriving newtype Keep

newtype Standalone = MkStandalone { unStandalone :: Bool }
deriving newtype instance Keep Standalone

useInline :: Inline -> Inline
useInline = keep

useStandalone :: Standalone -> Standalone
useStandalone = keep

-- This derivation depends on another accepted derivation in this module.
newtype Nested = MkNested { unNested :: Standalone }
deriving newtype instance Keep Nested

useNested :: Nested -> Nested
useNested = keep
