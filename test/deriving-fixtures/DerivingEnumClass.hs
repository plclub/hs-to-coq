{-# LANGUAGE NoImplicitPrelude #-}
module DerivingEnumClass where

import Prelude (Int)

-- Bootstrap class metadata only; the compiled base supplies the real class.
class Enum a where
  enumFrom :: a -> [a]
  enumFromTo :: a -> a -> [a]
  enumFromTo _ _ = []
  fromEnum :: a -> Int
  pred :: a -> a
  succ :: a -> a
  toEnum :: Int -> a
