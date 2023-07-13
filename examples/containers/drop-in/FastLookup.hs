{-# LANGUAGE BangPatterns #-}

module FastLookup where

import Data.IntMap.Internal
import Prelude hiding (lookup)

fastLookup :: Key -> IntMap a -> Maybe a
fastLookup !k = go
  where
    go (Bin _p m l r) | zero k m  = go l
                      | otherwise = go r
    go (Tip kx x) | k == kx   = Just x
                  | otherwise = Nothing
    go Nil = Nothing

