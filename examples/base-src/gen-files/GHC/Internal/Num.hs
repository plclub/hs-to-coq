{-# LANGUAGE NoImplicitPrelude #-}
module GHC.Internal.Num (Num (..)) where

import GHC.Num.Integer (Integer)

infixl 7  *
infixl 6  +, -

class Num a where
    (+), (-), (*)       :: a -> a -> a
    negate              :: a -> a
    abs                 :: a -> a
    signum              :: a -> a
    fromInteger         :: Integer -> a
