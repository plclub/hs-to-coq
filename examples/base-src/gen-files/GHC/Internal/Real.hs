{-# LANGUAGE NoImplicitPrelude, RoleAnnotations #-}
module GHC.Internal.Real (Integral (..), Real (..), Fractional, RealFrac, Ratio, Rational) where

import GHC.Classes (Ord)
import GHC.Num.Integer (Integer)

import {-# SOURCE #-} GHC.Internal.Num (Num)
import {-# SOURCE #-} GHC.Internal.Enum (Enum)

type role Ratio phantom
data Ratio a
type Rational = Ratio Integer

class Fractional a
class (Fractional a, Real a) => RealFrac a

class (Num a, Ord a) => Real a where
    toRational          :: a -> Rational

class (Real a, Enum a) => Integral a where
    quot                :: a -> a -> a
    rem                 :: a -> a -> a
    div                 :: a -> a -> a
    mod                 :: a -> a -> a
    quotRem             :: a -> a -> (a,a)
    divMod              :: a -> a -> (a,a)
    toInteger           :: a -> Integer
