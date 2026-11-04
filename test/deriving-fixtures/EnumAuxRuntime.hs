{-# LANGUAGE MagicHash, NoImplicitPrelude #-}
module EnumAuxRuntime where

import GHC.Exts (Int#, (==#), isTrue#)

-- A small source-generated model of the primitives used by stock Enum helpers.
data Boxed = BoxInt Int#
data E = A | B

tagToE :: Int# -> E
tagToE n = if isTrue# (n ==# 0#) then A else B

dataToTagE :: E -> Int#
dataToTagE A = 0#
dataToTagE B = 1#

range :: Boxed -> Boxed -> [Boxed]
range start finish = [start, finish]

mapList :: (a -> b) -> [a] -> [b]
mapList _ [] = []
mapList f (x:xs) = f x : mapList f xs
