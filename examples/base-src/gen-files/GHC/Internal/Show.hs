{-# LANGUAGE NoImplicitPrelude #-}
module GHC.Internal.Show where

import GHC.Types (Char)

class Show a where
  showsPrec :: a -> [Char] -> [Char]
  show :: a -> [Char]
  showList :: [a] -> [Char] -> [Char]

type ShowS = [Char] -> [Char]

showParen :: Bool -> ShowS -> ShowS
showParen = showParen

showString :: [Char] -> ShowS
showString = showString
