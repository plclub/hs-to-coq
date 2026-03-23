{-# LANGUAGE NoImplicitPrelude #-}
module GHC.Internal.IO where

import GHC.Types (IO, Char)

mkUserError :: [Char] -> a
mplusIO :: IO a -> IO a -> IO a
