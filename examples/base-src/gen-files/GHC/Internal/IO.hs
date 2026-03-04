{-# LANGUAGE NoImplicitPrelude #-}
module GHC.Internal.IO where

import GHC.Types (IO, Char)

mkUserError :: [Char] -> a
mkUserError = mkUserError

mplusIO :: IO a -> IO a -> IO a
mplusIO = mplusIO
