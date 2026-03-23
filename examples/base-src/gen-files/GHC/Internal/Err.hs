{-# LANGUAGE NoImplicitPrelude #-}
module GHC.Internal.Err where

import GHC.Types (Char)

error :: [Char] -> a
error = error

errorWithoutStackTrace :: [Char] -> a
errorWithoutStackTrace = errorWithoutStackTrace

undefined :: a
undefined = undefined
