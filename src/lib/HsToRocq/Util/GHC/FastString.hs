{-# LANGUAGE CPP #-}
module HsToRocq.Util.GHC.FastString (module FastString, fsToText) where

#if __GLASGOW_HASKELL__ >= 900
import GHC.Data.FastString as FastString
#else
import FastString
#endif
import Data.Text (Text)
import qualified Data.Text as T

fsToText :: FastString -> Text
fsToText = T.pack . unpackFS

