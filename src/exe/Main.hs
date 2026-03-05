module Main (main) where

import GHC.IO.Encoding (setLocaleEncoding, utf8)
import HsToCoq.Util.GHC
import HsToCoq.CLI

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultRunGhc $ processFilesMain convertAndPrintModules
