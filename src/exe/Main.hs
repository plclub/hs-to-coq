module Main (main) where

import GHC.IO.Encoding (setLocaleEncoding, utf8)
import HsToCoq.Util.GHC
import HsToCoq.CLI

main :: IO ()
main = do
  -- Ensures Unicode edits/midambles work regardless of system locale
  -- (CI containers often have LANG=C)
  setLocaleEncoding utf8
  defaultRunGhc $ processFilesMain convertAndPrintModules
