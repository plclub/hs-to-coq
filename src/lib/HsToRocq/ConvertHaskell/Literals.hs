{-# LANGUAGE CPP, OverloadedStrings #-}

module HsToRocq.ConvertHaskell.Literals (
  convertInteger, convertFastString, convertFractional
  ) where

import Prelude hiding (Num)
import Control.Monad.IO.Class
import HsToRocq.Util.GHC.FastString
import HsToRocq.Rocq.Gallina
import HsToRocq.Rocq.Gallina.Util

#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins ()
import GHC.Types.SourceText (FractionalLit(..))
#else
import BasicTypes
#endif
import Data.Ratio (numerator, denominator)

convertInteger :: String -> Integer -> Either String Num
convertInteger what int | int >= 0  = Right $ fromInteger int
                        | otherwise = Left  $ "negative " ++ what

convertFastString :: FastString -> Term
convertFastString = HsString . fsToText

convertFractional :: MonadIO f => FractionalLit -> f Term
convertFractional
  -- GHC 9.x added fl_exp and fl_signi fields to FractionalLit
#if __GLASGOW_HASKELL__ >= 900
  (FL _ _ fl_v _ _)
#else
  (FL _ _ fl_v)
#endif
  = do
   let fr = Var "fromRational"
   let qn = App2 (Var "Q.Qmake") (Num (fromInteger (numerator fl_v)))
                                 (Num (fromInteger (denominator fl_v)))
   pure $ App1 fr qn
