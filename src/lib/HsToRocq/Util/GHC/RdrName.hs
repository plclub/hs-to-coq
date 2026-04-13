{-# LANGUAGE CPP #-}
module HsToRocq.Util.GHC.RdrName (module RdrName, isRdrOperator) where

#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins
import GHC.Types.Name.Reader as RdrName
#else
import OccName
import RdrName
#endif

isRdrOperator :: RdrName -> Bool
isRdrOperator = isSymOcc . rdrNameOcc
{-# INLINABLE isRdrOperator #-}
