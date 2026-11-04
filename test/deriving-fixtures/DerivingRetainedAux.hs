{-# LANGUAGE CPP, StandaloneDeriving #-}
module DerivingRetainedAux where

import EnumAuxRuntime (E(..))
#ifdef DERIVING_SOURCE_DEPENDENCY
import DerivingEnumClass ()
#endif

deriving instance Enum E
