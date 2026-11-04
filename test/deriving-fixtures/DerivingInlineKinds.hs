{-# LANGUAGE NoImplicitPrelude, PolyKinds, KindSignatures, GeneralizedNewtypeDeriving, DerivingStrategies, DeriveGeneric #-}
module DerivingInlineKinds where

import GHC.Internal.Base (Functor, Semigroup)
import Data.Kind (Type)
import GHC.Internal.Generics (Generic1)

newtype Phantom a (b :: k) = MkPhantom { getPhantom :: a }
  deriving newtype Semigroup

newtype Wrap (f :: Type -> Type) a = MkWrap { getWrap :: f a }
  deriving newtype Functor

-- Generic1 context inference specializes the intermediate kind to Type.
-- Production edits intentionally skip Generic1; checking requests must still
-- associate its generated body with the original polykinded declaration.
newtype Compose (f :: k1 -> Type) (g :: k2 -> k1) (a :: k2) = MkCompose (f (g a))
  deriving stock Generic1
