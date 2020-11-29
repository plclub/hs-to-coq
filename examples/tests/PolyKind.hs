{-# LANGUAGE PolyKinds                  #-}

module PolyKind where

-- T :: (k -> *) -> k -> *
data T m a = MkT (m a)

-- F :: (* -> *) -> *
data F f = MkF (f A)

-- G :: * -> *
data G a = MkG a

-- A :: *
data A = MkA

t :: T F G
t = MkT (MkF (MkG MkA))
