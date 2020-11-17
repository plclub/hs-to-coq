{-# LANGUAGE PolyKinds, RankNTypes #-}

module PolyKind where

-- T :: (k -> *) -> k -> *
newtype T m a = MkT (m a)

-- F :: (* -> *) -> *
newtype F f = MkF (f A)

-- G :: * -> *
newtype G a = MkG a

-- A :: *
data A = MkA

t :: T F G
t = MkT (MkF (MkG MkA))

class Foo a where
  bar :: a -> A
  
class Foo' a where
  bar' :: a -> A

instance Foo (T m a) where
  bar _ = MkA

instance forall k (m :: k -> *) a. Foo' (T m a) where
  bar' _ = MkA
