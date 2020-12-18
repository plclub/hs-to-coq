{-# LANGUAGE PolyKinds, RankNTypes #-}

module PolyKindClass where

class Foo bar where
    id :: bar a a -> bar a a

data Baz (a :: *) (b :: *) = MkBaz a b

instance Foo Baz where
    id a = a
