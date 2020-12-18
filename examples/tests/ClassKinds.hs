{-# LANGUAGE MultiParamTypeClasses #-}

module ClassKinds where

class Foo f a where
  bar :: f a -> f a

class Category cat where
    id :: cat a a
    (.) :: cat b c -> cat a b -> cat a c
