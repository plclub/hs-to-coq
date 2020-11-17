{-# LANGUAGE MultiParamTypeClasses #-}

module ClassKinds where

class Foo f a where
  bar :: f a -> f a
