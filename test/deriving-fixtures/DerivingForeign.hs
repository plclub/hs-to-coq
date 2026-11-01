{-# LANGUAGE DeriveFoldable, DeriveFunctor #-}
module DerivingForeign where

data Foreign a = MkForeign { unForeign :: a }
  deriving (Functor, Foldable)
