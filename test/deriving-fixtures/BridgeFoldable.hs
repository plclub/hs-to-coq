{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, DeriveFoldable, ScopedTypeVariables #-}
module GHC.Internal.Data.Foldable where

import GHC.Internal.Base hiding (foldr)
import GHC.Internal.Num (Num(..))
import GHC.Internal.Err (errorWithoutStackTrace)
import GHC.Internal.Data.Monoid (Endo(..), Dual(..))
import GHC.Internal.Data.Ord (Down(..))
import GHC.Tuple (Solo(..))

-- The installed class's API, with ordinary Haskell defaults. Partial methods
-- have the same intentional method skips as production base translation.
class Foldable t where
  {-# MINIMAL foldMap | foldr #-}
  fold :: Monoid m => t m -> m
  fold = foldMap id
  foldMap :: Monoid m => (a -> m) -> t a -> m
  foldMap f = foldr (mappend . f) mempty
  foldMap' :: Monoid m => (a -> m) -> t a -> m
  foldMap' f = foldl' (\acc a -> acc <> f a) mempty
  foldr :: (a -> b -> b) -> b -> t a -> b
  foldr f z t = appEndo (foldMap (Endo . f) t) z
  foldr' :: (a -> b -> b) -> b -> t a -> b
  foldr' f z0 xs = foldl (\k x z -> z `seq` k (f x z)) id xs z0
  foldl :: (b -> a -> b) -> b -> t a -> b
  foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z
  foldl' :: (b -> a -> b) -> b -> t a -> b
  foldl' f z0 xs = foldr (\x k z -> z `seq` k (f z x)) id xs z0
  foldr1 :: (a -> a -> a) -> t a -> a
  foldr1 _ _ = errorWithoutStackTrace "partial method skipped by production edits"
  foldl1 :: (a -> a -> a) -> t a -> a
  foldl1 _ _ = errorWithoutStackTrace "partial method skipped by production edits"
  toList :: t a -> [a]
  toList = foldr (:) []
  null :: t a -> Bool
  null = foldr (\_ _ -> False) True
  length :: t a -> Int
  length = foldl' (\n _ -> n + 1) 0
  elem :: Eq a => a -> t a -> Bool
  elem x = foldr (\y found -> x == y || found) False
  maximum :: forall a. Ord a => t a -> a
  maximum _ = errorWithoutStackTrace "partial method skipped by production edits"
  minimum :: forall a. Ord a => t a -> a
  minimum _ = errorWithoutStackTrace "partial method skipped by production edits"
  sum :: Num a => t a -> a
  sum = foldl' (+) 0
  product :: Num a => t a -> a
  product = foldl' (*) 1

data Wrap a = MkWrap (Down a)

deriving instance Foldable Down
deriving instance Foldable Solo
deriving instance Foldable Wrap

useDown :: (a -> b -> b) -> b -> Down a -> b
useDown = foldr
useWrap :: (a -> b -> b) -> b -> Wrap a -> b
useWrap = foldr
useSolo :: (a -> b -> b) -> b -> Solo a -> b
useSolo = foldr
